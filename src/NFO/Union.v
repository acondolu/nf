(** * NFO.Union : Union of NFO sets *)

(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Add LoadPath "src".
From Internal Require Import Misc FunExt.
From NFO Require Import Xor BoolExpr Model Eq In Morphism Sets Ext.
(* end hide *)

(** The union of NFO sets is defined as follows:
    - The resulting B-part is simply the union of the input B-parts.
    - The resulting A-part is a more complex combination of the input A-parts and B-parts.
      TODO:
*)

(** TODO: clean up and explain *)
Definition aux {X Y Z: Type} (f': X -> SET) (g: Y -> SET) (g': Z -> SET) e e' z := 
  (BIN z (map g' e') -> BIN z (map g e)) /\ (BIN z (map g e) -> (AIN z f' <-> BIN z (map g' e')))
.
(* (a -> b) /\ (b -> (c <-> a)) *)
(* (a && b && c) || (! a && ! b) || (! a && ! c) *)

Local Lemma aux_respects {X Y Z: Type} (f': X -> SET) (g: Y -> SET) (g': Z -> SET) e e':
  respects EQ (aux f' g g' e e').
Proof.
  unfold respects. intros. unfold aux.
  setoid_rewrite (EQ_BIN H).
  setoid_rewrite (EQ_AIN H).
  apply iff_refl.
Qed.

Definition cup x y := 
  match x, y with S X Y f g e, S X' Y' f' g' e' =>
    S _ _
      (select f (aux f' g g' e e' ∘ f) ⨁ select f' (aux f g' g e' e ∘ f'))
        (g ⨁ g') (Or (map inl e) (map inr e'))
  end.

Theorem cup_ok x y z: IN z (cup x y) <-> IN z x \/ IN z y.
Proof.
  destruct x, y. unfold cup. rewrite IN_unfold.
  rewrite AIN_sums. simpl BIN.
  setoid_rewrite map_compose.
  setoid_rewrite (@map_compose_inl _ _ _ g g0).
  setoid_rewrite (@map_compose_inr _ _ _ g g0).
  setoid_rewrite IN_unfold.
  unfold AIN, select, compose.
  setoid_rewrite (ex_T_resp (aux f0 g g0 e e0)).
  setoid_rewrite (ex_T_resp (aux f g0 g e0 e)).
  - unfold aux.
      classic (exists x, f x == z);
        classic (exists x, f0 x == z);
          classic (BIN z (map g e));
            classic (BIN z (map g0 e0));
              clear; unfold xor; tauto.
  - apply aux_respects.
  - apply aux_respects.
Qed.
