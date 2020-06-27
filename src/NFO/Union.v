(** * NFO.Union : Union of NFO sets *)

(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Add LoadPath "src".
From Internal Require Import Aux FunExt.
From NFO Require Import Xor BoolExpr Model Eeq Iin Morphs Sets Ext.
(* end hide *)

(** The union of NFO sets is defined as follows:
    - The resulting B-part is simply the union of the input B-parts.
    - The resulting A-part is a more complex combination of the input A-parts and B-parts.
      TODO:
*)

(** TODO: clean up and explain *)
Definition aux {X Y Z: Type} (f': X -> set) (g: Y -> set) (g': Z -> set) e e' z := 
  (Qin z g' e' -> Qin z g e) /\ (Qin z g e -> (Ain z f' <-> Qin z g' e'))
.
(* (a -> b) /\ (b -> (c <-> a)) *)
(* (a && b && c) || (! a && ! b) || (! a && ! c) *)

Local Lemma aux_respects {X Y Z: Type} (f': X -> set) (g: Y -> set) (g': Z -> set) e e':
  respects eeq (aux f' g g' e e').
Proof.
  unfold respects. intros. unfold aux.
  setoid_rewrite (eeq_Qin H).
  setoid_rewrite (eeq_Ain H).
  apply iff_refl.
Qed.

Definition cup x y := 
  match x, y with S X Y f g e, S X' Y' f' g' e' =>
    S _ _
      (select f (aux f' g g' e e' ∘ f) ⨁ select f' (aux f g' g e' e ∘ f'))
        (g ⨁ g') (Or (map inl e) (map inr e'))
  end.

Theorem cup_ok x y z: iin z (cup x y) <-> iin z x \/ iin z y.
Proof.
  destruct x, y. unfold cup. rewrite iin_unfold.
  rewrite Ain_sums. simpl Qin.
  setoid_rewrite Qin_sum_inl.
  setoid_rewrite Qin_sum_inr.
  setoid_rewrite iin_unfold.
  unfold Ain, select, compose.
  setoid_rewrite (ex_T_resp (aux f0 g g0 e e0)).
  setoid_rewrite (ex_T_resp (aux f g0 g e0 e)).
  - unfold aux.
      classic (exists x, f x == z);
        classic (exists x, f0 x == z);
          classic (Qin z g e);
            classic (Qin z g0 e0);
              clear; unfold xor; tauto.
  - apply aux_respects.
  - apply aux_respects.
Qed.
