(** * NFO.Union : Union of NFO sets *)

(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Add LoadPath "src/Internal" as Internal.
From Internal Require Import Misc FunExt.
Add LoadPath "src/NFO" as NFO.
From NFO Require Import Xor BoolExpr Model Eq In Morphism Sets.
(* end hide *)

(** The union of NFO sets is defined as follows:
    - The resulting B-part is simply the union of the input B-parts.
    - The resulting A-part is a more complex combination of the input A-parts and B-parts.
      TODO:
*)

(** TODO: clean up and explain *)
Definition half {X} (f: X -> SET) e e' s := 
  (BIN s e' -> BIN s e) /\ (BIN s e -> (AIN s f <-> BIN s e'))
.
(* (a -> b) /\ (b -> (c <-> a)) *)
(* (a && b && c) || (! a && ! b) || (! a && ! c) *)

(* 
a b
c d

(a AND b AND c AND d) OR (a AND NOT c AND NOT d) OR (NOT a AND NOT b AND c) OR (NOT b AND c AND NOT d)

*)

Local Lemma half_respects {X} (f: X -> SET) e e':
  respects EQ (half f e e').
Proof.
  unfold respects. intros. unfold half.
  setoid_rewrite (EQ_BIN H).
  setoid_rewrite (EQ_AIN H).
  apply iff_refl.
Qed.

(** 'restrictC f P' restricts the domain of a function f according to a predicate P that restricts the codomain: *)
Definition restrictC {X Y} (f: X -> Y) (P: Y -> Prop)
  : { x: X & P (f x) } -> Y
  := fun x => f (projT1 x).

Definition cup x y := 
  match x, y with S X Y f g e, S X' Y' f' g' e' =>
    S _ _
      (   restrictC f  (half f' (map g  e ) (map g' e'))
       ⨁ restrictC f' (half f  (map g' e') (map g  e )))
      (g ⨁ g')
      (Or (map inl e) (map inr e'))
  end.

Theorem cup_ok x y z: IN z (cup x y) <-> IN z x \/ IN z y.
Proof.
  destruct x, y. unfold cup. rewrite IN_unfold.
  rewrite AIN_sums. simpl BIN.
  setoid_rewrite map_compose.
  setoid_rewrite (@map_compose_inl _ _ _ g g0).
  setoid_rewrite (@map_compose_inr _ _ _ g g0).
  setoid_rewrite IN_unfold.
  unfold AIN, restrictC, compose.
  fold (AIN z f). fold (AIN z f0).
  setoid_rewrite (ex_T_resp (half f0 (map g e) (map g0 e0))).
  setoid_rewrite (ex_T_resp (half f (map g0 e0) (map g e))).
  - unfold half.
      classic (AIN z f);
        classic (AIN z f0);
          classic (BIN z (map g e));
            classic (BIN z (map g0 e0));
              clear; unfold xor; tauto.
  - apply half_respects.
  - apply half_respects.
Qed.
