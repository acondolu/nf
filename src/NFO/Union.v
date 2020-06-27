(** NFO.Union : Union of NFO sets *)

(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Add LoadPath "src".
From Internal Require Import Aux FunExt.
From NFO Require Import Xor BoolExpr Model Eeq Iin Morphs Sets Ext.
(* end hide *)

(** TODO: clean up and explain *)
Definition aux {X Y Z: Type} (A2: X -> set) (Q1: Y -> set) (p1: boolean) (Q2: Z -> set) (p2: boolean) a := 
(Qin a Q2 p2 -> Qin a Q1 p1)
/\ (Qin a Q1 p1 -> (Ain a A2 <-> Qin a Q2 p2))
.
(* (a -> b) /\ (b -> (c <-> a)) *)
(* (a && b && c) || (! a && ! b) || (! a && ! c) *)

(** The union of NFO sets is defined as follows:
    - The resulting A-part is a complex combination TODO: explain
    - The resulting B-part is the union of the input B-parts.
*)
Definition cup B C := 
  match B, C with S X Y f g e, S X' Y' f' g' e' =>
  S _ _
    (select f (aux f' g e g' e' ∘ f) ⨁ select f' (aux f g' e' g e ∘ f'))
      (g ⨁ g') (Or (map inl e) (map inr e'))
end.

Lemma cup_ok x y z: iin z (cup x y) <-> iin z x \/ iin z y.
Proof.
  destruct x, y. unfold cup. rewrite iin_unfold.
  rewrite Ain_sums. simpl Qin.
  setoid_rewrite Qin_sum_inl. setoid_rewrite Qin_sum_inr.
  setoid_rewrite iin_unfold.
  unfold Ain, select.
  unfold compose.
  setoid_rewrite (ex_T_resp (aux f0 g e g0 e0) z f).
  setoid_rewrite (ex_T_resp (aux f g0 e0 g e) z f0).
  - unfold aux.
      classic (exists x, f x == z);
        classic (exists x, f0 x == z);
          classic (Qin z g e);
            classic (Qin z g0 e0);
              clear; unfold xor; tauto.
  - unfold respects. intros. unfold aux.
    setoid_rewrite (eeq_Qin H).
    setoid_rewrite (eeq_Ain H).
    apply iff_refl.
  - unfold respects. intros. unfold aux.
    setoid_rewrite (eeq_Qin H).
    setoid_rewrite (eeq_Ain H).
    apply iff_refl.
Qed.
