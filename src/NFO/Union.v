(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Add LoadPath "src".
From Internal Require Import Aux FunExt.
From NFO Require Import Xor BoolExpr Model Eeq Iin Morphs Sets Ext.
(* end hide *)

(** Union of NFO sets *)

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
  match B, C with S A p h X f, S A' p' h' X' f' =>
  S _ (Or (map inl p) (map inr p')) (h ⨁ h')
    _ (select f (aux f' h p h' p' ∘ f) ⨁ select f' (aux f h' p' h p ∘ f'))
end.

Lemma aaa: forall {X Y R} P z (f: X -> Y),
  respects R P ->
(exists xp : {x: X & P (f x) : Prop}, R (f (projT1 xp)) z) <-> P z /\ exists x, R (f x) z.
Proof.
  intros. setoid_rewrite (ex_T (fun X => P (f X)) (fun X => R (f X) z)).
  split; intro H0; destruct H0. destruct H0; split; eauto. apply (H _ _ H1). auto.
  firstorder.
Qed.

Lemma cup_ok x y z: iin z (cup x y) <-> iin z x \/ iin z y.
Proof.
  destruct x, y. unfold cup. rewrite iin_unfold'.
  rewrite Ain_sums. simpl Qin.
  setoid_rewrite Qin_sum_inl. setoid_rewrite Qin_sum_inr.
  setoid_rewrite iin_unfold'.
  unfold Ain, select.
  unfold compose.
  setoid_rewrite (aaa (aux f0 h p h0 p0) z f).
  setoid_rewrite (aaa (aux f h0 p0 h p) z f0).
  - unfold aux.
      classic (exists x, f x == z);
        classic (exists x, f0 x == z);
          classic (Qin z h p);
            classic (Qin z h0 p0);
              clear; unfold Xor; tauto.
  - unfold respects. intros. unfold aux.
    setoid_rewrite (eeq_Qin H).
    setoid_rewrite (eeq_Ain H).
    apply iff_refl.
  - unfold respects. intros. unfold aux.
    setoid_rewrite (eeq_Qin H).
    setoid_rewrite (eeq_Ain H).
    apply iff_refl.
Qed.
