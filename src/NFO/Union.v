From Coq.Program Require Import Basics Combinators.

Add LoadPath "src".
From Internal Require Import Aux FunExt.
From NFO Require Import Xor BoolExpr Model Eeq Iin Morphs Sets Ext.

(* TODO: Union *)

Definition aux {X Y Z: Type} (A2: X -> set) (Q1: Y -> set) (p1: boolean) (Q2: Z -> set) (p2: boolean) a := 
(Qin a Q2 p2 -> Qin a Q1 p1)
/\ (Qin a Q1 p1 -> (Ain a A2 <-> Qin a Q2 p2))
.
(* (a -> b) /\ (b -> (c <-> a)) *)
(* (a && b && c) || (! a && ! b) || (! a && ! c) *)

Definition cup B C := 
  match B, C with S A p h X f, S A' p' h' X' f' =>
  let p'' := Or (map inl p) (map inr p') in
  S _ p'' (h <+> h') _
    ((select f (compose (aux f' h p h' p') f)) <+> (select f' (compose (aux f h' p' h p) f')))
end.


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
  unfold aux.
  Require Import Coq.Logic.Classical_Prop.
  destruct (classic (exists x : X, f x == z)); destruct (classic ((exists x : X0, f0 x == z))); split; unfold Xor; intros; tauto.

  unfold respects. intros. unfold aux.
  setoid_rewrite (eeq_Qin H).
  setoid_rewrite (eeq_Ain H).
  apply iff_refl.
  unfold respects. intros. unfold aux.
  setoid_rewrite (eeq_Qin H).
  setoid_rewrite (eeq_Ain H).
  apply iff_refl.
Qed.
