Add LoadPath "src/NFO/".
Require Import Xor Aux FunExt.
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Iin Morphs Sets.

(* TODO: Union *)


Lemma cup_A_ok {X X'} {f: X -> set} {f': X' -> set} {x}:
  Ain x (sum_funs f f') <-> (Ain x f) \/ (Ain x f').
Proof.
  unfold Ain, sum_funs. split; intro.
  - destruct H, x0. left; eauto. right; eauto.
  - destruct H, H. exists (inl x0). auto. exists (inr x0). auto.
Qed.

Definition aux {X Y Z: Type} (A2: X -> set) (Q1: Y -> set) (p1: boolean Y) (Q2: Z -> set) (p2: boolean Z) a := 
(Qin a Q2 p2 -> Qin a Q1 p1)
/\ (Qin a Q1 p1 -> (Ain a A2 <-> Qin a Q2 p2))
.
(* (a -> b) /\ (b -> (c <-> a)) *)
(* (a && b && c) || (! a && ! b) || (! a && ! c) *)
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Definition cup B C := 
  match B, C with S A p h X f, S A' p' h' X' f' =>
  let A'' := sum A A' in
  let h'' := sum_funs h h' in
  let p'' := Or _ (boolean_map inl p) (boolean_map inr p') in
  S A'' p'' h'' _ (sum_funs (select f (compose (aux f' h p h' p') f)) (select f' (compose (aux f h' p' h p) f')))
end.

Lemma aaa: forall {X} P z f,
  respects eeq P ->
(exists xp : {x: X & P (f x) : Prop}, (let (x, _) := xp in f x) == z) <-> P z /\ exists x, f x == z.
Proof.
  split; intro. destruct H0, x. split. apply (H (f x)). auto. eauto.
  eauto.
  destruct H0, H1. cut (P (f x)). intro. exists (existT _ x H2). auto. apply (H z). symmetry. assumption. assumption.
Qed.


Lemma cup_ok x y z: iin z (cup x y) <-> iin z x \/ iin z y.
Proof.
  destruct x, y. unfold cup. rewrite iin_unfold'.
  rewrite cup_A_ok. simpl Qin.
  setoid_rewrite aux1. setoid_rewrite aux2.
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
