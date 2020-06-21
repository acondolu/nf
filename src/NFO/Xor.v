(* Warning! This module uses classical logic! *)
Require Import Coq.Logic.Classical_Prop.

Definition Xor a b := (a /\ ~b) \/ (~a /\ b).

Lemma xor_assoc {a b c}: Xor a (Xor b c) -> Xor (Xor a b) c.
Proof. unfold Xor. tauto. Qed.

Lemma xor_assoc2 {a b c}: Xor a (Xor b c) <-> Xor (Xor a b) c.
Proof. unfold Xor. tauto. Qed.

Lemma xor_absorb {a}: Xor a a <-> False.
Proof. unfold Xor. tauto. Qed.

Lemma xor_comm {a b}: Xor a b -> Xor b a.
Proof. unfold Xor. tauto. Qed.

Lemma xor_comm2 {a b}: Xor a b <-> Xor b a.
Proof. unfold Xor. tauto. Qed.

Lemma xor_pairs {a b c d}: Xor (Xor a b) (Xor c d) <-> Xor (Xor a c) (Xor b d).
Proof. unfold Xor. split; intro; destruct H; tauto. Qed.

Lemma Xor_eq {a a' b b'}: (a <-> a') -> (b <-> b') -> Xor a b <-> Xor a' b'.
Proof. unfold Xor. tauto. Qed.

Lemma Xor_ext {a a' b b'}: (a <-> a') -> (b <-> b') -> Xor a b -> Xor a' b'.
Proof. unfold Xor. tauto. Qed.

Lemma Xor_iff {a b}: (Xor a b <-> False) <-> (a <-> b).
Proof. unfold Xor. split; tauto. Qed.

Lemma Xor_neg {a b}: (~Xor a b) <-> (a <-> b).
Proof. unfold Xor. split; tauto. Qed.

Lemma Xor_1 {a b: Prop}: a -> (~b) -> Xor a b.
Proof. unfold Xor. tauto. Qed.

Lemma Xor_2 {a b: Prop}: (~a) -> b -> Xor a b.
Proof. unfold Xor. tauto. Qed.

Lemma negb_xor_r : forall a b,
  (~ Xor a (~ b)) -> Xor a b.
Proof.
  unfold Xor. intros. 
  destruct (classic a); destruct (classic b); tauto.
Qed.

Lemma negb_xor : forall a b,
  (Xor a (~ b)) <-> ~Xor a b.
Proof.
  unfold Xor. intros. 
  destruct (classic a); destruct (classic b); tauto.
Qed.

Lemma And_eq3 {a a' b b' c c'}: (a <-> a') -> (b <-> b') -> (c <-> c') -> (a /\ b /\ c) <-> (a' /\ b' /\ c').
Proof. tauto. Qed.