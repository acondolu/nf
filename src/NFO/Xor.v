Require Import Coq.Logic.Classical_Prop.

Definition Xor a b := (a \/ b) /\ (a -> b -> False).

Lemma negb_xor_r : forall a b,
  (~ Xor a (~ b)) -> Xor a b.
Proof.
  unfold Xor. intros. 
  destruct (classic a); destruct (classic b); tauto.
Qed.

Lemma Xor_eq {a a' b b'}: (a <-> a') -> (b <-> b') -> Xor a b <-> Xor a' b'.
Proof. unfold Xor. tauto. Qed.

Lemma And_eq3 {a a' b b' c c'}: (a <-> a') -> (b <-> b') -> (c <-> c') -> (a /\ b /\ c) <-> (a' /\ b' /\ c').
Proof. tauto. Qed.