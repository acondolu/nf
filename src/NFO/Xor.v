Require Import Coq.Logic.Classical_Prop.

Definition Xor a b := (a \/ b) /\ (a -> b -> False).

Lemma negb_xor_r : forall a b,
  (~ Xor a (~ b)) -> Xor a b.
Proof.
  unfold Xor. intros. 
  destruct (classic a); destruct (classic b); tauto.
Qed.