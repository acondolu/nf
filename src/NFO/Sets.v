Add LoadPath "src/NFO/".
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Iin.


Definition emptyset :=
  S False (Bot _) (False_rect _) False (False_rect _).

Lemma emptyset_ok: forall x, ~ iin x emptyset.
Proof.
  red. unfold emptyset. intro x. rewrite iin_unfold. unfold iin_low. unfold XOR. simpl. destruct 1. repeat destruct H. destruct x0.
Qed.


Definition compl x := match x with
  S A p h X f => S A (Not _ p) h X f
end.

Lemma compl_ok_1: forall x y, iin x y -> iin x (compl y) -> False.
Proof.
  unfold compl. intros x y.
  destruct y. repeat rewrite iin_unfold.
  intros. unfold XOR in *. simpl boolean_map in *. simpl eval in *. tauto.
Qed.

Require Import Coq.Logic.Classical_Prop.
Lemma negb_xor_r : forall a b,
  (XOR a (~b) -> False) -> XOR a b.
Proof.
  unfold XOR. intros. 
  destruct (classic a); destruct (classic b); tauto.
Qed.
Lemma compl_ok_2: forall x y,
  (iin x (compl y) -> False) -> iin x y.
Proof.
  intros x y. repeat rewrite iin_unfold. destruct y. unfold compl. simpl boolean_map. simpl eval. intros.
  apply negb_xor_r. auto.
Qed.
Lemma compl_ok: forall x y,
  iin x y <-> (iin x (compl y) -> False).
Proof.
  intros. split.
  apply compl_ok_1. apply compl_ok_2.
Qed.

Definition cosin x := S unit (Atom _ tt) (fun _ => x) False (False_rect _).

Lemma cosin_ok: forall x y, iin x (cosin y) <-> iin y x.
Proof.
  intros x y.
  unfold cosin. rewrite iin_unfold.
  unfold XOR, iin_low. simpl. split; intros.
  - repeat destruct H. destruct x0. assumption.
  - split. right; auto. intros. destruct H0. destruct x0.
Qed.

Definition sin x := S False (Bot _) (False_rect _) unit (fun _ => x).

Lemma sin_ok: forall x y, iin x (sin y) <-> eeq x y.
Proof.
  intros x y.
  unfold sin. rewrite iin_unfold.
  unfold XOR, iin_low. simpl. split; intros.
  - repeat destruct H. apply eeq_sym. auto.
  - split. left. exists tt. apply eeq_sym. auto.
    intros. destruct H1.
Qed.
