Add LoadPath "src/NFO/".
Require Import Xor.
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Iin.
Require Import Ext.

(* Empty set *)
Definition emptyset :=
  S False (Bot _) (False_rect _) False (False_rect _).

Lemma emptyset_ok: forall x, ~ iin x emptyset.
Proof.
  red. unfold emptyset. intro x. rewrite iin_unfold. unfold Ain. unfold Xor. simpl. destruct 1. repeat destruct H. destruct x0.
Qed.

(* Set complement *)
Definition compl x := match x with
  S A p h X f => S A (Not _ p) h X f
end.

Lemma compl_ok: forall x y,
  iin x y <-> (iin x (compl y) -> False).
Proof.
  intro x. destruct y. unfold compl. repeat rewrite iin_unfold. simpl boolean_map. simpl eval. split; intros.
  - unfold Xor in *. tauto.
  - apply negb_xor_r. auto.
Qed.

(* Co-singleton *)
Definition cosin x := S unit (Atom _ tt) (fun _ => x) False (False_rect _).

Lemma cosin_ok: forall x y, iin x (cosin y) <-> iin y x.
Proof.
  intros x y. unfold cosin. rewrite iin_unfold.
  unfold Xor, Ain. simpl. split; intros.
  - repeat destruct H. destruct x0. assumption.
  - split. right; auto. intros. destruct H0. destruct x0.
Qed.

(* Singleton *)
Definition sin x := S False (Bot _) (False_rect _) unit (fun _ => x).

Lemma sin_ok: forall x y, iin x (sin y) <-> eeq x y.
Proof.
  intros x y. unfold sin. rewrite iin_unfold.
  unfold Xor, Ain. simpl. split; intros.
  - repeat destruct H. apply eeq_sym. auto.
  - split. left. exists tt. apply eeq_sym. auto.
    intros. destruct H1.
Qed.

(* Exclusive or of sets *)
(* Definition QXor {A p h X f A' p' h' X' f'} :=
  let A'' := sum A A' in
  let h'' := mk_sum h h' in
  let X'' := sum {x: X & forall x', ~ eeq (f' x') (f x)} {x': X' & forall x, ~ eeq (f x) (f' x')} in 
  (S A p h X f, S A' p' h' X' f'). *)


(* TODO: Union *)
