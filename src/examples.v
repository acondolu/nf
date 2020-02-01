Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require cumulative.
Import cumulative.Cumulative.

(* Examples *)


Definition Universe : U := fun n => match n with
  | O => tt
  | S m => fun _ => True
end.

Lemma univ_self : self Universe.
Proof.
  unfold self. intros. induction n.
  - unfold ll. unfold Universe. auto.
  - simpl Universe. simpl ll. intros. split; auto.
Qed.

Definition Empty : U := fun n => match n with
  | O => tt
  | S m => fun _ => False
end.

Lemma empty_self : self Empty.
Proof.
  unfold self. intros. induction n.
  - unfold ll. auto.
  - simpl Empty. simpl ll. intros. split; auto.
Qed.

Definition Conj : U -> U -> U := fun x y n =>
  match n with
  | O => tt
  | S m => fun z => x (S m) z /\ y (S m) z
end.

Theorem conj_self : forall x y, self x -> self y -> self (Conj x y).
Proof.
  unfold self. intros. destruct n.
  - simpl Conj. simpl ll. auto.
  - simpl Conj. simpl ll. intros.
    destruct (H (S n) z z' H1). destruct (H0 (S n) z z' H1).
    split; intros; split; auto; destruct H6.
    apply H2; auto.
    apply H4; auto.
    apply H3; auto.
    apply H5; auto.
Qed.

Definition Neg : U -> U := fun x n =>
  match n with
  | O => tt
  | S m => fun z => x (S m) z -> False
end.

Theorem neg_self : forall x, self x -> self (Neg x).
Proof.
  unfold self. intros. destruct n.
  - simpl Neg. simpl ll. auto.
  - simpl Neg. simpl ll. intros.
    destruct (H (S n) z z' H0). split; intros.
    -- apply H3. apply H2. auto.
    -- apply H3. apply H1. auto.
Qed. 

Definition Pow: U -> U := fun x n =>
  match n return u n with
  | O => tt
  | S O => fun _ => True
  | S (S m) => fun z: u (S m) => forall z' : u m, z z' -> x (S m) z'
end.

Theorem pow_univ: Pow Universe = Universe.
Proof.
  unfold Pow. unfold Universe.
  extensionality n. destruct n; auto.
  destruct n; auto.
  extensionality z. apply propositional_extensionality.
  split; auto.
Qed.

Theorem pow_corr: forall x y, iin y (Pow x) <-> forall z, iin z y -> iin z x.
Proof.
  intros. split.
  - intros. unfold iin in *. intros. destruct n.
    -- apply (H (S O) (z O)). apply H0.
    -- apply (H (S (S n))). apply H0.
  - intros. unfold iin.  intros. destruct n.
    -- simpl Pow. destruct (y 0). simpl iin in *. auto.
    -- simpl Pow. intros. unfold iin in *.
  (* use raise *)
Admitted.