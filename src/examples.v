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

Definition Sing: U -> U := fun x n =>
  match n return u n with
  | O => tt
  | S m => fun z => z = x m
end.

Lemma Sing_self: forall x, self x -> self (Sing x).
Proof.
  intros. unfold self. destruct n.
  - simpl. trivial.
  - simpl. intros. split; intro. rewrite H1 in H0.
    pose proof (H n).


 destruct n.
  -- unfold self in H. destruct z. destruct (x O).
      destruct H0. split; auto; intro. extensionality zz.
      destruct zz. 
     admit.
  -- simpl. 

 pose proof (H O). simpl ll in H1.
      destruct z.
      destruct (x O). destruct z. unfold ll in H0.


 split; intros.
  -- unfold self in H. pose proof (H n). destruct n.
  ---  simpl ll in H2. simpl ll in H0.
  --- simpl ll in H0. unfold self in H. 

Lemma try: forall x, self x -> forall y, self y -> iin y (Sing x) <-> x = y.
Proof.
  intros.
  unfold iin, Sing. split. intro. extensionality n. auto.
  intro. destruct H1. auto.
Qed.

Definition Pow: U -> U := fun x n =>
  match n return u n with
  | O => tt
  | S O => fun _ => True
  | S (S m) => fun z: u (S m) => forall z' : u m, z z' -> x (S m) z'
end.

Theorem pow_self: forall x, self x -> self (Pow x).
Proof.
  intros. unfold self. intro n. destruct n; simpl ll; auto.
  intros. destruct n. simpl. split; auto. intros. destruct H1. destruct z'0.
  admit.
  split; intros. 
  destruct (trivial_lower z'0).
  apply (H (S (n)) x0 z'0). apply H3. apply H1.
  destruct n; simpl; auto. unfold ll in H0. unfold ll in H3. destruct x0.
Qed.

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