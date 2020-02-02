Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require cumulative.
Import cumulative.Cumulative.

(* Examples *)


Definition univ : U := fun n => match n with
  | O => tt
  | S m => fun _ => True
end.

Lemma univ_self : self univ.
Proof.
  unfold self. intros. induction n.
  - unfold ll. unfold univ. auto.
  - simpl univ. simpl ll. intros. split; auto.
Qed.

Lemma univ_correct : forall x, self x -> iin x univ.
Proof.
  intros.
  intro n. unfold univ. auto.
Qed.

Definition empty : U := fun n => match n with
  | O => tt
  | S m => fun _ => False
end.

Lemma empty_correct : forall x, self x -> iin x empty -> False.
Proof.
  intros.
  unfold empty in H0. unfold iin in H0. apply H0. exact 666.
Qed.


Lemma empty_self : self empty.
Proof.
  unfold self. intros. induction n.
  - unfold ll. auto.
  - simpl empty. simpl ll. intros. split; auto.
  -- intro f. destruct f.
  -- intro. destruct H. destruct H. auto.
Qed.

Definition Conj : U -> U -> U := fun x y n =>
  match n with
  | O => tt
  | S m => fun z => (*x (S m) z /\ y (S m) z*)
      exists z', self z' /\ iin z' x /\ iin z' y /\ z' m = z
end.

Theorem conj_self : forall x y, self x -> self y -> self (Conj x y).
Proof.
  unfold self. intros.
  destruct n; simpl Conj; simpl ll; auto; intros.
  split; intros. destruct H1 as [z' [sz' [z'x [z'y z'z]]]]. fold u in *.
  - exists (z' (S n)). split. rewrite<- z'z. apply sz'.
    exists z'. auto.
  - destruct H1 as [z' [zz' [z'0 [s0 [iox [ioy ss]]]]]].
    exists z'0. repeat (split; auto). pose proof (s0 n). rewrite ss in *.
    apply (inj H1 zz').
Qed. 

Lemma conj_correct: forall x, self x -> forall y, self y ->
  forall z, self z -> iin z (Conj x y) <-> iin z x /\ iin z y.
Proof.
  intros. split; intros. 
  - unfold Conj in H2. unfold iin in H2. split.
    unfold iin. intros. destruct (H2 n). destruct H3. destruct H4.
    destruct H5. rewrite<- H6. apply H4.
    unfold iin. intros. destruct (H2 n). destruct H3. destruct H4.
    destruct H5. rewrite<- H6. apply H5.
  - intro n. unfold Conj. exists z. destruct H2. split; auto.
Qed.

Definition Neg : U -> U := fun x n =>
  match n return u n with
  | O => tt
  | S m => fun z => forall z', ll z z' -> x (S (S m)) z' -> False
end.


Lemma neg_correct : forall x, self x -> forall z, self z -> iin z (Neg x) <-> ~iin z x.
Proof.
  intros. split; intro.
  - intro. unfold iin in *. unfold Neg in H1.
    cut (forall n : nat,
     exists z' : U, self z' /\ ~ iin z' x /\ x (S n) (z' n)).
    intro. 

destruct (H1 O).
    destruct H3. destruct H4. apply H4. intro. induction n.
    -- pose proof (H2 O). destruct (z O). destruct H5. assumption.
    -- 
 intro n. pose proof (H2 n).
    destruct (H1 n). destruct H7. destruct H8. *)
  admit.
  - intro n. unfold Neg. exists z. auto.
Admitted.

Theorem neg_self : forall x, self x -> self (Neg x).
Proof.
  unfold self. intros. destruct n.
  - simpl Neg. simpl ll. auto.
  - simpl Neg. simpl ll. intros.
    destruct (H (S n) z). split; intros.
    -- destruct H2. exists (x0 (S n)). admit.
    -- destruct H2. destruct H2. (*apply H4. 
       pose proof (H0 H3). destruct H5. 


 z' H0). split; intros.
    -- apply H3. apply H2. auto.
    -- apply H3. apply H1. auto.*) admit.
Admitted. 


Definition Sing: U -> U := fun x n =>
  match n return u n with
  | O => tt
  | S m => fun z => z = x m
end.

Lemma Sing_self: forall x, self x -> self (Sing x).
Proof.
  intros. unfold self. destruct n.
  - simpl. trivial.
  - simpl. intros. split; intro.
  -- rewrite H0. exists (x (S n)). pose proof (H n). auto.
  -- destruct H0. destruct H0. rewrite H1 in H0. clear x0 H1.
     pose proof (H n). apply (inj H0 H1).
Qed.

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

Theorem pow_univ: Pow univ = univ.
Proof.
  unfold Pow. unfold univ.
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