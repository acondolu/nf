Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Module Cumulative.

Definition Zero := unit.
Definition Two := Prop.

Fixpoint u n : Type := match n with
  | O => Zero
  | S m => u m -> Two
end.

Definition U : Type := forall n, u n.

Fixpoint ll {n} : u n -> u (S n) -> Prop := 
  match n with
  | O   => fun _ _ => True
  | S m => fun x y => forall z, x z <-> exists z', ll z z' /\ y z'
end.

Definition self : U -> Prop := fun x => 
  forall n, ll (x n) (x (S n)).

Definition iin: U -> U -> Prop := fun x y =>
  forall n, y (S n) (x n).

Theorem raise {n x y}:
  self x -> x (S n) y -> exists y', self y' /\ y' n = y /\ iin y' x.
Proof.
  fold u.
  intros. fold U.
Admitted.

Theorem u_ext: forall x y, self x -> self y -> 
  x = y <-> forall z, self z -> iin z x <-> iin z y.
Proof.
  intros x y cx cy.
  split.
  - intros eqxy z. split.
      * intro inzx. unfold iin in *.  rewrite<- eqxy. auto.
      * intro inzy. rewrite eqxy. auto.
  - intro ex. extensionality n. case n.
    * destruct (x 0). destruct (y 0). trivial.
    * intro m. extensionality z'. apply propositional_extensionality.
  split; intro.
      ** destruct (raise cx H). fold u in *. fold U in *.
          destruct H0. destruct H1. destruct (ex x0 H0).
          pose proof (H3 H2). unfold iin in H5.
          pose proof (H5 m). rewrite<- H1. assumption.
      ** destruct (raise cy H). fold u in *. fold U in *.
          destruct H0. destruct H1. destruct (ex x0 H0).
          pose proof (H4 H2). unfold iin in H5.
          pose proof (H5 m). rewrite<- H1. assumption.
Qed.

Lemma inj: forall {n x y z}, @ll n x z -> ll y z -> x = y.
Proof.
  destruct n; intros.
  - destruct x, y. auto.
  - extensionality z'. destruct (H z'). destruct (H0 z').
    apply propositional_extensionality; split; intros.
    -- apply H4. destruct (H1 H5). exists x0. auto.
    -- apply H2. destruct (H3 H5). exists x0. auto.
Qed.

Lemma trivial_raise: forall n,
  forall x, exists y, @ll n x y.
Proof.
  induction n.
  - intro. unfold ll, u. exists (fun _ => True). auto.
  - intros. simpl u. 
    exists (fun z' : u (S n) => exists z, ll z z' /\ x z).
    simpl ll. intros. split; intros. fold u in z. (* exists x. split. 
    destruct (inj H H1).
    auto. auto.*)
Admitted.

Lemma trivial_lower: forall {n}, forall x, exists y, @ll n y x.
Admitted.


End Cumulative.
