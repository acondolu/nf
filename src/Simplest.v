Require Import Coq.Sets.Finite_sets.

(* see also https://github.com/coq-contribs/zfc *)
Inductive set :=
  | Pos : forall X, (X -> set) -> set
  | Neg : forall X, (X -> set) -> set
.

Fixpoint eeq a b := match a,b with
  | Pos _ _, Neg _ _ => False
  | Neg _ _, Pos _ _ => False
  | Pos X f, Pos Y g =>
      (forall x, exists y, eeq (f x) (g y))
      /\ (forall y, exists x, eeq (f x) (g y))
  | Neg X f, Neg Y g =>
    (forall x, exists y, eeq (f x) (g y))
    /\ (forall y, exists x, eeq (f x) (g y))
end.

Definition iin a b := match b with
  | Pos X f => exists x: X, eeq (f x) a
  | Neg X f => forall x: X, eeq (f x) a -> False
end.

Definition U := Neg False (fun x => match x with end).
Definition E := Pos False (fun x => match x with end).

Lemma u_in_u : iin U U.
Proof. intro H. destruct H. Qed.

Lemma e_empty : forall x, iin x E -> False.
Proof. intros x H. apply H. Qed.


Lemma eq_refl : forall x, eeq x x.
Proof.
  induction x; simpl eeq; split; intro x; exists x; apply H.
Qed.

Lemma eq_trans : forall x y z, eeq x y -> eeq y z -> eeq x z.
Proof.
  induction x; induction y; induction z; intros; simpl eeq.
  - simpl eeq in H2, H3. destruct H2, H3. split; intro.
    destruct (H2 x). destruct (H3 x0). exists x1. apply (H _ _ _ H6 H7).
    destruct (H5 y). destruct (H4 x). exists x0. apply (H _ _ _ H7 H6).
  - simpl eeq in H3. destruct H3.
  - simpl eeq in H3. destruct H3.
  - simpl eeq in H2. destruct H2.
  - simpl eeq in H2. destruct H2.
  - simpl eeq in H2. destruct H2.
  - simpl eeq in H3. destruct H3.
  - simpl eeq in H2, H3. destruct H2, H3. split; intro.
  destruct (H2 x). destruct (H3 x0). exists x1. apply (H _ _ _ H6 H7).
  destruct (H5 y). destruct (H4 x). exists x0. apply (H _ _ _ H7 H6).
Qed.

(* Lemma eq_sym : forall x y, eeq x y -> eeq y x.
Proof.
  intros x y. induction x; destruct y; intro. destruct H0; simpl eeq.
  - simpl eeq. split.
    -- intro x. destruct (H1 x). pose proof (H x0). destruct (s x0). *)
Conjecture eq_sym : forall x y, eeq x y -> eeq y x.

Lemma ext1: forall x y, eeq x y -> forall z, iin z x -> iin z y.
Proof.
destruct x; destruct y; simpl eeq; intros e z; simpl iin; simpl eeq; intros; destruct e.
destruct H. destruct (H0 x). exists x0. pose proof (eq_sym _ _ H2). apply (eq_trans _ _ _ H3 H).
  - destruct (H2 x). pose proof (eq_trans _ _ _ H3 H0). apply (H _ H4).
Qed.

 