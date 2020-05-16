Require Import Coq.Sets.Finite_sets.

(* see also https://github.com/coq-contribs/zfc *)
Inductive set :=
  | Pos : forall X, (X -> set) -> set
  | Neg : forall X, (X -> set) -> set
.
Notation 𝓥 := set.

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
Notation "A ≡ B" := (eeq A B) (at level 85).

Definition iin a b := match b with
  | Pos X f => exists x: X, eeq (f x) a
  | Neg X f => forall x: X, eeq (f x) a -> False
end.
Notation "A ∈ B" := (iin A B) (at level 85).

(* Equality is an equivalence relation *)

Lemma eeq_refl : forall {x}, x ≡ x.
Proof. induction x; split; intro x; exists x; apply H. Qed.

Lemma eeq_trans : forall {x y z}, x ≡ y -> y ≡ z -> x ≡ z.
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

Lemma eeq_sym : forall {x y}, x ≡ y -> y ≡ x.
Proof.
  intro x. induction x; destruct y; simpl eeq; auto.
  - intro A. destruct A. split; intro a.
    -- destruct (H1 a). exists x. apply (H _ _ H2).
    -- destruct (H0 a). exists x. apply (H _ _ H2).
  - intro A. destruct A. split; intro a.
  -- destruct (H1 a). exists x. apply (H _ _ H2).
  -- destruct (H0 a). exists x. apply (H _ _ H2).
Qed.
