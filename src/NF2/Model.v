(**
  There are two kinds of sets:
  - Sets with positive extension ("low"), which correspond to the
    usual understanding of sets as collections of 
    given sets.
  - Sets with negative extension ("high"), which correspond to the
    complement of positive sets, i.e. they include all but
    the sets in a given collection.
  
  This model is inspired by the standard formalisation of
  ZF set theory in Coq. Visit https://github.com/coq-contribs/zfc.
*)
Require Import Setoid Morphisms.

Inductive set :=
  | Low : forall {X}, (X -> set) -> set
  | High : forall {X}, (X -> set) -> set
.
Notation 𝓥 := set.

(* Set equality *)
Fixpoint eeq a b := match a,b with
  | Low _, High _ => False
  | High _, Low _ => False
  | Low f, Low g =>
      (forall x, exists y, eeq (f x) (g y)) /\ (forall y, exists x, eeq (f x) (g y))
  | High f, High g =>
      (forall x, exists y, eeq (f x) (g y)) /\ (forall y, exists x, eeq (f x) (g y))
end.
Notation "A ≡ B" := (eeq A B) (at level 85).

(* Set membership *)
Definition iin a b := match b with
  | Low f => exists x, eeq (f x) a
  | High f => forall x, ~ eeq (f x) a
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

(** Register [set, eeq] as a setoid: *)
Instance nfo_setoid : Equivalence eeq.
Proof.
  constructor. exact @eeq_refl. exact @eeq_sym. exact @eeq_trans.
Qed.

(** Equality is sound w.r.t. membership *)

Lemma in_sound_right:
  forall {x y}, x ≡ y -> forall z, z ∈ x -> z ∈ y.
Proof.
  destruct x; destruct y; simpl eeq; intros e z; simpl iin; simpl eeq; intros; destruct e.
  - destruct H. destruct (H0 x). exists x0. pose proof (eeq_sym H2). apply (eeq_trans H3 H).
  - destruct (H1 x). intro. apply (H x0). transitivity (s0 x); auto.
Qed.

Lemma in_sound_left:
  forall {x y}, x ≡ y -> forall z, x ∈ z -> y ∈ z.
Proof.
  destruct z; simpl iin; intros.
  - destruct H0. exists x0. apply (eeq_trans H0 H).
  - rewrite<- H. apply (H0 x0).
Qed.

Add Morphism iin with signature eeq ==> eeq ==> iff as iin_mor.
Proof.
  intros. split; intro.
  - apply (in_sound_left H). apply (in_sound_right H0). auto.
  - apply (in_sound_left (eeq_sym H)). apply (in_sound_right (eeq_sym H0)). auto.
Qed.

(** We call [pos] the sets having a positive extension *)
Definition pos x := match x with
  | Low _ => True
  | High _ => False
end.