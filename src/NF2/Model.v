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
(* begin hide *)
Add LoadPath "src".
(* end hide *)
From Internal Require Import Common.

Inductive set :=
  | Low  : forall X, (X -> set) -> set
  | High : forall X, (X -> set) -> set
.

(* Set equality *)
Fixpoint EQ a b := match a,b with
  | Low _ _, High _ _ => False
  | High _ _, Low _ _ => False
  | Low _ f, Low _ g => 
      (forall x, exists y, EQ (f x) (g y)) /\ (forall y, exists x, EQ (f x) (g y))
  | High _ f, High _ g =>
      (forall x, exists y, EQ (f x) (g y)) /\ (forall y, exists x, EQ (f x) (g y))
end.
Notation "A ≡ B" := (EQ A B) (at level 85).

Infix "AEQ" := (eq_aczel EQ) (at level 85).
(** printing AEQ %\ensuremath{\AEQ}% *)

(* Set membership *)
Definition IN a b := match b with
  | Low _ f => exists x, EQ (f x) a
  | High _ f => forall x, ~ EQ (f x) a
end.
Notation "A ∈ B" := (IN A B) (at level 85).

Infix "AIN" := (in_aczel EQ) (at level 85).
(** printing AIN %\ensuremath{\AIN}% *)

(* Equality is an equivalence relation *)

Lemma EQ_refl : forall {x}, x ≡ x.
Proof. induction x; split; intro x; exists x; apply H. Qed.

Ltac ABAB x y := firstorder ; [ x | y | x | y ] .

Lemma EQ_trans : forall {x y z}, x ≡ y -> y ≡ z -> x ≡ z.
Proof.
  induction x; induction y; induction z; intros; simpl EQ; firstorder.
  destruct (H2 x); destruct (H3 x0); exists x1; apply (H _ _ _ H6 H7).
  destruct (H4 y); destruct (H5 x); exists x0; apply (H _ _ _ H7 H6).
  destruct (H2 x). destruct (H3 x0). exists x1. apply (H _ _ _ H6 H7).
  destruct (H4 y). destruct (H5 x). exists x0. apply (H _ _ _ H7 H6).
Qed.

Lemma EQ_sym : forall {x y}, x ≡ y -> y ≡ x.
Proof.
  intro x. induction x; destruct y; simpl EQ; firstorder.
  destruct (H1 x). exists x0. apply (H _ _ H2).
  destruct (H0 y). exists x. apply (H _ _ H2).
  destruct (H1 x). exists x0. apply (H _ _ H2).
  destruct (H0 y). exists x. apply (H _ _ H2).
Qed.

(** Register [set, EQ] as a setoid: *)
Instance nfo_setoid : Equivalence EQ.
Proof.
  constructor. exact @EQ_refl. exact @EQ_sym. exact @EQ_trans.
Qed.

(** Equality is sound w.r.t. membership *)

Lemma in_sound_right:
  forall {x y}, x ≡ y -> forall z, z ∈ x -> z ∈ y.
Proof.
  destruct x, y; simpl EQ; intros e z; simpl IN; simpl EQ; intros; destruct e.
  - destruct H, (H0 x). exists x0. rewrite<- H, H2. reflexivity.
  - destruct (H1 x). intro. apply (H x0). rewrite H2, H3. reflexivity.
Qed.

Lemma in_sound_left:
  forall {x y}, x ≡ y -> forall z, x ∈ z -> y ∈ z.
Proof.
  destruct z; simpl IN; intros.
  - destruct H0. exists x0. apply (EQ_trans H0 H).
  - rewrite<- H. apply (H0 x0).
Qed.

Add Morphism IN with signature EQ ==> EQ ==> iff as IN_mor.
Proof.
  intros. split; intro.
  - apply (in_sound_left H). apply (in_sound_right H0). auto.
  - apply (in_sound_left (EQ_sym H)). apply (in_sound_right (EQ_sym H0)). auto.
Qed.

Definition low x := match x with
  | Low _ _ => True
  | High _ _ => False
end.