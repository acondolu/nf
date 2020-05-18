
(* see also https://github.com/coq-contribs/zfc *)
Inductive set :=
  | Pos : forall {X}, (X -> set) -> set
  | Neg : forall {X}, (X -> set) -> set
.
Notation 𝓥 := set.

(* Set equality *)
Fixpoint eeq a b := match a,b with
  | Pos _, Neg _ => False
  | Neg _, Pos _ => False
  | Pos f, Pos g =>
      (forall x, exists y, eeq (f x) (g y)) /\ (forall y, exists x, eeq (f x) (g y))
  | Neg f, Neg g =>
      (forall x, exists y, eeq (f x) (g y)) /\ (forall y, exists x, eeq (f x) (g y))
end.
Notation "A ≡ B" := (eeq A B) (at level 85).

(* Set membership *)
Definition iin a b := match b with
  | Pos f => exists x, eeq (f x) a
  | Neg f => forall x, eeq (f x) a -> False
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

(* Equality is sound w.r.t. membership *)

Lemma in_sound_right:
  forall {x y}, x ≡ y -> forall z, z ∈ x -> z ∈ y.
Proof.
  destruct x; destruct y; simpl eeq; intros e z; simpl iin; simpl eeq; intros; destruct e.
  - destruct H. destruct (H0 x). exists x0. pose proof (eeq_sym H2). apply (eeq_trans H3 H).
  - destruct (H2 x). pose proof (eeq_trans H3 H0). apply (H _ H4).
Qed.

Lemma in_sound_left:
  forall {x y}, x ≡ y -> forall z, x ∈ z -> y ∈ z.
Proof.
  destruct z; simpl iin; intros.
  - destruct H0. exists x0. apply (eeq_trans H0 H).
  - apply (H0 x0). apply (eeq_trans H1 (eeq_sym H)).
Qed.

(* ZF set (with positive extension) *)
Definition zf x := match x with
  | Pos _ => True
  | Neg _ => False
end.