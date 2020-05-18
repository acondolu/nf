Add LoadPath "src/".
Require Import Simplest.

Lemma weak_regularity: forall {x}, zf x -> iin x x -> False.
Proof.
  induction x; simpl zf; auto; intros.
  destruct H1. apply (H x).
  - destruct (s x); simpl; auto.
  - assert (H1' := H1). destruct (s x) in H1; destruct H1.
    destruct (H2 x).
    apply (in_sound_left (eeq_sym H1')).
    apply (in_sound_right (eeq_sym H1')).
    exists x. assumption. 
Qed.

Definition f_sum {X Y} f g (z: X + Y): set :=
  match z with
  | inl x => f x
  | inr y => g y
  end
.

Require Import Coq.Logic.Classical_Prop.

Lemma contra: forall X f Y g, (forall z, iin z (@Pos X f) <-> iin z (@Neg Y g)) -> (forall z, iin z (@Pos (X + Y) (f_sum f g))).
Proof.
  intros. simpl iin in *.
  pose proof (H z).
  destruct (classic (exists x : X, eeq (f x) z)).
  - destruct H1. exists (inl x). simpl f_sum. assumption.
  - cut (exists y : Y, eeq (g y) z). intro. destruct H2.
    exists (inr x). auto.
  destruct H0. pose proof (fun T => H1 (H2 T)).
  apply NNPP. intro. apply H3. intros. apply H4. exists x. auto.
Qed.

Lemma contra': forall X f Y g, (forall z, iin z (@Pos X f) <-> iin z (@Neg Y g)) -> False.
Proof.
  intros.
  pose proof (contra _ _ _ _ H).
  apply (@weak_regularity (@Pos (X + Y) (f_sum f g)) I). apply H0.
Qed.

Lemma ext2: forall X f Y g, (forall z, iin z (@Pos X f) <-> iin z (@Pos Y g)) -> eeq (@Pos X f) (@Pos Y g).
Proof.
  intros. simpl; split; intro.
  - destruct (H (f x)). simpl iin in H0.
    cut (exists x0 : X, eeq (f x0) (f x)). intro. destruct (H0 H2). exists x0. apply eeq_sym. assumption. exists x. apply eeq_refl.
  - destruct (H (g y)). simpl iin in H1.
  cut (exists x : Y, eeq (g x) (g y)). intro. destruct (H1 H2). exists x. assumption. exists y. apply eeq_refl.
Qed.

Require Import Coq.Logic.Classical_Pred_Type.

Lemma ext3: forall X f Y g, (forall z, iin z (@Neg X f) <-> iin z (@Neg Y g)) -> eeq (@Pos X f) (@Pos Y g).
Proof.
  intros. simpl; split; intro.
  - destruct (H (f x)). simpl iin in H1.
    apply NNPP. intro.
    cut (forall x0 : Y, eeq (g x0) (f x) -> False). intro.
    pose proof (H1 H3). apply (H4 x). apply eeq_refl. intros.
    pose proof (eeq_sym H3). revert H4. clear H3. revert x0.
    apply not_ex_all_not. assumption.
  - destruct (H (g y)). simpl iin in H0.
  apply NNPP. intro.
  cut (forall x : X, eeq (f x) (g y) -> False). intro.
  pose proof (H0 H3). apply (H4 y). apply eeq_refl.
  apply not_ex_all_not. assumption.
Qed.

Lemma extensionality: forall x y, x ≡ y <-> forall z, z ∈ x <-> z ∈ y.
Proof.
  intros. split. intros. split; apply in_sound_right; auto. apply eeq_sym. assumption.
  destruct x; destruct y.
  - apply ext2.
  - intros. destruct (contra' _ _ _ _ H).
  - intros. cut (forall z : set, iin z (@Pos X0 s0) <-> iin z (@Neg X s)).
    intro. destruct (contra' _ _ _ _ H0).
    intro z. apply iff_sym. apply (H z). 
  - apply ext3.
Qed.