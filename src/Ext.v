Add LoadPath "src/".
Require Import Simplest.


Lemma in_sound_right:
  forall x y, x ≡ y -> forall z, z ∈ x -> z ∈ y.
Proof.
  destruct x; destruct y; simpl eeq; intros e z; simpl iin; simpl eeq; intros; destruct e.
  - destruct H. destruct (H0 x). exists x0. pose proof (eeq_sym H2). apply (eeq_trans H3 H).
  - destruct (H2 x). pose proof (eeq_trans H3 H0). apply (H _ H4).
Qed.

Definition isPos x := match x with
  | Pos _ _ => True
  | _ => False end.

  Definition getX x := match x with
  | Pos X _ => X
  | Neg X _ => X end.

  Definition getf x: getX x -> set := match x with
  | Pos X f => f
  | Neg X f => f end.

Lemma boh': forall a, isPos a -> forall x : getX a, forall b, b = getf a x -> eeq (getf a x) a -> False.
Proof.
  intro a. induction a. unfold getX, getf. intros.
  - destruct b. rewrite<- H1 in H2. destruct H2.
    destruct (H3 x).
    cut (isPos (s x)). intro.
    pose proof (H x).
    rewrite<- H1 in H6.
    rewrite<- H1 in H5.
    pose proof (H6 H5 x0 (s0 x0) (eq_refl _)).
    rewrite<- H1 in H4.
    apply (H7 H4).
    rewrite<- H1. auto.
    rewrite<- H1 in H2. destruct H2.
  - intros. destruct H0.
Qed.

Lemma boh'': forall X f x, eeq (f x) (Pos X f) -> False.
Proof.
  intros.
  apply (boh' (Pos X f) I x (f x) (eq_refl _) H).
Qed.

 Lemma boh: forall x, isPos x -> iin x x -> False.
 Proof.
  intros.
  induction x.
  - destruct H0. apply (boh'' _ _ _ H0).
  - destruct H.
Qed.

Definition f_sum {X Y} f g (z: X + Y): set :=
  match z with
  | inl x => f x
  | inr y => g y
  end.

Require Import Coq.Logic.Classical_Prop.

Lemma contra: forall X f Y g, (forall z, iin z (Pos X f) <-> iin z (Neg Y g)) -> (forall z, iin z (Pos (X + Y) (f_sum f g))).
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

Lemma contra': forall X f Y g, (forall z, iin z (Pos X f) <-> iin z (Neg Y g)) -> False.
Proof.
  intros.
  pose proof (contra _ _ _ _ H).
  apply (boh (Pos (X + Y) (f_sum f g)) I). apply H0.
Qed.

Lemma ext2: forall X f Y g, (forall z, iin z (Pos X f) <-> iin z (Pos Y g)) -> eeq (Pos X f) (Pos Y g).
Proof.
  intros. simpl; split; intro.
  - destruct (H (f x)). simpl iin in H0.
    cut (exists x0 : X, eeq (f x0) (f x)). intro. destruct (H0 H2). exists x0. apply eeq_sym. assumption. exists x. apply eeq_refl.
  - destruct (H (g y)). simpl iin in H1.
  cut (exists x : Y, eeq (g x) (g y)). intro. destruct (H1 H2). exists x. assumption. exists y. apply eeq_refl.
Qed.

Require Import Coq.Logic.Classical_Pred_Type.

Lemma ext3: forall X f Y g, (forall z, iin z (Neg X f) <-> iin z (Neg Y g)) -> eeq (Pos X f) (Pos Y g).
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
  - intros. cut (forall z : set, iin z (Pos X0 s0) <-> iin z (Neg X s)).
    intro. destruct (contra' _ _ _ _ H0).
    intro z. apply iff_sym. apply (H z). 
  - apply ext3.
Qed.