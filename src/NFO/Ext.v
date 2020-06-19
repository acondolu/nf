Add LoadPath "src/NFO/".
Require Import Bool.
Require Import Model.
Require Import Wff.
Require Import Eeq.
Require Import Iin.

Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.

Require Import Xor.

(* LOW *)

Lemma eeq_iin_low_1: forall {x y X} {f: X -> _},
  x == y -> iin_low x f <-> iin_low y f.
Proof.
  intros. unfold iin_low. split; intro; destruct H0; exists x0.
  apply (eeq_trans H0 H). apply (eeq_trans H0 (eeq_sym H)).
Qed.
Lemma eeq_iin_low_2: forall {X Y} {f: X -> _} {g: Y -> _},
  eeq_low f g -> forall x, iin_low x f <-> iin_low x g.
Proof.
  intros. unfold iin_low. destruct H. split; intro; destruct H1.
  - destruct (H x0). exists x1. apply (eeq_trans (eeq_sym H2) H1).
  - destruct (H0 x0). exists x1. apply (eeq_trans H2 H1).
Qed.
Lemma eeq_iin_low_3: forall {X Y} {f: X -> _} {g: Y -> _},
  (forall x, iin_low x f <-> iin_low x g) -> eeq_low f g.
Proof.
  intros. unfold eeq_low. split; intro x.
  - destruct (H (f x)). cut (iin_low (f x) f). intro. destruct (H0 H2).
    exists x0. eauto with Eeq. unfold iin_low. eauto with Eeq.
  - destruct (H (g x)). cut (iin_low (g x) g). intro. destruct (H1 H2).
    exists x0. eauto with Eeq. unfold iin_low. eauto with Eeq.
Qed.

Theorem low_ext {X Y} {f: X -> _} {g: Y -> _} :
  eeq_low f g <-> (forall x, iin_low x f <-> iin_low x g).
Proof. split. apply eeq_iin_low_2. apply eeq_iin_low_3. Qed.


(* TODO: Prove extensionality *)

Lemma iin_respects_eeq: forall z x y, eeq x y ->
  (iin z x <-> iin z y)
  /\ (iin x z <-> iin y z).
Proof.
  induction z.
  apply (wf_two_ind (fun x y => eeq x y -> _: Prop)).
  destruct x1, x2. intros. repeat rewrite iin_unfold. split; apply Xor_eq.
  - apply eeq_iin_low_2. rewrite eeq_unfold in H2; destruct H2. assumption.
  - rewrite eeq_unfold in H2; destruct H2. unfold eeq_boolean in H1.
    pose (fun s : set =>
      (exists a0, s == h0 a0 /\ iin (h0 a0) (S A p h X f))
      \/ (exists a1, s == h1 a1 /\ iin (h1 a1) (S A p h X f))
    ) as g.
    repeat rewrite boolean_map_compose in H3.
    cut (eval (boolean_map (Basics.compose g h0) p0) <-> (let w := fun a : A0 => iin (h0 a) (S A p h X f) in eval (boolean_map w p0))). intro.
    cut (eval (boolean_map (Basics.compose g h1) p1) <-> (let w := fun a : A1 => iin (h1 a) (S A p h X f) in eval (boolean_map w p1))). intro.
    rewrite<- H4. rewrite<- H5. 
    cut (respects g eeq). 
    -- repeat rewrite<- boolean_map_compose. apply H2.
    -- unfold respects. intros. unfold g. split; intro; repeat destruct H7.
      left. exists x0. split; eauto with Eeq.
      right. exists x0. split; eauto with Eeq.
      left. exists x0. split; eauto with Eeq.
      right. exists x0. split; eauto with Eeq.
    -- apply boolean_map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold g. split; intro. repeat destruct H5; auto.
       apply (fun K => proj2 (H1 (h0 x) (h1 a1) K (eeq_sym H5))).
       auto with Wff. assumption.
       apply (fun K => proj2 (H1 (h1 x) (h1 a1) K (eeq_sym H5))).
       auto with Wff. assumption.
       right. exists a1. split; eauto with Eeq.
    -- apply boolean_map_extP. unfold FunExt.extP. intro a1.
       unfold Basics.compose. unfold g. split; intro. repeat destruct H4; auto.
       apply (fun K => proj2 (H1 (h0 a1) (h0 x) K H4)).
       auto with Wff. assumption.
       apply (fun K => proj2 (H1 (h0 a1) (h1 x) K H4)).
       auto with Wff. assumption.
       left. exists a1. split; eauto with Eeq.
  - apply eeq_iin_low_1. rewrite eeq_unfold. rewrite eeq_unfold in H2; destruct H2. auto.
  - apply boolean_map_extP. unfold FunExt.extP. intro a.
    apply (proj1 (H a (S A0 p0 h0 X0 f0) (S A1 p1 h1 X1 f1) H2)).
Qed.

(* iin move there? *)

Lemma iin_high_aux {x A} {p: boolean A} {h} :
  (let w a := iin (h a) x
  in eval (boolean_map w p))
  <-> (iin_high x h p).
Proof. induction p; simpl; tauto. Qed.

Lemma iin_unfold' {x A' p' h' X' f'} :
  iin x (S A' p' h' X' f')
    <->
    Xor
      (iin_low x f')
      (iin_high x h' p').
Proof.
  rewrite iin_unfold.
  apply Xor_eq. tauto.
  apply iin_high_aux.
Qed.

Lemma aux {X p} {h: X -> _} {x}:
  eval (boolean_map (fun x' => iin (h x') x) p)
  <-> 
  iin_high x h p.
Proof. induction p; simpl; tauto. Qed.

(* HIGH *)

Lemma eeq_iin_high_1: forall {X Y} {p p'} {h: X -> _} {h': Y -> _},
  eeq_boolean eeq (boolean_map h p) (boolean_map h' p')
  -> forall x, iin_high x h p <-> iin_high x h' p'.
Proof.
  intros. unfold eeq_boolean in H.
  pose proof (H (fun s => iin s x)).
  repeat rewrite boolean_map_compose in H0.
  unfold Basics.compose in H0.
  repeat rewrite<- aux. apply H0.
  unfold respects. intros.
  apply iin_respects_eeq. assumption.
Qed.

Definition mk_low {X} f h :=
S False (Bot _) (False_rect _) { x: X & f (h x) } (fun k => h (projT1 k)).

Lemma xxx {X Y} {p} {h: X -> _} {f: set -> Prop} (g: Y -> _):
respects f eeq ->
iin_high (mk_low f (mk_sum h g)) h p <-> eval (boolean_map f (boolean_map h p)).
Proof.
  intro. induction p; simpl; simpl boolean_map; simpl iin_high; simpl eval.
  - tauto.
  - unfold mk_low. rewrite iin_unfold. unfold Xor. simpl. unfold iin_low. split; intros.
  repeat destruct H0. destruct x0. apply (H _ _ H0). assumption.
  split. left. exists (existT _ (inl x) H0). eauto with Eeq. tauto.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

Lemma xxx_r {X Y} {p} {h: X -> _} {f: set -> Prop} (g: Y -> _):
respects f eeq ->
iin_high (mk_low f (mk_sum g h)) h p <-> eval (boolean_map f (boolean_map h p)).
Proof.
  intro. induction p; simpl; simpl boolean_map; simpl iin_high; simpl eval.
  - tauto.
  - unfold mk_low. rewrite iin_unfold. unfold Xor. simpl. unfold iin_low. split; intros.
  repeat destruct H0. destruct x0. apply (H _ _ H0). assumption.
  split. left. exists (existT _ (inr x) H0). eauto with Eeq. tauto.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

Lemma eeq_iin_high_2: forall {X Y} {p p'} {h: X -> _} {h': Y -> _},
  (forall x, iin_high x h p <-> iin_high x h' p')
  -> eeq_boolean eeq (boolean_map h p) (boolean_map h' p').
Proof.
  intros. unfold eeq_boolean. intros.
  pose (mk_low f h) as g.
  pose proof (H g).
  rewrite<- (xxx h'). rewrite<- (xxx_r h). apply H. auto. auto.
Qed.

Theorem high_ext {X Y} {p p'} {h: X -> _} {h': Y -> _} :
  eeq_boolean eeq (boolean_map h p) (boolean_map h' p')
  <-> forall x, iin_high x h p <-> iin_high x h' p'.
Proof. split. apply eeq_iin_high_1. apply eeq_iin_high_2. Qed.
