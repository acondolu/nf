Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Require Export Relation_Definitions.
Require Export Setoid.

Add LoadPath "src".
From Internal Require Import FunExt.
From NFO Require Import Bool Model Wff Eeq Iin Sets Xor.

(* Aext *)

Lemma Aeq_Ain: forall {X Y} {f: X -> _} {g: Y -> _},
  Aeq f g -> forall x, Ain x f <-> Ain x g.
Proof.
  intros. unfold Ain. destruct H. split; intro; destruct H1.
  - destruct (H x0). exists x1. apply (eeq_trans (eeq_sym H2) H1).
  - destruct (H0 x0). exists x1. apply (eeq_trans H2 H1).
Qed.
Lemma Ain_Aeq: forall {X Y} {f: X -> _} {g: Y -> _},
  (forall x, Ain x f <-> Ain x g) -> Aeq f g.
Proof.
  intros. unfold Aeq. split; intro x.
  - destruct (H (f x)). cut (Ain (f x) f). intro. destruct (H0 H2).
    exists x0. eauto with Eeq. unfold Ain. eauto with Eeq.
  - destruct (H (g x)). cut (Ain (g x) g). intro. destruct (H1 H2).
    exists x0. eauto with Eeq. unfold Ain. eauto with Eeq.
Qed.

Theorem Aext {X Y} {f: X -> _} {g: Y -> _} :
  Aeq f g <-> forall x, Ain x f <-> Ain x g.
Proof. split. apply Aeq_Ain. apply Ain_Aeq. Qed.

Lemma eeq_Ain: forall {x y X} {f: X -> _},
  x == y -> Ain x f <-> Ain y f.
Proof.
  intros. unfold Ain. split; intro; destruct H0; exists x0.
  apply (eeq_trans H0 H). apply (eeq_trans H0 (eeq_sym H)).
Qed.

(* respects eeq (iin z)
/\ respecs eeq (fun x => iin x z) *)

Lemma iin_respects_eeq: forall z x y, eeq x y ->
  (iin z x <-> iin z y)
  /\ (iin x z <-> iin y z).
Proof.
  induction z.
  apply (wf_two_ind (fun x y => eeq x y -> _: Prop)).
  destruct x1, x2. intros. repeat rewrite iin_unfold. split; apply xor_iff.
  - apply Aeq_Ain. rewrite eeq_unfold in H2; destruct H2. assumption.
  - rewrite eeq_unfold in H2; destruct H2. unfold eeq_boolean in H1.
    pose (fun s : set =>
      (exists a0, s == h0 a0 /\ iin (h0 a0) (S A p h X f))
      \/ (exists a1, s == h1 a1 /\ iin (h1 a1) (S A p h X f))
    ) as g.
    repeat rewrite boolean_map_compose in H3.
    cut (eval (boolean_map (Basics.compose g h0) p0) <-> (let w := fun a : A0 => iin (h0 a) (S A p h X f) in eval (boolean_map w p0))). intro.
    cut (eval (boolean_map (Basics.compose g h1) p1) <-> (let w := fun a : A1 => iin (h1 a) (S A p h X f) in eval (boolean_map w p1))). intro.
    rewrite<- H4. rewrite<- H5. 
    cut (respects eeq g). 
    -- repeat rewrite<- boolean_map_compose. apply H3.
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
  - apply eeq_Ain. rewrite eeq_unfold. rewrite eeq_unfold in H2; destruct H2. auto.
  - apply boolean_map_extP. unfold FunExt.extP. intro a.
    apply (proj1 (H a (S A0 p0 h0 X0 f0) (S A1 p1 h1 X1 f1) H2)).
Qed.

Add Morphism iin with signature eeq ==> eeq ==> iff as iin_mor.
Proof.
  intros. destruct (iin_respects_eeq x x0 y0 H0).
  destruct (iin_respects_eeq y0 x y H). tauto.
Qed.

(* Qext *)

Lemma aux {X p} {h: X -> _} {x}:
  eval (boolean_map (fun x' => iin (h x') x) p)
  <-> 
  Qin x h p.
Proof. induction p; simpl; tauto. Qed.


Lemma Qeq_Qin: forall {X Y} {p p'} {h: X -> _} {h': Y -> _},
  Qeq (boolean_map h p) (boolean_map h' p')
  -> forall x, Qin x h p <-> Qin x h' p'.
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
  respects eeq f ->
  Qin (mk_low f (sum_funs h g)) h p <-> eval (boolean_map f (boolean_map h p)).
Proof.
  intro. induction p; simpl; simpl boolean_map; simpl Qin; simpl eval.
  - tauto.
  - unfold mk_low. rewrite iin_unfold. simpl. unfold Ain.
    rewrite xor_false_r. split; intros.
    destruct H0, x0, x0.
    simpl sum_funs in *. apply (H (h x0) (h x) H0). assumption.
    simpl sum_funs in *. apply (H (g y) (h x) H0). assumption.
    exists (existT _ (inl x) H0). eauto with Eeq.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

Lemma xxx_r {X Y} {p} {h: X -> _} {f: set -> Prop} (g: Y -> _):
  respects eeq f ->
  Qin (mk_low f (sum_funs g h)) h p <-> eval (boolean_map f (boolean_map h p)).
Proof.
  intro. induction p; simpl; simpl boolean_map; simpl Qin; simpl eval.
  - tauto.
  - unfold mk_low. rewrite iin_unfold. simpl. unfold Ain.
    rewrite xor_false_r. split; intros.
    destruct H0, x0, x0.
    simpl sum_funs in *. apply (H (g y) (h x) H0). assumption.
    simpl sum_funs in *. apply (H (h x0) (h x) H0). assumption.
    exists (existT _ (inr x) H0). eauto with Eeq.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

Lemma Qin_Qeq: forall {X Y} {p p'} {h: X -> _} {h': Y -> _},
  (forall x, Qin x h p <-> Qin x h' p')
  -> Qeq (boolean_map h p) (boolean_map h' p').
Proof.
  intros. unfold Qeq, eeq_boolean. intros.
  pose (mk_low P h) as g.
  pose proof (H g).
  rewrite<- (xxx h'). rewrite<- (xxx_r h). apply H. auto. auto.
Qed.

Theorem Qext {X Y} {p p'} {h: X -> _} {h': Y -> _} :
  Qeq (boolean_map h p) (boolean_map h' p')
  <-> forall x, Qin x h p <-> Qin x h' p'.
Proof. split. apply Qeq_Qin. apply Qin_Qeq. Qed.

Lemma eeq_Qin: forall {x y A p} {h: A -> _},
  x == y -> Qin x h p <-> Qin y h p.
Proof.
  intros x y A p. induction p; simpl Qin. 
  - tauto.
  - intro. apply iin_respects_eeq.
  - intro. specialize IHp with h. tauto.
  - intro h. specialize IHp1 with h. specialize IHp2 with h. tauto.
Qed.

(* Extensionality *)

Definition ext_empty x := forall z, ~ iin z x.

Lemma xor_ext: forall {x y},
  (forall z, iin z x <-> iin z y) <-> ext_empty (QXor x y).
Proof.
  intros.
  unfold ext_empty.
  setoid_rewrite xor_ok.
  setoid_rewrite Xor_neg.
  apply iff_refl.
Qed.

Lemma weak_regularity x :
  match x with S _ _ _ _ f => Ain x f -> False end.
Proof.
  induction x. intros. unfold Ain in H1. destruct H1.
  pose proof (H0 x). assert (H1' := H1). destruct (f x) in H1, H2.
  apply H2. unfold Ain. assert (H1'' := H1).
  rewrite eeq_unfold in H1. destruct H1, H1.
  destruct (H4 x). exists x0.
  apply (eeq_trans (eeq_trans H5 H1') (eeq_sym H1'')).
Qed.
