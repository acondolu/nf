Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Setoid Morphisms.

Add LoadPath "src".
From Internal Require Import Aux FunExt.
From NFO Require Import BoolExpr Model Wff.

Definition eeq' : set * set -> Prop.
refine ( Fix wf_two (fun _ => Prop) (
  fun x rec => (
    match x as x0 return (x = x0 -> Prop) with
    | (S A p h X f, S A' p' h' X' f') => fun eqx =>
          (forall x, exists y, rec (f x, f' y) _)
          /\ (forall y, exists x, rec (f x, f' y) _)
          /\ let w (i j: A + A') := match i, j with
            | inl i', inl j' => rec (h i', h j') _
            | inl i', inr j' => rec (h i', h' j') _
            | inr i', inl j' => rec (h' i', h j') _
            | inr i', inr j' => rec (h' i', h' j') _
            end in 
            eeq_boolean w
              (map inl p) (map inr p')
    end) eq_refl
 ))
 ; rewrite eqx; eauto with Wff.
Defined.

Definition eeq x y := eeq' (x, y).
Infix "==" := eeq (at level 50) : type_scope.

(* "Aczel" equality *)
Definition Aeq {X Y} f g :=
  (forall x: X, exists y, f x == g y)
  /\ forall y: Y, exists x, f x == g y.

Lemma And_eq2 {a a' b b'}:
  (a <-> a') -> (b <-> b') -> (a /\ b) <-> (a' /\ b').
Proof. tauto. Qed.

(* Temporary unfolding lemma for eeq. 
   It will be improved in eeq_unfold. *)
Local Lemma eeq_def : forall x y, eeq x y <->
  match x, y with S A p h X f, S A' p' h' X' f'
    => Aeq f f'
    /\ eeq_boolean (eeq ⨀ (h ⨁ h'))
        (map inl p) (map inr p')
end.
Proof.
  apply wf_two_ind.
  destruct x1, x2. intros.
  unfold eeq at 1. unfold eeq' at 1. rewrite Fix_iff. fold eeq'.
  - rewrite<- and_assoc. apply And_eq2. apply iff_refl. apply eeq_boolean_ext.
    unfold compR, sumF, extR. destruct x, y; apply iff_refl.
  - intros. destruct x. destruct s. destruct s0.
    apply And_eq3.
    -- split; intros. destruct (H1 x). exists x0. rewrite<- H0. assumption.
        destruct (H1 x). exists x0. rewrite H0. assumption.
    -- split; intros. destruct (H1 y). exists x. rewrite<- H0. assumption.
    destruct (H1 y). exists x. rewrite H0. assumption.
    -- apply eeq_boolean_ext. unfold FunExt.extR. intros.
       destruct x, y; repeat rewrite H0; tauto.
Qed.

Lemma eeq_refl {x} : eeq x x.
Proof.
  induction x. rewrite eeq_def. unfold Aeq. split.
  split; intro; eauto. eauto with Bool.
Qed.
Hint Immediate eeq_refl : Eeq.

Lemma eeq_sym : forall {x y}, eeq x y -> eeq y x.
Proof.
  apply (wf_two_ind (fun x y => eeq x y -> eeq y x)).
  destruct x1, x2.
  repeat rewrite eeq_def. intros. repeat destruct H0.
  split. split.
  - intro x0. destruct (H2 x0). eauto with Wff.
  - intro x. destruct (H0 x). eauto with Wff.
  - revert H1. exact eeq_boolean_sym.
Qed.
Hint Resolve eeq_sym : Eeq.

Lemma eeq_trans : forall {x y z}, eeq x y -> eeq y z -> eeq x z.
Proof.
  apply (wf_three_ind (fun x y z => eeq x y -> eeq y z -> eeq x z)).
  destruct x1, x2, x3. 
  repeat rewrite eeq_def. unfold Aeq in *. intros.
  repeat destruct H0. repeat destruct H1.
  split. split.
  - intro x. destruct (H0 x). destruct (H1 x0).
    eauto with Wff.
  - intro y. destruct (H5 y). destruct (H3 x).
    eauto with Wff.
  - apply (fun X => eeq_boolean_trans (@eeq_sym) X H2 H4).
    intros. repeat destruct H6; destruct H7; repeat destruct H6; destruct H8; repeat destruct H6; apply (fun X => H _ _ _ X H9 H10); eauto with Wff.
Qed.
Hint Resolve eeq_trans : Eeq.

(* Register eeq as an equivalence *)
Instance eeqs : Equivalence eeq.
Proof.
  constructor. exact @eeq_refl. exact @eeq_sym. exact @eeq_trans.
Qed.

Lemma Aeq_refl: forall X f, @Aeq X X f f.
Proof. intros. unfold Aeq. eauto with Eeq. Qed.

Lemma Aeq_sym: forall X Y f g, @Aeq X Y f g -> Aeq g f.
Proof.
  unfold Aeq. intros. destruct H. split; intro z.
  destruct (H0 z). eauto with Eeq.
  destruct (H z). eauto with Eeq.
Qed.

Lemma Aeq_trans: forall {X Y Z} f g h, @Aeq X Y f g -> Aeq g h -> @Aeq X Z f h.
Proof.
  unfold Aeq. intros. destruct H, H0. split; intro z.
  destruct (H z).  destruct (H0 x). eauto with Eeq.
  destruct (H2 z). destruct (H1 x). eauto with Eeq.
Qed.

(* Register Aeq as an equivalence *)
(* Instance eeqs X Y : Equivalence (@Aeq X Y). *)
(* Impossible? Because of equivalences must be homogeneous *)

(* "Quine" equality *)
Definition Qeq := eeq_boolean eeq.

(* TODO: move this to Bool.v: *)
Lemma eeq_boolean_qeq:
  forall {X Y p p'} {h: X -> set} {h': Y -> set},
    eeq_boolean
      (eeq ⨀ (h ⨁ h'))
        (map inl p) (map inr p')
    <->
    Qeq (map h p) (map h' p').
Proof.
  intros. unfold Qeq, eeq_boolean. split; intros.
  - specialize H with (compose P (h ⨁ h')).
    repeat rewrite map_compose in H.
    repeat rewrite compose_assoc in H.
    rewrite<- map_compose in H.
    rewrite map_compose_inl in H.
    rewrite<- map_compose in H.
    rewrite map_compose_inr in H.
    apply H. unfold respects in *. intros.
    destruct x, x'; unfold compose, sumF; apply H0; apply H1.
  - pose (invert_sum P (compose eeq h) (compose eeq h')) as g.
    specialize H with g.
    cut (respects eeq g).
  -- intro. repeat rewrite map_compose.
    rewrite (map_extP (compose P inl) (compose g h)).
    rewrite (map_extP (compose P inr) (compose g h')).
    repeat rewrite<- map_compose. apply (H H1).
    --- unfold FunExt.extP. unfold compose.
        intros. unfold g. split; intro.
        right. exists x. split; auto. apply eeq_refl.
        repeat destruct H2.
        apply (H0 (inl x0)); auto.
        apply (H0 (inr x0)); auto.
    --- unfold FunExt.extP. unfold compose.
        intros. unfold g. split; intro.
        left. exists x. split; auto. apply eeq_refl.
        repeat destruct H2.
        apply (H0 (inl x0)); auto.
        apply (H0 (inr x0)); auto.
  -- unfold respects in *. unfold g. intros.
     split; intros; repeat destruct H2.
     left. eauto with Eeq.
     right. eauto with Eeq.
     left. exists x0. eauto with Eeq.
     right. exists x0. eauto with Eeq.
Qed.


Lemma eeq_unfold {A p h X f A' p' h' X' f'}:
  eeq (S A p h X f) (S A' p' h' X' f')
  <->
  Aeq f f'
    /\
  Qeq (map h p) (map h' p')
.
Proof.
  rewrite<- eeq_boolean_qeq.
  rewrite eeq_def.
  tauto.
Qed.
