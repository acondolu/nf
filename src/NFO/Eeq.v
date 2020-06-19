Add LoadPath "src/NFO/".
Require Import FunExt.
Require Import Bool.
Require Import Model.
Require Import Wff.

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
              (boolean_map inl p) (boolean_map inr p')
    end) eq_refl
 ))
 ; rewrite eqx; eauto with Wff.
Defined.

Definition eeq x y := eeq' (x, y).
Infix "==" := eeq (at level 50) : type_scope.

Definition eeq_low {X Y} f g :=
  (forall x: X, exists y, f x == g y)
  /\ forall y: Y, exists x, f x == g y.

Lemma eeq_def : forall x y, eeq x y <->
  match x, y with S A p h X f, S A' p' h' X' f'
    => eeq_low f f'
        /\  
          eeq_boolean (sum_i eeq h h') (boolean_map inl p) (boolean_map inr p')
end.
Proof.
  apply wf_two_ind.
  destruct x1, x2. intros.
  unfold eeq at 1. unfold eeq' at 1. rewrite Fix_iff. fold eeq'.
  - unfold eeq_low. unfold sum_i. tauto.
  - intros. destruct x. destruct s. destruct s0.
    Require Import Xor. apply And_eq3.
    -- split; intros. destruct (H1 x). exists x0. rewrite<- H0. assumption.
        destruct (H1 x). exists x0. rewrite H0. assumption.
    -- split; intros. destruct (H1 y). exists x. rewrite<- H0. assumption.
    destruct (H1 y). exists x. rewrite H0. assumption.
    -- apply eeq_boolean_ext. unfold FunExt.extP2. intros.
       destruct x, y; repeat rewrite H0; tauto.
Qed.

Lemma eeq_refl {x} : eeq x x.
Proof.
  induction x. rewrite eeq_def. unfold eeq_low. split.
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
  - revert H1. apply eeq_boolean_sym.
Qed.
Hint Resolve eeq_sym : Eeq.

Lemma eeq_trans : forall {x y z}, eeq x y -> eeq y z -> eeq x z.
Proof.
  apply (wf_three_ind (fun x y z => eeq x y -> eeq y z -> eeq x z)).
  destruct x1. destruct x2. destruct x3. intros. 
  rewrite eeq_def in *. unfold eeq_low in *.
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

(* eeq high *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Lemma eeq_b_simplified:
  forall {X Y p p'} {h: X -> set} {h': Y -> set},
    eeq_boolean (sum_i eeq h h') (boolean_map inl p) (boolean_map inr p')
    <->
    eeq_boolean eeq (boolean_map h p) (boolean_map h' p').
Proof.
  intros. unfold eeq_boolean. split; intros.
  - specialize H with (compose f (mk_sum h h')).
    repeat rewrite boolean_map_compose in H.
    repeat rewrite compose_assoc in H.
    rewrite<- boolean_map_compose in H.
    rewrite boolean_map_compose_inl in H.
    rewrite<- boolean_map_compose in H.
    rewrite boolean_map_compose_inr in H.
    apply H. unfold respects in *. intros.
    destruct x, x'; unfold compose, mk_sum; apply H0; apply H1.
  - pose (invert_sum f (compose eeq h) (compose eeq h')) as g.
    specialize H with g.
    cut (respects eeq g).
  -- intro. repeat rewrite boolean_map_compose.
    rewrite (boolean_map_extP (compose f inl) (compose g h)).
    rewrite (boolean_map_extP (compose f inr) (compose g h')).
    repeat rewrite<- boolean_map_compose. apply (H H1).
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

Require Import Setoid.
Lemma eeq_unfold {A p h X f A' p' h' X' f'}:
  eeq (S A p h X f) (S A' p' h' X' f') <->
    eeq_boolean eeq (boolean_map h p) (boolean_map h' p')
      /\  
    eeq_low f f'
.
Proof.
  rewrite<- eeq_b_simplified.
  rewrite eeq_def.
  tauto.
Qed.
