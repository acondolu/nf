(** * NFO.Eeq : Equality of NFO sets *)
(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Require Import Setoid Morphisms.
Add LoadPath "src".
From Internal Require Import Aux FunExt.
From NFO Require Import BoolExpr Model Wff.
(* end hide *)

(** TODO: rename to Eq *)

(* begin hide *)
Local Definition eeq' : set * set -> Prop.
refine ( Fix wf_two (fun _ => Prop) (
  fun x rec => (
    match x as x0 return (x = x0 -> Prop) with
    | (S X Y f g e, S X' Y' f' g' e') => fun eqx =>
          ((forall x, exists x', rec (f x, f' x') _)
          /\ (forall x', exists x, rec (f x, f' x') _))
          /\ let w (yy yy': Y + Y') := match yy, yy' with
            | inl y, inl y' => rec (g y, g y') _
            | inl y, inr y' => rec (g y, g' y') _
            | inr y, inl y' => rec (g' y, g y') _
            | inr y, inr y' => rec (g' y, g' y') _
            end in 
            eeq_boolean w (map inl e) (map inr e')
    end) eq_refl
 ))
 ; rewrite eqx; eauto with Wff.
Defined.
(* end hide *)

Definition eeq : set -> set -> Prop.
  intros x y. exact (eeq' (x, y)).
Defined.
Infix "==" := eeq (at level 50) : type_scope.

(** * "Aczel" equality: *)
Definition Aeq {X Y} f g :=
  (forall x: X, exists y, f x == g y) /\ forall y: Y, exists x, f x == g y.

(* Temporary unfolding lemma for eeq. 
   It will be improved in eeq_unfold. *)
Local Lemma eeq_def : forall x y,
  eeq x y <-> match x, y with S X Y f g e, S X' Y' f' g' e' =>
    Aeq f f'
      /\
        eeq_boolean (eeq ⨀ (g ⨁ g')) (map inl e) (map inr e')
end.
Proof.
  apply wf_two_ind.
  destruct x1, x2. intros.
  unfold eeq at 1. unfold eeq' at 1. rewrite Fix_iff. fold eeq'.
  - apply and_morph. apply iff_refl. apply eeq_boolean_ext.
    unfold compR, sumF, extR. intros. destruct x, y; apply iff_refl.
  - intros. destruct x, s, s0. apply and_morph. apply and_morph.
    -- split; intros. destruct (H1 x). exists x0. rewrite<- H0. assumption.
        destruct (H1 x). exists x0. rewrite H0. assumption.
    -- split; intros. destruct (H1 x'). exists x. rewrite<- H0. assumption.
    destruct (H1 x'). exists x. rewrite H0. assumption.
    -- apply eeq_boolean_ext. unfold FunExt.extR. intros.
       destruct x, y; repeat rewrite H0; tauto.
Qed.

(** eeq is an equivalence relation: *)
Lemma eeq_refl: forall x, eeq x x.
Proof.
  induction x. rewrite eeq_def. unfold Aeq. split.
  split; intro; eauto. eauto with Bool.
Qed.
Hint Immediate eeq_refl : Eeq.

Lemma eeq_sym: forall x y, eeq x y -> eeq y x.
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

Lemma eeq_trans : forall x y z, eeq x y -> eeq y z -> eeq x z.
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
  - apply (fun X => eeq_boolean_trans eeq_sym X H2 H4).
    intros. repeat destruct H6; destruct H7; repeat destruct H6; destruct H8; repeat destruct H6; apply (fun X => H _ _ _ X H9 H10); eauto with Wff.
Qed.
Hint Resolve eeq_trans : Eeq.

(** Register (set, eeq) as a setoid: *)
Instance nfo_setoid : Equivalence eeq.
Proof.
  constructor. exact @eeq_refl. exact @eeq_sym. exact @eeq_trans.
Qed.

(** Aeq is an equivalence *)
Lemma Aeq_refl: forall {X} f, @Aeq X X f f.
Proof. intros. unfold Aeq. eauto with Eeq. Qed.

Lemma Aeq_sym: forall {X Y} f g, @Aeq X Y f g -> Aeq g f.
Proof.
  unfold Aeq. intros. destruct H. split; intro z.
  destruct (H0 z). eauto with Eeq.
  destruct (H z). eauto with Eeq.
Qed.

Lemma Aeq_trans: forall {X Y Z} f g h, @Aeq X Y f g -> @Aeq Y Z g h -> Aeq f h.
Proof.
  unfold Aeq. intros. destruct H, H0. split; intro z.
  destruct (H z).  destruct (H0 x). eauto with Eeq.
  destruct (H2 z). destruct (H1 x). eauto with Eeq.
Qed.

(** "Quine" equality *)
(** TODO: rename in Beq *)
Definition Qeq := eeq_boolean eeq.

(** The good unfolding lemma for eeq: *)
Lemma eeq_unfold {X' Y' f' g' e' X Y f g e}:
  eeq (S X Y f g e) (S X' Y' f' g' e')
    <-> Aeq f f' /\ Qeq (map g e) (map g' e').
Proof.
  unfold Qeq. rewrite<- (eeq_boolean_simpl nfo_setoid).
  rewrite eeq_def.
  tauto.
Qed.
