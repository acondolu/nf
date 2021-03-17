(** * NFO.Eq : Equality of NFO sets *)
(**
    This module defines [EQ] (in symbols, [==]), the
    equality relation between NFO sets.
*)
From Coq.Program Require Import Basics Combinators.
Require Import Setoid Morphisms.
(* begin hide *)
Add LoadPath "src/Internal" as Internal.
Add LoadPath "src/NFO" as NFO.
(* end hide *)
From Internal Require Import Misc FunExt Common.
From NFO Require Import BoolExpr Model Wf.

Local Definition EQ' : SET * SET -> Prop.
refine ( Fix (wf_two wf_lt) (fun _ => Prop) (
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
            eq_bexpr w (map inl e) (map inr e')
    end) eq_refl
 ))
 ; rewrite eqx; eauto with Wff.
Defined.

(* rewrite eqx; unfold le22'; rewrite decr_unfold; unfold list2, all, List.some, WfMult.all; setoid_rewrite cons_not_nil; clear; try setoid_rewrite le_f_rew; try setoid_rewrite le_g_rew; clear; tauto. *)

Definition EQ : SET -> SET -> Prop.
  intros x y. exact (EQ' (x, y)).
Defined.
Infix "==" := EQ (at level 50) : type_scope.

(** * Aczel part *)
Notation AEQ f g := (eq_aczel EQ f g).
(** printing AEQ %\ensuremath{\AEQ}% *)

(** Temporary unfolding lemma for EQ. 
   It will be improved in EQ_unfold. *)
Lemma EQ_def : forall x y,
  EQ x y <-> match x, y with S X Y f g e, S X' Y' f' g' e' =>
    AEQ f f'
      /\
        eq_bexpr (EQ ⨀ (g ⨁ g')) (map inl e) (map inr e')
end.
Proof.
  apply (wf_two_ind wf_lt).
  destruct x1, x2. intros.
  unfold EQ at 1. unfold EQ' at 1. rewrite Fix_iff. fold EQ'.
  - apply and_morph. apply iff_refl. apply eq_bexpr_ext.
    unfold compR, sumF, extR. intros. destruct x, y; apply iff_refl.
  - intros. destruct x, s, s0. apply and_morph. apply and_morph.
    -- split; intros. destruct (H1 x). exists x0. rewrite<- H0. assumption.
        destruct (H1 x). exists x0. rewrite H0. assumption.
    -- split; intros. destruct (H1 x'). exists x. rewrite<- H0. assumption.
    destruct (H1 x'). exists x. rewrite H0. assumption.
    -- apply eq_bexpr_ext. unfold FunExt.extR. intros.
       destruct x, y; repeat rewrite H0; tauto.
Qed.
Global Opaque EQ.

(** EQ is an equivalence relation: *)
Lemma EQ_refl: forall x, EQ x x.
Proof.
  induction x. rewrite EQ_def. unfold AEQ. split.
  split; intro; eauto. apply eq_bexpr_refl. auto.
Qed.
#[export] Hint Immediate EQ_refl : Eeq.

Lemma EQ_sym: forall x y, EQ x y -> EQ y x.
Proof.
  apply (wf_two_ind wf_lt (fun x y => EQ x y -> EQ y x)).
  destruct x1, x2.
  repeat rewrite EQ_def. intros. repeat destruct H0.
  split. split.
  - intro x0. destruct (H2 x0). eauto with Wff.
  - intro x. destruct (H0 x). eauto with Wff.
  - revert H1. apply eq_bexpr_sym.
Qed.
#[export] Hint Resolve EQ_sym : Eeq.

Lemma EQ_trans : forall x y z, EQ x y -> EQ y z -> EQ x z.
Proof.
  apply (wf_three_ind wf_lt (fun x y z => EQ x y -> EQ y z -> EQ x z)).
  destruct x1, x2, x3. 
  repeat rewrite EQ_def. unfold AEQ in *. intros.
  repeat destruct H0. repeat destruct H1.
  split. split.
  - intro x. destruct (H0 x). destruct (H1 x0).
    eauto with Wff.
  - intro y. destruct (H5 y). destruct (H3 x).
    eauto with Wff.
  - apply (fun X => eq_bexpr_trans EQ_sym X H2 H4).
    intros. repeat destruct H6; destruct H7; repeat destruct H6; destruct H8; repeat destruct H6; apply (fun X => H _ _ _ X H9 H10); eauto with Wff.
Qed.
#[export] Hint Resolve EQ_trans : Eeq.

(** Register (SET, EQ) as a setoid: *)
Instance nfo_setoid : Equivalence EQ.
Proof.
  constructor. exact @EQ_refl. exact @EQ_sym. exact @EQ_trans.
Qed.

(** AEQ is an equivalence *)
Lemma AEQ_refl: forall {X} (f: X -> _), AEQ f f.
Proof. intros. unfold AEQ. eauto with Eeq. Qed.

Lemma AEQ_sym: forall {X Y} (f: X -> _) (g: Y -> _),
  AEQ f g -> AEQ g f.
Proof.
  unfold AEQ. intros. destruct H. split; intro z.
  destruct (H0 z). eauto with Eeq.
  destruct (H z). eauto with Eeq.
Qed.

Lemma AEQ_trans: forall {X Y Z} (f: X -> _) (g: Y -> _) (h: Z -> _),
  AEQ f g -> AEQ g h -> AEQ f h.
Proof.
  unfold AEQ. intros. destruct H, H0. split; intro z.
  destruct (H z).  destruct (H0 x). eauto with Eeq.
  destruct (H2 z). destruct (H1 x). eauto with Eeq.
Qed.

Notation BEQ := (eq_bexpr EQ).

(** The good unfolding lemma for EQ: *)
Lemma EQ_unfold {X' Y' f' g' e' X Y f g e}:
  EQ (S X Y f g e) (S X' Y' f' g' e')
    <-> AEQ f f' /\ BEQ (map g e) (map g' e').
Proof.
  rewrite (eq_bexpr_simpl nfo_setoid).
  rewrite EQ_def. apply iff_refl.
Qed.
