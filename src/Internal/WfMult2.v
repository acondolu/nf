
Require Import Coq.Lists.List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Coq.omega.Omega.
Require Import Coq.Sorting.Permutation.
From Coq.Wellfounded Require Import Inclusion Inverse_Image Transitive_Closure.
Add LoadPath "src".
From Internal Require Import Misc List WfMult.

Section WfMult2.

Variable A : Type.
Variable lt : A -> A -> Prop.
Variable wf_lt: well_founded lt.

Definition lltlp := (clos_trans _ (WfMult.ltlp lt)).
Definition wf_trans: well_founded lltlp.
Proof.
  apply wf_clos_trans. apply WfMult.wf_perm. apply wf_lt.
Qed.

(** Aux: comment *)
Lemma lltlp_concat_left: forall a b b',
  lltlp b b' -> lltlp (a ++ b) (a ++ b').
Proof.
  intros. revert a. induction H; intro a.
  - destruct H, H. apply t_step. exists (a ++ x0).
    split. apply (Permutation_app_head a). assumption.
    apply (ltl_concat_left _ _ a). assumption.
  - apply (t_trans _ _ _ (a ++ y)).
    apply IHclos_trans1. apply IHclos_trans2.
Qed.

Lemma lltlp_concat_right: forall b a a',
  lltlp a a' -> lltlp (a ++ b) (a' ++ b).
Proof.
  intros. revert b. induction H; intro b.
  - destruct H, H. apply t_step. exists (x0 ++ b).
    split. apply (Permutation_app_tail b). assumption.
    apply (ltl_concat_right _ _ b). assumption.
  - apply (t_trans _ _ _ (y ++ b)).
    apply IHclos_trans1. apply IHclos_trans2.
Qed.

Lemma lltlp_concat: forall a a' b b',
  lltlp a a' -> lltlp b b' -> lltlp (a ++ b) (a' ++ b').
Proof.
  intros.
  apply (t_trans _ _ _ (a ++ b')); fold lltlp.
  apply lltlp_concat_left. assumption.
  apply lltlp_concat_right. assumption.
Qed.

Lemma l_perm_lt_sx: forall {a a' b},
  Permutation a' a -> lltlp a b -> lltlp a' b.
Proof.
  intros. revert a' H. induction H0; intros.
  - apply t_step. destruct H, H. exists x0. split.
    transitivity x. auto. auto. auto.
  - apply (t_trans _ _ _ y). apply (IHclos_trans1 _ H).
    apply (IHclos_trans2 y). reflexivity. 
Qed.


(* other *)

Definition other: list A -> list A -> Type :=
fun l l' =>  prod (l' <> nil) (all' (fun a => some' (lt a) l') l).

Definition gather: forall l l' a',
  all' (fun a => some' (lt a) (a' :: l')) l -> list A.
  induction l; simpl; intros.
  - exact nil.
  - destruct X. pose proof s as s'. destruct s. refine (a :: _).
    apply (IHl _ _ a0).
    apply (IHl _ _ a0).
Defined.

Lemma gather_ok: forall {l l' a'},
  forall (p: all' (fun a => some' (lt a) (a' :: l')) l),
    all' (fun a => lt a a') (gather _ _ _ p).
Proof.
  intros. induction l.
  simpl. auto.
  destruct p, s. simpl.
  - split. auto. apply IHl.
  - apply IHl.
Qed.

Definition drop: forall l l' a',
  all' (fun a => some' (lt a) (a' :: l')) l -> list A.
  induction l; simpl; intros.
  - exact nil.
  - destruct X. pose proof s as s'. destruct s.
    apply (IHl _ _ a0).
    refine (a :: _).
    apply (IHl _ _ a0).
Defined.

Lemma drop_ok: forall {l l' a'},
  forall (p: all' (fun a => some' (lt a) (a' :: l')) l),
    all' (fun a => some' (lt a) l') (drop _ _ _ p).
Proof.
  intros. induction l.
  simpl. auto.
  destruct p, s. simpl.
  - apply IHl.
  - split. auto. apply IHl.
Qed.

Lemma gather_drop_okay: forall l l' a a0,
 Permutation l (gather l l' a a0 ++ drop l l' a a0).
Proof.
  intros. induction l; simpl.
  reflexivity. destruct a0. destruct s. simpl.
  specialize IHl with a0. apply perm_skip. auto.
  transitivity (a1 :: gather l l' a a0 ++ drop l l' a a0).
  apply perm_skip. auto. apply Permutation_middle.
Qed.

Theorem other_ok: forall l l', other l l' -> lltlp l l'.
Proof.
  unfold other. intros l l'. revert l. induction l'; intros; destruct X.
  - destruct (n (eq_refl)).
  - destruct l'.
  -- apply t_step. exists l. split. reflexivity.
    pose proof (C A lt O (a :: nil) l (Nat.lt_0_succ _)).
    simpl in H. simpl in a0. rewrite app_nil_r in H. apply H.
    clear n H. induction l; simpl. auto. destruct a0, s. split. assumption.
    apply IHl; auto. destruct f.
  -- pose proof (lltlp_concat (gather _ _ _ a0) (a::nil) (drop _ _ _ a0) (a1::l')).
    apply (fun X Y => l_perm_lt_sx (gather_drop_okay _ _ _ _) (H X Y)).
    --- apply t_step. exists (gather l (a1 :: l') a a0). split. reflexivity.
    cut (0 < length (a :: nil)). intro. pose proof (C A lt O (a::nil) (gather l (a1 :: l') a a0) H0). simpl in H1.
    rewrite app_nil_r in H1. apply H1.
    pose proof (gather_ok a0). apply (all_all _ _ X). simpl length. omega.
    --- simpl. apply IHl'. split. intro X. pose proof (@nil_cons _ a1 l'). auto.
      apply (drop_ok a0).
Qed.

Definition other' (a b: list A) : Prop := ☐ (other a b).
Theorem wf_other: well_founded other'.
Proof.
  apply (wf_incl _ _ lltlp).
  unfold inclusion. intros. destruct H. apply other_ok. auto.
  apply wf_clos_trans.
  apply WfMult.wf_perm.
  apply wf_lt.
Qed.

Lemma other'_unfold : forall l l',
other' l l' <-> (l' <> nil) /\ (all _ (fun a => some (lt a) l') l).
Proof.
  intros. unfold other'. split; intros.
  - destruct H, X. split; auto. apply all_all. auto.
    refine (all'_mono _ _ _ _ a). intro. apply some_some.
  - destruct H.
    unfold other.
    pose proof (fun Q K => all_mono _ Q K l H0).
    pose proof (H1 _ (fun x => some_some_2 (lt x) l')).
    psplit. passumption.
    apply all_PROP. auto.
Qed.

Lemma other'_unfold_2 : forall l l',
other' l l' <-> (l' <> nil)
  /\ forall x, In x l -> exists y, In y l' /\ lt x y.
Proof.
  intros.
  rewrite other'_unfold.
  rewrite<- all_In.
  apply and_morph. apply iff_refl.
  apply all_ext. intros. apply some_In.
Qed.

End WfMult2.

Arguments other' : default implicits.