
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

(* decr' *)

Definition decr' l l': Type :=
  prod (l' <> nil) (allT (fun a => someT (lt a) l') l).

Definition gather: forall l l' a',
  allT (fun a => someT (lt a) (a' :: l')) l -> list A.
  induction l; simpl; intros.
  - exact nil.
  - destruct X. pose proof s as s'. destruct s. refine (a :: _).
    apply (IHl _ _ a0).
    apply (IHl _ _ a0).
Defined.

Lemma gather_ok: forall {l l' a'},
  forall (p: allT (fun a => someT (lt a) (a' :: l')) l),
    allT (fun a => lt a a') (gather _ _ _ p).
Proof.
  intros. induction l.
  simpl. auto.
  destruct p, s. simpl.
  - split. auto. apply IHl.
  - apply IHl.
Qed.

Definition drop: forall l l' a',
  allT (fun a => someT (lt a) (a' :: l')) l -> list A.
  induction l; simpl; intros.
  - exact nil.
  - destruct X. pose proof s as s'. destruct s.
    apply (IHl _ _ a0).
    refine (a :: _).
    apply (IHl _ _ a0).
Defined.

Lemma drop_ok: forall {l l' a'},
  forall (p: allT (fun a => someT (lt a) (a' :: l')) l),
    allT (fun a => someT (lt a) l') (drop _ _ _ p).
Proof.
  intros. induction l.
  simpl. auto.
  destruct p, s. simpl.
  - apply IHl.
  - split. auto. apply IHl.
Qed.

Lemma gather_drop_ok: forall l l' a a0,
 Permutation l (gather l l' a a0 ++ drop l l' a a0).
Proof.
  intros. induction l; simpl.
  reflexivity. destruct a0. destruct s. simpl.
  specialize IHl with a0. apply perm_skip. auto.
  transitivity (a1 :: gather l l' a a0 ++ drop l l' a a0).
  apply perm_skip. auto. apply Permutation_middle.
Qed.

Theorem decr'_ok: forall l l', decr' l l' -> lltlp lt l l'.
Proof.
  unfold decr'. intros l l'. revert l. induction l'; intros; destruct X.
  - destruct (n (eq_refl)).
  - destruct l'.
  -- apply t_step. exists l. split. reflexivity.
    pose proof (C A lt O (a :: nil) l (Nat.lt_0_succ _)).
    simpl in H. simpl in a0. rewrite app_nil_r in H. apply H.
    clear n H. induction l; simpl. auto. destruct a0, s. split. assumption.
    apply IHl; auto. destruct f.
  -- pose proof (lltlp_concat _ lt (gather _ _ _ a0) (a::nil) (drop _ _ _ a0) (a1::l')).
    apply (fun X Y => l_perm_lt_sx _ lt (gather_drop_ok _ _ _ _) (H X Y)).
    --- apply t_step. exists (gather l (a1 :: l') a a0). split. reflexivity.
    cut (0 < length (a :: nil)). intro. pose proof (C A lt O (a::nil) (gather l (a1 :: l') a a0) H0). simpl in H1.
    rewrite app_nil_r in H1. apply H1.
    pose proof (gather_ok a0). apply (allT_all _ _ X). simpl length. omega.
    --- simpl. apply IHl'. split. intro X. pose proof (@nil_cons _ a1 l'). auto.
      apply (drop_ok a0).
Qed.

Definition decr (a b: list A) : Prop := ☐ (decr' a b).

Theorem wf_decr: well_founded decr.
Proof.
  apply (wf_incl _ _ (lltlp lt)).
  unfold inclusion. intros. destruct H. apply decr'_ok. auto.
  apply WfMult.wf_trans.
  apply wf_lt.
Qed.

Lemma decr_unfold : forall l l',
  decr l l'
    <-> l' <> nil /\ all _ (fun a => some (lt a) l') l.
Proof.
  intros. unfold decr. split; intros.
  - destruct H, X. split; auto. apply allT_all. auto.
    refine (allT_mono _ _ _ _ a). intro. apply someT_some.
  - destruct H.
    unfold decr'.
    pose proof (fun Q K => all_mono _ Q K l H0).
    pose proof (H1 _ (fun x => some_someT (lt x) l')).
    psplit. passumption.
    apply all_PROP. auto.
Qed.

Lemma decr_unfold_2 : forall l l',
  decr l l'
    <-> l' <> nil /\ forall x, In x l -> exists y, In y l' /\ lt x y.
Proof.
  intros.
  rewrite decr_unfold.
  rewrite<- all_In.
  apply and_morph. apply iff_refl.
  apply all_ext. intros. apply some_In.
Qed.

End WfMult2.

Arguments decr : default implicits.