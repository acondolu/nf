
Require Import Coq.Lists.List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Coq.omega.Omega.
Require Import Coq.Sorting.Permutation.
From Coq.Wellfounded Require Import Inclusion Inverse_Image Transitive_Closure.
Add LoadPath "src".
From Internal Require Import WfMult.

Inductive PROP X : Prop :=
  PP : X -> PROP X.
Notation "☐ A" := (PROP A) (at level 85).

Lemma PROP_prod {X Y}: ☐ X -> ☐ Y -> ☐ prod X Y.
Proof.
  intros. destruct H, H0.
  refine (PP _ _). auto.
Qed.

Ltac psplit := apply PROP_prod.
Ltac passumption := refine (PP _ _); assumption.
Ltac pauto := refine (PP _ _); auto.

Section WfMult2.

Variable A : Type.
Variable lt : A -> A -> Prop.
Variable wf_lt: well_founded lt.

Definition lltlp := (clos_trans _ (WfMult.ltlp lt)).
Definition wf_trans: well_founded lltlp.
Proof.
  apply wf_clos_trans. apply WfMult.wf_perm. apply wf_lt.
Qed.

Fixpoint all P (l: list A): Prop := match l with
| nil => True
| cons b bs => P b /\ all P bs
end.

Fixpoint all' P (l: list A): Type := match l with
| nil => True : Type
| cons b bs => prod (P b) (all' P bs)
end.

Lemma all_PROP: forall {P l},
  all (fun x => ☐ P x) l
  -> ☐ all' (fun x => P x) l.
Proof.
  intros. induction l. simpl. pauto.
  destruct H. psplit. assumption.
  apply IHl. assumption.
Qed.

Fixpoint some P (l: list A) := match l with
| nil => False
| cons b bs => P b \/ some P bs
end.

Fixpoint some' P (l: list A) : Type := match l with
| nil => False : Type
| cons b bs => sum (P b) (some' P bs)
end.

Lemma all_all: forall (P: A -> Prop) l, all' P l -> all P l.
Proof.
  induction l. auto. simpl. intros. destruct X. tauto.
Qed.
Lemma all_all_2: forall (P: A -> Prop) l, all P l -> all' P l.
Proof.
  induction l. auto. simpl. intros. destruct H. tauto.
Qed.
Lemma some_some: forall (P: A -> Prop) l, some' P l -> some P l.
Proof.
  induction l. auto. simpl. intros. destruct X; tauto.
Qed.
Lemma some_some_2: forall (P: A -> Prop) l, some P l -> ☐ (some' P l).
Proof.
  induction l; intro. refine (PP _ _). auto.
  destruct H. refine (PP _ _). left. auto.
  destruct (IHl H). refine (PP _ _). right. auto.
Qed.

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

Conjecture lltlp_concat: forall a a' b b', lltlp a a' -> lltlp b b' -> lltlp (a ++ b) (a' ++ b').

Conjecture XXX: forall l l' a a0,
 Permutation (gather l l' a a0 ++ drop l l' a a0) l.

Conjecture l_perm_lt_sx: forall {a a' b}, Permutation a a' -> lltlp a b -> lltlp a' b.



Theorem other_ok: forall l l', other l l' -> lltlp l l'.
Proof.
  unfold other. intros l l'. revert l. induction l'.
  - destruct l; simpl; intros. destruct H. admit. tauto.
  - intros. destruct X.
    (* destruct l'.
    apply t_step. exists (gather _ _ _ a0). split. reflexivity.
    cut (0 < length (a :: nil)). intro. pose proof (C A lt O (a::nil) (gather l l' a a0) H0). simpl in H1.
    rewrite app_nil_r in H1. apply H1.
    pose proof (gather_ok a0). apply (all_all _ _ X). simpl length. omega. *)


    pose proof (lltlp_concat (gather _ _ _ a0) (a::nil) (drop _ _ _ a0) l').
    apply (fun X Y => l_perm_lt_sx (XXX _ _ _ _) (H X Y)).
    -- apply t_step. exists (gather l l' a a0). split. reflexivity.
    cut (0 < length (a :: nil)). intro. pose proof (C A lt O (a::nil) (gather l l' a a0) H0). simpl in H1.
    rewrite app_nil_r in H1. apply H1.
    pose proof (gather_ok a0). apply (all_all _ _ X). simpl length. omega.
    -- simpl. apply IHl'. split. admit.
      apply (drop_ok a0).
Admitted.

Definition other' (a b: list A) : Prop := ☐ (other a b).
Theorem wf_other: well_founded other'.
Proof.
  apply (wf_incl _ _ lltlp).
  unfold inclusion. intros. destruct H. apply other_ok. auto.
  apply wf_clos_trans.
  apply WfMult.wf_perm.
  apply wf_lt.
Qed.

Conjecture all'_mono: forall (P: A -> Type) (Q: A -> Type),
  (forall x, P x -> Q x) ->
  forall l, all' P l -> all' Q l.

Conjecture all_mono: forall (P: A -> Prop) (Q: A -> Prop),
  (forall x, P x -> Q x) ->
  forall l, all P l -> all Q l.

Lemma other'_unfold : forall l l',
other' l l' <-> (l' <> nil) /\ (all (fun a => some (lt a) l') l).
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

End WfMult2.

Arguments other' : default implicits.