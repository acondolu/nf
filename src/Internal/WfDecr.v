
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
From Coq.Wellfounded Require Import Inclusion Inverse_Image Transitive_Closure.
Add LoadPath "src/Internal" as Internal.
From Internal Require Import Misc List WfMult.

Section WfDecr.

Variable A : Type.
Variable lt : A -> A -> Prop.
Variable wf_lt: well_founded lt.

(** We define the [decr] binary relation between lists, such that
    [decr l l'] iff every element of [l] is smaller than some
    element of [l'].
*)
Definition decr' l l': Type :=
  prod (l' <> nil) (allT (fun a => someT (lt a) l') l).

Local Infix "<L" := decr' (at level 10).

(** [gather l l' a p] gathers all the elements of [l] that
    are smaller than the first element of [l'].
*)
Definition gather: forall l l' a',
  allT (fun a => someT (lt a) (a' :: l')) l -> list A.
  induction l; simpl; intros.
  - exact nil.
  - destruct X. pose proof s as s'. destruct s. refine (a :: _).
    apply (IHl _ _ a0).
    apply (IHl _ _ a0).
Defined.

Fixpoint gatherYYY {xs ys} : xs <L ys -> list A :=
  match xs, ys with
  | nil, _ => fun _ => nil
  | _, nil => fun _ => nil (* derive contradiction here *)
  | x::_, y::_ => fun d =>
    let (ne, d') := d in
    let (xys, xsys) := d' in
    match xys with
    | inl _ => x :: gatherYYY (ne, xsys)
    | inr _ => gatherYYY (ne, xsys)
    end
  end.

(** Correctness of [gather]: *)
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

Lemma gather_okYYY: forall {xs y ys},
  forall d: xs <L (y :: ys),
    allT (fun x => lt x y) (gatherYYY d).
Proof.
  intros. induction xs.
  simpl. auto. destruct d.
  destruct a0, s; simpl. split. auto. apply IHxs.
  apply IHxs.
Qed.

(** [drop l l' a p] drops all the elements from [l] that
    are smaller than the first element of [l'].
    (It is the dual of [gather]).
*)
Definition drop: forall l l' a',
  allT (fun a => someT (lt a) (a' :: l')) l -> list A.
  induction l; simpl; intros.
  - exact nil.
  - destruct X. pose proof s as s'. destruct s.
    apply (IHl _ _ a0).
    refine (a :: _).
    apply (IHl _ _ a0).
Defined.

Fixpoint dropYYY {xs ys} : xs <L ys -> list A :=
  match xs, ys with
  | nil, _ => fun _ => nil
  | _, nil => fun _ => nil (* derive contradiction here *)
  | x::_, y::_ => fun d =>
    let (ne, d') := d in
    let (xys, xsys) := d' in
    match xys with
    | inl _ => dropYYY (ne, xsys)
    | inr _ => x :: dropYYY (ne, xsys)
    end
  end.

(** Correctness sof [drop]: *)
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

Lemma drop_okYYY: forall {xs y ys},
  forall d: xs <L (y :: ys),
    allT (fun x => someT (lt x) ys) (dropYYY d).
Proof.
  intros. induction xs.
  simpl. auto. destruct d.
  destruct a0, s; simpl.
  - apply IHxs.
  - split. auto. apply IHxs.
Qed.

(** We use [gather] and [drop] to permutate a list [l],
    moving all the gathered elements to the head of the list:
*)
Lemma gather_drop_ok: forall l l' a a0,
 Permutation l (gather l l' a a0 ++ drop l l' a a0).
Proof.
  intros. induction l; simpl.
  reflexivity. destruct a0. destruct s. simpl.
  specialize IHl with a0. apply perm_skip. auto.
  transitivity (a1 :: gather l l' a a0 ++ drop l l' a a0).
  apply perm_skip. auto. apply Permutation_middle.
Qed.

Lemma gather_drop_okYYY: forall {xs y ys} {d: xs <L (y :: ys)},
 Permutation xs (gatherYYY d ++ dropYYY d).
Proof.
  intros. induction xs. auto. destruct d, a0, s; simpl.
  - apply perm_skip. apply IHxs.
  - transitivity (a :: gatherYYY (n, a0) ++ dropYYY (n, a0)).
  -- apply perm_skip. apply IHxs.
  -- apply Permutation_middle.
Qed.

(** An important result. We show that [decr] is contained in the
    transitive closure of the permutation order between lists
    defined in [Internal.WfMult].

    To prove it, we proceed by induction on [l'], using [gather_drop_ok]
    and concluding by i.h.
*)
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
    pose proof (gather_ok a0). apply (allT_all _ _ X). simpl length. lia.
    --- simpl. apply IHl'. split. intro X. pose proof (@nil_cons _ a1 l'). auto.
      apply (drop_ok a0).
Qed.

Definition decr (a b: list A) : Prop := ☐ (decr' a b).

(** As a consequence, we easily obtain well-foundedness
    of [decr] by the inclusion theorem.
*)
Theorem wf_decr: well_founded decr.
Proof.
  apply (wf_incl _ _ (lltlp lt)).
  unfold inclusion. intros. destruct H. apply decr'_ok. auto.
  apply WfMult.wf_trans.
  apply wf_lt.
Qed.

Lemma decr_unfold : forall l l',
  decr l l'
    <-> l' <> nil /\ all (fun a => some (lt a) l') l.
Proof.
  intros. unfold decr. split; intros.
  - destruct H, X. split; auto. apply allT_all. auto.
    refine (allT_mono _ _ _ _ a). intro. apply someT_some.
  - destruct H.
    unfold decr'.
    pose proof (fun Q K => all_mono _ Q K l H0).
    pose proof (H1 _ (fun x => some_someT (lt x) l')).
    psplit. passumption.
    apply all_allT. auto.
Qed.

(** A nicer unfolding lemma for [decr], using [In]
    instead of [all] and [some]. We won't use this version, thought.
*)
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

End WfDecr.

Arguments decr : default implicits.
