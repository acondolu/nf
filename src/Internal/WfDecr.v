
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

(** We define [decr'] as a binary relation between lists, such that
    [decr xs ys] iff every element of [xs] is smaller than some
    element of [ys].
*)
Definition decr' xs ys: Type :=
  prod (ys <> nil) (allT (fun a => someT (lt a) ys) xs).

Local Infix "<L" := decr' (at level 10).

(** [gather] gathers all the elements of [xs] that
    are smaller than the first element of [ys].
*)
Fixpoint gather {xs ys} : xs <L ys -> list A :=
  match xs, ys with
  | nil, _ => fun _ => nil
  | _::_, nil => fun d => match d with (ne, _) => False_rect _ (ne eq_refl) end
  | x::_, y::_ => fun d =>
    match d with
    | (ne, (xys, xsys)) =>
      match xys with
      | inl _ => x :: gather (ne, xsys)
      | inr _ => gather (ne, xsys)
      end
    end
  end.

(** Correctness of [gather]: *)
Lemma gather_ok: forall {xs y ys},
  forall d: xs <L (y :: ys),
    allT (fun x => lt x y) (gather d).
Proof.
  intros. induction xs.
  simpl. auto. destruct d.
  destruct a0, s; simpl. split. auto. apply IHxs.
  apply IHxs.
Qed.

(** [drop] drops all the elements from [xs] that
    are smaller than the first element of [ys].
    (It is the dual of [gather]).
*)
Fixpoint drop {xs ys} : xs <L ys -> list A :=
  match xs, ys with
  | nil, _ => fun _ => nil
  | _::_, nil => fun d => match d with (ne, _) => False_rect _ (ne eq_refl) end
  | x::_, y::_ => fun d => match d with
  | (ne, (xys, xsys)) =>
      match xys with
      | inl _ => drop (ne, xsys)
      | inr _ => x :: drop (ne, xsys)
      end
  end
end.

(** Correctness of [drop]: *)
Lemma drop_ok: forall {xs y ys},
  forall d: xs <L (y :: ys),
    allT (fun x => someT (lt x) ys) (drop d).
Proof.
  intros. induction xs.
  simpl. auto. destruct d.
  destruct a0, s; simpl.
  - apply IHxs.
  - split. auto. apply IHxs.
Qed.

(** We use [gather] and [drop] to permutate a list [xs],
    moving all the gathered elements to the head of the list:
*)
Lemma gather_drop_ok: forall {xs y ys} (d: xs <L (y :: ys)),
 Permutation xs (gather d ++ drop d).
Proof.
  intros. induction xs. auto. destruct d, a0, s; simpl.
  - apply perm_skip. apply IHxs.
  - transitivity (a :: gather (n, a0) ++ drop (n, a0)).
  -- apply perm_skip. apply IHxs.
  -- apply Permutation_middle.
Qed.

(** An important result. We show that [decr] is contained in the
    transitive closure of the permutation order between lists
    defined in [Internal.WfMult].

    To prove it, we proceed by induction on [l'], using [gather_drop_ok]
    and concluding by i.h.
*)
Theorem decr'_ok: forall l l', l <L l' -> lltlp lt l l'.
Proof.
  unfold decr'. intros l l'. revert l. induction l'; intros; destruct X.
  - destruct (n (eq_refl)).
  - destruct l'.
  -- apply t_step. exists l. split. reflexivity.
     pose proof (@ltl_base _ lt a nil l).
     rewrite app_nil_r in H. apply H.
     clear n H. induction l; simpl. auto. destruct a0, s. split. assumption.
    apply IHl; auto. destruct s.
  -- pose proof (lltlp_concat _ lt (gather (n, a0)) (a::nil) (drop (n, a0)) (a1::l')).
    apply (fun X Y => l_perm_lt_sx _ lt (gather_drop_ok _) (H X Y)).
    --- apply t_step. exists (gather (n, a0)). split. reflexivity.
    cut (0 < length (a :: nil)). intro. 
    pose proof (@ltl_base _ lt a nil (gather (n, a0))).
    rewrite app_nil_r in H1. apply H1.
    pose proof (gather_ok (n, a0)). apply (allT_all _ _ X). simpl length. lia.
    --- simpl. apply IHl'. split. intro X. pose proof (@nil_cons _ a1 l'). auto.
      apply (drop_ok (n, a0)).
Qed.

Definition decr (a b: list A) : Prop := ☐ (a <L b).

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
