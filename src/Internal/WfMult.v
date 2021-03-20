(** * Internal.WfMult : Well-founded multiset extension *)
(** This module defines the multiset extension
    of a well-founded binary relation.
    
    We represent multisets simply as lists. Then we use
    permutations to ignore the position of elements
    in a list.
*)
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Lt.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
Require Import Relation_Definitions.
Require Import Relation_Operators.
From Coq.Wellfounded Require Import Inclusion Inverse_Image Transitive_Closure.
Add LoadPath "src/Internal" as Internal.
From Internal Require Import List.

Section WfMult.

(** We assume a well-founded binary relation [<<] over A: *)
Variable A : Type.
Variable lt : A -> A -> Prop.
Local Infix "<<" := lt (at level 80).
Variable wf_lt: well_founded lt.

(** Replace the element of a list at a certain position by concatenating
    another list in its place:
*)
Definition replace : forall {xs: list A} {i: nat},
  i < length xs -> list A -> list A.
Proof.
  induction xs; intros i H ys.
  - exact ys.
  - destruct i.
  -- exact (ys ++ xs).
  -- simpl in H. refine (a :: _).
     exact (IHxs _ (lt_S_n _ _ H) ys).
Defined.

Local Lemma eq_cons: forall {A} (a: A) xs ys, xs = ys -> a :: xs = a :: ys.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma replace_irr: forall {xs i ys} (p p': i < length xs),
  replace p ys = replace p' ys.
Proof.
  induction xs; intros i ys p p'.
  - simpl in *. lia.
  - destruct i.
  -- reflexivity.
  -- simpl in p, p'. simpl. apply eq_cons. apply IHxs.
Qed.

(** Get an element of the list by its index: *)
Definition get: forall {xs: list A} {i: nat}, i < length xs -> A.
Proof.
  induction xs; intros i H.
  - simpl in H. lia.
  - destruct i.
  -- exact a.
  -- simpl in H.
      exact (IHxs _ (lt_S_n _ _ H)).
Defined.

Lemma get_irr: forall {xs i} (p p': i < length xs),
  get p = get p'.
Proof.
  induction xs; intros i p p'.
  - simpl in *. lia.
  - destruct i.
  -- reflexivity.
  -- simpl in p, p'. simpl. apply IHxs.
Qed.

(** The extension of [<<] to lists. [l <<< l'] holds iff there exists an element [x]
    in [l] such that [l'] is obtained from [l] by replacing that element with a
    (possibly empty) list whose elements are all strictly smaller than [x].
*)
Inductive ltl : list A -> list A -> Prop :=
  | C : forall i (xs ys: list A) (p: i < length xs),
         all (fun x => x << get p) ys
          -> ltl (replace p ys) xs.
Local Infix "<<<" := ltl (at level 80).

(** Comment: *)

Lemma ltl_cons: forall x xs ys,
  xs <<< ys -> (x :: xs) <<< (x :: ys).
Proof.
  intros. destruct H. 
  pose proof (C (S i) (x :: xs) ys (lt_n_S _ _ p)).
  simpl in H0.
  rewrite (get_irr _ p) in H0.
  rewrite (replace_irr _ p) in H0.
  tauto.
Qed.

Lemma ltl_concat_left: forall zs xs ys,
  xs <<< ys -> (zs ++ xs) <<< (zs ++ ys).
Proof.
  induction zs; simpl. auto.
  intros. apply ltl_cons. auto.
Qed.

Lemma ltl_concat_right: forall zs xs ys,
  xs <<< ys -> (xs ++ zs) <<< (ys ++ zs).
Proof.
  intros. revert zs.
  dependent destruction H. revert i p H.
  induction xs; simpl; intros. lia.
  destruct i.
  - pose proof (C O (a :: xs ++ zs) ys).
  cut (0 < length (a :: xs ++ zs)). intro.
  specialize H0 with H1. simpl.
  rewrite<- app_assoc. apply H0. assumption.
  simpl. lia.
  - simpl replace. fold (@length A). apply ltl_cons. apply IHxs. 
  assumption.
Qed.

(** A useful inversion lemma:  *)
Lemma ltl_cases: forall {xs y ys}, 
  xs <<< y :: ys
    -> (exists zs, zs <<< ys /\ xs = y :: zs)
      \/ exists zs, xs = zs ++ ys /\ all (fun z => z << y) zs.
Proof.
  intros. dependent destruction H.
  induction i.
  - right. exists ys0. simpl. split; auto.
  - left. exists (replace (lt_S_n _ _ p) ys0). split.
    refine (C _ ys ys0 (lt_S_n _ _ p) H).
    simpl. apply (replace_irr p).
Qed.

(** We follow the proof by Tobias Nipkov in "An inductive Proof of the 
    Wellfoundedness of the Multiset Order". We adapt the lemmas
    in that document to the case of lists instead of multisets.

    Note: the definition of [<<<] above is justified by our need to keep
    the proofs nicely inductive on the structure of lists. We are forced to 
    concatenate the new list of smaller elements exactly at the position
    where the removed element was.
*)

(** Lemma 2.1: *)
Lemma l2p1: forall {a M0},
  (forall b, b << a -> forall M, Acc ltl M -> Acc ltl (b :: M))
    -> Acc ltl M0
      -> (forall M, M <<< M0 -> Acc ltl (a :: M))
        -> Acc ltl (a :: M0).
Proof.
  intros. apply Acc_intro. intros. destruct (ltl_cases H2).
  - destruct H3, H3. rewrite H4 in *. clear H4 y. apply (H1 x H3).
  - destruct H3, H3. rewrite H3 in *; clear H3 y. induction x; simpl; intros.
  -- assumption.
  -- destruct H4. apply H. assumption. apply IHx; try assumption.
      apply (C O (a :: M0) x (Nat.lt_0_succ _) H4).
Qed.

(** Lemma 2.2: *)
Lemma l2p2: forall a,
  (forall b, b << a -> forall M, Acc ltl M -> Acc ltl (b :: M))
    -> forall M, Acc ltl M ->  Acc ltl (a :: M).
Proof.
  intros.
    refine (@Fix_F (list A) ltl (fun M0 => Acc ltl M0 -> Acc ltl (a::M0)) _ M H0 H0). intros M0 H1 H2.
    pose H2 as H2'. destruct H2'. pose proof (fun y h => H1 y h (H3 y h)).
    revert H H2 H4. clear. exact l2p1.
Qed.

(** Lemma 2.3: *)
Lemma l2p3: forall {a} M, Acc ltl M -> Acc ltl (a :: M).
Proof.
  apply (well_founded_ind wf_lt (fun a => forall M, Acc ltl M -> Acc ltl (a :: M))).
  exact l2p2. 
Qed.

Theorem wf_ltl: well_founded ltl.
Proof.
  unfold well_founded. intro l. induction l.
  - apply Acc_intro. intros. dependent destruction H.
    simpl length in p. lia.
  - apply (l2p3 l IHl).
Qed.

(** * Unordered
    To consider lists as multisets, we now use permutations so to make
    our order relation ignore the position of elements in a list.

    We use Coq's Permutation library
    (see https://coq.github.io/doc/master/stdlib/Coq.Sorting.Permutation.html).
*)

Definition ltlp l l' :=
  exists l'', Permutation l l'' /\ l'' <<< l'.
Local Infix "p<<<" := ltlp (at level 80).

Lemma perm_lt_dx: forall {a b b'},
  Permutation b b' -> a <<< b' -> a p<<< b.
Proof.
  intros. revert a H0. dependent induction H; intros; unfold ltlp.
  - dependent destruction H0. destruct (Nat.nlt_0_r _ p).
  - destruct (ltl_cases H0); destruct H1, H1.
  -- rewrite H2 in *. clear a H2.
     destruct (IHPermutation _ H1), H2.
     exists (x :: x1). split.
  --- apply perm_skip. assumption.
  --- apply ltl_cons. assumption.
  -- rewrite H1 in *. clear a H1. exists (x0 ++ l). split.
     apply Permutation_app_head. apply Permutation_sym. assumption.
     refine (C O (x::l) x0 _ H2). apply Nat.lt_0_succ.
  - destruct (ltl_cases H0); destruct H, H.
  -- rewrite H1 in *. clear a H1. destruct (ltl_cases H); destruct H1, H1.
  --- rewrite H2 in *. clear x0 H2. exists (y :: x :: x1).
      split. apply perm_swap.
      apply ltl_cons. apply ltl_cons. assumption.
  --- rewrite H1 in *. clear x0 H1. exists (x1 ++ x :: l). split.
      apply Permutation_cons_app. reflexivity.
      refine (C O (y :: x :: l) x1 _ _). apply H2.
  -- rewrite H in *. clear a H. exists (y :: x0 ++ l). split.
     symmetry. apply Permutation_cons_app. reflexivity.
     refine (C 1 (y :: x :: l) x0 _ _). apply H1.
  - destruct (IHPermutation2 _ H1), H2. destruct (IHPermutation1 _ H3), H4.
    exists x0. split. transitivity x; auto. auto.
    Unshelve. apply Nat.lt_0_succ. simpl length. lia.
Qed.

Lemma perm_Acc: forall xs ys,
  Permutation xs ys -> Acc ltlp xs -> Acc ltlp ys.
Proof.
  intros xs ys H H0. induction H; auto;
  apply Acc_intro; intros; apply H0.
  - destruct H1, H1.
    destruct (perm_lt_dx (perm_skip x H) H2). destruct H3.
    exists x1. split; auto. transitivity x0; auto.
  - destruct H, H.
    destruct (perm_lt_dx (perm_swap x y l) H1). destruct H2.
    exists x1. split; auto. transitivity x0; auto.
Qed.

Theorem wf_perm : well_founded ltlp.
Proof.
    intro xs. induction (wf_ltl xs) as [xs H H1].
    apply Acc_intro. intros ys H2.
    destruct H2 as [zs [H2 H3]].
    apply (perm_Acc _ _ (Permutation_sym H2)). auto.
Qed.

(* lltlp *)

Definition lltlp := clos_trans _ ltlp.
Definition wf_trans: well_founded lltlp.
Proof.
  apply wf_clos_trans. apply wf_perm.
Qed.

(** Aux: comment *)
Lemma lltlp_concat_left: forall zs xs ys,
  lltlp xs ys -> lltlp (zs ++ xs) (zs ++ ys).
Proof.
  intros. revert zs. induction H; intro zs.
  - destruct H, H. apply t_step. exists (zs ++ x0).
    split. apply (Permutation_app_head zs). assumption.
    apply (ltl_concat_left zs). assumption.
  - apply (t_trans _ _ _ (zs ++ y)).
    apply IHclos_trans1. apply IHclos_trans2.
Qed.

Lemma lltlp_concat_right: forall zs xs ys,
  lltlp xs ys -> lltlp (xs ++ zs) (ys ++ zs).
Proof.
  intros. revert zs. induction H; intro zs.
  - destruct H, H. apply t_step. exists (x0 ++ zs).
    split. apply (Permutation_app_tail zs). assumption.
    apply (ltl_concat_right zs). assumption.
  - apply (t_trans _ _ _ (y ++ zs)).
    apply IHclos_trans1. apply IHclos_trans2.
Qed.

Lemma lltlp_concat: forall xs xs' ys ys',
  lltlp xs xs' -> lltlp ys ys' -> lltlp (xs ++ ys) (xs' ++ ys').
Proof.
  intros.
  apply (t_trans _ _ _ (xs ++ ys')); fold lltlp.
  apply lltlp_concat_left. assumption.
  apply lltlp_concat_right. assumption.
Qed.

Lemma l_perm_lt_sx: forall {xs xs' ys},
  Permutation xs' xs -> lltlp xs ys -> lltlp xs' ys.
Proof.
  intros. revert xs' H. induction H0; intros.
  - apply t_step. destruct H, H. exists x0. split.
    transitivity x. auto. auto. auto.
  - apply (t_trans _ _ _ y). apply (IHclos_trans1 _ H).
    apply (IHclos_trans2 y). reflexivity. 
Qed.

End WfMult.

Arguments lltlp : default implicits.
Arguments wf_trans : default implicits.
