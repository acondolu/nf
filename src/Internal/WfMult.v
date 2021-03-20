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

(** The extension of [<<] to lists. [l <<< l'] holds iff there exists an element [x]
    in [l] such that [l'] is obtained from [l] by replacing that element with a
    (possibly empty) list whose elements are all strictly smaller than [x].
*)
Inductive ltl : list A -> list A -> Prop :=
  | ltl_base : forall {x xs ys},
      all (fun y => y << x) ys -> ltl (ys ++ xs) (x :: xs)
  | ltl_skip : forall {xs ys} x,
      ltl xs ys -> ltl (x :: xs) (x :: ys)
.
Local Infix "<<<" := ltl (at level 80).

(** Comment: *)

Lemma ltl_cons: forall x xs ys,
  xs <<< ys -> (x :: xs) <<< (x :: ys).
Proof.
  intros. destruct H.
  - apply ltl_skip. apply ltl_base. auto.
  - apply ltl_skip. apply ltl_skip. auto.
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
  dependent induction H; intro zs.
  - rewrite<- app_assoc. rewrite<- app_comm_cons.
    apply ltl_base. assumption.
  - rewrite<- app_comm_cons. rewrite<- app_comm_cons.
    apply ltl_skip. apply IHltl.
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
  intros. apply Acc_intro. intros. dependent destruction H2.
  - induction ys.
  -- assumption.
  -- rewrite<- app_comm_cons. destruct H2. apply H.
     assumption. auto.
  - apply H1. assumption.
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
  Permutation b b' -> a <<< b -> a p<<< b'.
Proof.
  intros. revert a H0.
  dependent induction H; intros; unfold ltlp; dependent destruction H0.
  - exists (ys ++ l'). split.
  -- apply Permutation_app_head. assumption.
  -- apply ltl_base. assumption.
  - destruct (IHPermutation _ H0) as [xs' [p3' H3']]. exists (x :: xs').
     split. apply perm_skip. assumption. apply ltl_skip. assumption.
  - exists (x :: ys ++ l). split.
  -- symmetry. apply Permutation_middle.
  -- apply ltl_skip. apply ltl_base. assumption.
  - dependent destruction H0.
  -- exists (ys ++ y :: l). split.
  --- apply Permutation_middle.
  --- apply ltl_base. assumption.
  -- exists (x :: y :: xs). split.
  --- apply perm_swap.
  --- apply ltl_skip. apply ltl_skip. assumption.
  (* perm_trans *)
  - rewrite (Permutation_nil (Permutation_sym H)) in H1.
    dependent destruction H1.
  - destruct (IHPermutation1 _ H1), H2.
    destruct (IHPermutation2 _ H3), H4.
    exists x1. split. transitivity x0; assumption. assumption.
  - destruct (IHPermutation1 _ H1), H0.
    destruct (IHPermutation2 _ H2), H3.
    exists x1. split. transitivity x0; assumption. assumption.
  - destruct (IHPermutation1 _ H1), H0.
    destruct (IHPermutation2 _ H2), H3.
    exists x0. split. transitivity x; assumption. assumption.
Qed.

Lemma perm_Acc: forall xs ys,
  Permutation ys xs -> Acc ltlp xs -> Acc ltlp ys.
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
    apply (perm_Acc _ _ H2). auto.
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
