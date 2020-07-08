(** * Internal.WfMult : Well-founded multiset extension *)
(** This module defines the multiset extension
    of a well-founded binary relation.
    
    We represent multisets simply as lists. Then we use
    permutations so to ignore the position of elements in 
    a list.
*)
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.omega.Omega.
Require Import Coq.Sorting.Permutation.
Require Import Relation_Definitions.
Require Import Relation_Operators.
From Coq.Wellfounded Require Import Inclusion Inverse_Image Transitive_Closure.

Section WfMult.

(** We assume a well-founded relation [<<] over A: *)
Variable A : Type.
Variable lt : A -> A -> Prop.
Local Infix "<<" := lt (at level 80).
Variable wf_lt: well_founded lt.

(** Replace the element of a list at a certain position by concatenating
    another list in its place:
*)
Definition replace : forall {i: nat} {l: list A},
  i < length l -> list A -> list A.
Proof.
  induction i; destruct l.
  - simpl. omega.
  - intros. exact (X ++ l).
  - simpl. omega.
  - intros. refine (a :: IHi l (lt_S_n _ _ H) X).
Defined.

Lemma replace_cons: forall {i x l l'} (p: S i < length (x::l)) (p': i < length l),
  replace p l' = x :: replace p' l'.
Proof.
  induction i; intros; destruct l; simpl length in *.
  - omega.
  - reflexivity.
  - omega.
  - simpl. setoid_rewrite (IHi a l l'). apply eq_refl.
  Grab Existential Variables. apply (lt_S_n _ _ p').
Qed.

(** Get an element of the list by its index: *)
Definition get : forall {i: nat} {l: list A}, i < length l -> A.
Proof.
  induction i; destruct l.
  - simpl. omega.
  - intros. exact a.
  - simpl. omega.
  - intros. refine (IHi l (lt_S_n _ _ H)).
Defined.

Lemma get_cons: forall {i x l} (p: S i < length (x::l)) (p': i < length l),
  get p = get p'.
Proof.
  induction i; intros; destruct l; simpl length in *.
  - omega.
  - reflexivity.
  - omega.
  - simpl. setoid_rewrite (IHi a l p' (lt_S_n _ _ p')).
  setoid_rewrite (IHi a l (lt_S_n _ _ p) (lt_S_n _ _ p')). apply eq_refl.
Qed.

(** Check whether a predicate is satisfied by all the elements of a list: *)
Fixpoint all P (l: list A) := match l with
| nil => True
| cons b bs => P b /\ all P bs
end.

(** The extension of [<<] to lists. [l <<< l'] holds iff there exists an element [x]
    in [l] such that [l'] is obtained from [l] by replacing that element with a
    (possibly empty) list whose elements are all strictly smaller than [x].
*)
Inductive ltl : list A -> list A -> Prop :=
  | C : forall i (l l': list A) (p: i < length l),
         all (fun x => x << get p) l'
          -> ltl (replace p l') l .
Local Infix "<<<" := ltl (at level 80).

(** Comment: *)

Lemma ltl_cons: forall b a a',
  ltl a a' -> ltl (b :: a) (b :: a').
Proof.
  intros. destruct H. 
  pose proof (C (S i) (b :: l) l' (lt_n_S _ _ p)).
  rewrite (@get_cons i b l (lt_n_S _ _ p) p) in H0.
  rewrite (@replace_cons i b l l' (lt_n_S _ _ p) p) in H0.
  tauto.
Qed.

Lemma ltl_concat_left: forall a b b',
  ltl b b' -> ltl (a ++ b) (a ++ b').
Proof.
  induction a; simpl. auto.
  intros. pose proof (IHa _ _ H). destruct H0.
  pose proof (C (S i) (a :: l) l' (lt_n_S _ _ p)).
  setoid_rewrite (@replace_cons i a l l' (lt_n_S _ _ p) p) in H1.
  apply H1.
  rewrite (@get_cons i a l (lt_n_S _ _ p) p).
  assumption.
Qed.

Lemma ltl_concat_right: forall b a a',
  ltl a a' -> ltl (a ++ b) (a' ++ b).
Proof.
  intros. revert b.
  dependent destruction H. revert i p H.
  induction l; simpl; intros. omega.
  destruct i.
  - pose proof (C O (a :: l ++ b) l').
  cut (0 < length (a :: l ++ b)). intro.
  specialize H0 with H1. simpl.
  rewrite<- app_assoc. apply H0. assumption.
  simpl. omega.
  - simpl replace. fold (@length A). apply ltl_cons. apply IHl. 
  rewrite<- (@get_cons i a l p (lt_S_n _ _ p)). assumption.
Qed.

(** A useful inversion lemma:  *)
Lemma ltl_cases: forall {a l l'}, 
  l <<< a :: l'
    -> (exists l'', l'' <<< l' /\ l = a :: l'')
      \/ exists l'', l = l'' ++ l' /\ all (fun x => lt x a) l''.
Proof.
  intros. dependent destruction H.
  induction i.
  - right. exists l'0. simpl. split; auto.
  - left. exists (replace (lt_S_n _ _ p) l'0). split.
    pose proof (get_cons p).
    refine (C _ l' l'0 (lt_S_n _ _ p) H).
    apply (replace_cons p).
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
    simpl length in p. omega.
  - apply (l2p3 l IHl).
Qed.

(** * Unordered
    To consider lists as multisets, we now use permutations so to make
    our order relation ignore the position of elements in a list.

    We use Coq's Permutation library
    (see https://coq.github.io/doc/master/stdlib/Coq.Sorting.Permutation.html).
*)

Definition ltlp l l' := exists l'', Permutation l l'' /\ l'' <<< l'.

Lemma perm_lt_dx: forall {a b b'}, Permutation b b' -> a <<< b' -> ltlp a b.
Proof.
  intros. revert a H0. dependent induction H; intros; unfold ltlp.
  - dependent destruction H0. simpl length in p. omega.
  - destruct (ltl_cases H0); destruct H1, H1.
  -- rewrite H2 in *. clear a H2.
    destruct (IHPermutation _ H1), H2.
    exists (x :: x1). split.
  --- apply perm_skip. auto.
  --- dependent destruction H3. rewrite<- (replace_cons (lt_n_S _ _ p)).
      refine (C (S i) (x::l) l'0 _ _). rewrite (get_cons _ p). auto.
  -- rewrite H1 in *. clear a H1. exists (x0 ++ l). split.
     apply Permutation_app_head. apply Permutation_sym. auto.
     refine (C O (x::l) x0 _ H2). simpl length. omega.
  - destruct (ltl_cases H0); destruct H, H.
  -- rewrite H1 in *. clear a H1. destruct (ltl_cases H); destruct H1, H1.
  --- rewrite H2 in *. clear x0 H2. exists (y :: x :: x1).
      split. apply perm_swap. 
      dependent destruction H1.
      pose proof ((lt_n_S _ _ (lt_n_S _ _ p)) : S (S i) < length (y :: x :: l)).
      pose proof (fun X => C (S (S i)) (y :: x :: l) l' H2 X). simpl replace in H3.
      setoid_rewrite replace_cons in H3. apply H3.
      cut (get H2 = get p). intro. rewrite H4. assumption.
      simpl get.
      setoid_rewrite get_cons. apply eq_refl. auto.
  --- rewrite H1 in *. clear x0 H1. exists (x1 ++ x :: l). split.
      apply Permutation_cons_app. reflexivity.
      refine (C O (y :: x :: l) x1 _ _). apply H2.
  -- rewrite H in *. clear a H. exists (y :: x0 ++ l). split.
     symmetry. apply Permutation_cons_app. reflexivity.
     refine (C 1 (y :: x :: l) x0 _ _). apply H1.
  - destruct (IHPermutation2 _ H1), H2. destruct (IHPermutation1 _ H3), H4.
    exists x0. split. transitivity x; auto. auto.
    Grab Existential Variables. simpl length. omega. simpl length. omega.
Qed.

Lemma perm_Acc : forall l l', Permutation l l' -> Acc ltlp l -> Acc ltlp l'.
Proof.
  intros. induction H.
  - auto.
  - apply Acc_intro. intros. apply H0. destruct H1, H1. unfold ltlp.
    destruct (perm_lt_dx (perm_skip x H) H2). destruct H3. exists x1. split.
    transitivity x0; auto. auto.
  - apply Acc_intro. intros. apply H0. destruct H, H. unfold ltlp.
    destruct (perm_lt_dx (perm_swap x y l) H1). destruct H2. exists x1. split.
    transitivity x0; auto. auto.
  - auto.
Qed.

Theorem wf_perm : well_founded ltlp.
Proof.
    intro a. induction (wf_ltl a). apply Acc_intro. intros.
    destruct H1, H1. apply (perm_Acc _ _ (Permutation_sym H1)). auto.
Qed.

(* lltlp *)


Definition lltlp := clos_trans _ ltlp.
Definition wf_trans: well_founded lltlp.
Proof.
  apply wf_clos_trans. apply wf_perm.
Qed.

(** Aux: comment *)
Lemma lltlp_concat_left: forall a b b',
  lltlp b b' -> lltlp (a ++ b) (a ++ b').
Proof.
  intros. revert a. induction H; intro a.
  - destruct H, H. apply t_step. exists (a ++ x0).
    split. apply (Permutation_app_head a). assumption.
    apply (ltl_concat_left a). assumption.
  - apply (t_trans _ _ _ (a ++ y)).
    apply IHclos_trans1. apply IHclos_trans2.
Qed.

Lemma lltlp_concat_right: forall b a a',
  lltlp a a' -> lltlp (a ++ b) (a' ++ b).
Proof.
  intros. revert b. induction H; intro b.
  - destruct H, H. apply t_step. exists (x0 ++ b).
    split. apply (Permutation_app_tail b). assumption.
    apply (ltl_concat_right b). assumption.
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

End WfMult.

Arguments lltlp : default implicits.
Arguments wf_trans : default implicits.
