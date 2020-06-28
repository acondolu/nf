(** * Internal.Wff2 : Well-founded multiset extension *)
(** In this module we define the multiset extension
    of a well-founded binary relation.
    
    We represent multisets just as lists.
TODO:

*)
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.omega.Omega.
Require Import Coq.Sorting.Permutation.


Section Wff2.

Variable A : Type.
Variable lt : A -> A -> Prop.
Variable wf_lt: well_founded lt.

(** Replace an element of a list with another list: *)
Definition replace : forall {i: nat} {l: list A},
  i < length l -> list A -> list A.
Proof.
  induction i; destruct l.
  - simpl. omega.
  - intros. exact (X ++ l).
  - simpl. omega.
  - intros. refine (a :: IHi l (lt_S_n _ _ H) X).
Defined.

Lemma replace_succ: forall {i l l' x} (p: S i < length (x::l)) (p': i < length l),
  replace p l' = x :: replace p' l'.
Proof.
  induction i; intros; destruct l; simpl length in *.
  - omega.
  - reflexivity.
  - omega.
  - simpl. setoid_rewrite (IHi l l' a). apply eq_refl.
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

Lemma get_succ: forall {i l x} (p: S i < length (x::l)) (p': i < length (l)),
  get p = get p'.
Proof.
  induction i; intros; destruct l; simpl length in *.
  - omega.
  - reflexivity.
  - omega.
  - simpl. setoid_rewrite (IHi l a p' (lt_S_n _ _ p')).
  setoid_rewrite (IHi l a (lt_S_n _ _ p) (lt_S_n _ _ p')). apply eq_refl.
Qed.

Fixpoint all P (x: list A) := match x with
| nil => True
| cons b bs => P b /\ all P bs
end.

Inductive lt_lst : list A -> list A -> Prop :=
  | C: forall i (l l': list A) (p: i < length l),
         all (fun x => lt x (get p)) l'
         ->
         lt_lst (replace p l') l
.

Lemma xxx: forall {y a l}, 
  lt_lst y (a :: l) -> 
    (exists l', lt_lst l' l /\ y = a :: l') \/
      (exists l', y = l' ++ l /\ all (fun x => lt x a) l').
Proof.
  intros. dependent destruction H.
  induction i.
  - right. exists l'. simpl. split; auto.
  - left. exists (replace (lt_S_n _ _ p) l'). split.
    pose proof (get_succ p).
    refine (C _ l l' (lt_S_n _ _ p) H).
    apply (replace_succ p).
Qed.

Lemma l2p1: forall {a M0},
  (forall b, lt b a -> forall M, Acc lt_lst M -> Acc lt_lst (b :: M))
  -> Acc lt_lst M0
  -> (forall M, lt_lst M M0 -> Acc lt_lst (a :: M))
  -> Acc lt_lst (a :: M0).
Proof.
  intros. apply Acc_intro. intros. destruct (xxx H2).
  - destruct H3, H3. rewrite H4 in *. clear H4 y. apply (H1 x H3).
  - destruct H3, H3. rewrite H3 in *; clear H3 y. induction x; simpl; intros.
  -- assumption.
  -- destruct H4. apply H. assumption. apply IHx; try assumption.
      apply (C O (a :: M0) x (Nat.lt_0_succ _) H4).
Qed.

Lemma l2p2: forall x,
(forall y : A, lt y x -> forall M, Acc lt_lst M -> Acc lt_lst (y :: M))
-> forall M, (Acc lt_lst M) ->  Acc lt_lst (x :: M).
Proof.
  intros.
    refine (@Fix_F (list A) lt_lst (fun M0 => Acc lt_lst M0 -> Acc lt_lst (x::M0)) _ M H0 H0). intros.
    rename x0 into M0.
    pose H2 as H2'. destruct H2'. pose proof (fun y h => H1 y h (H3 y h)).
    revert H H2 H4. clear. exact l2p1.
Qed.

Lemma l2p3: forall {M} a, Acc lt_lst M -> Acc lt_lst (cons a M).
Proof.
  intros M a. revert M. apply (well_founded_ind wf_lt (fun a => forall M, Acc lt_lst M -> Acc lt_lst (cons a M))).
  exact l2p2. 
Qed.

Theorem wf_lst: well_founded lt_lst.
Proof.
  unfold well_founded. intro l. induction l.
  - apply Acc_intro. intros. dependent destruction H.
    simpl length in p. omega.
  - apply (l2p3 a IHl).
Qed.



Definition permle l l' := exists l'', Permutation l l'' /\ lt_lst l'' l'.

Lemma perm_lt_dx: forall {a b b'}, Permutation b b' -> lt_lst a b' -> permle a b.
Proof.
  intros. revert a H0. dependent induction H; intros; unfold permle.
  - dependent destruction H0. simpl length in p. omega.
  - destruct (xxx H0); destruct H1, H1.
  -- rewrite H2 in *. clear a H2.
    destruct (IHPermutation _ H1), H2.
    exists (x :: x1). split.
  --- apply perm_skip. auto.
  --- dependent destruction H3. rewrite<- (replace_succ (lt_n_S _ _ p)).
      refine (C (S i) (x::l) l'0 _ _). rewrite (get_succ _ p). auto.
  -- rewrite H1 in *. clear a H1. exists (x0 ++ l). split.
     apply Permutation_app_head. apply Permutation_sym. auto.
     refine (C O (x::l) x0 _ H2). simpl length. omega.
  - destruct (xxx H0); destruct H, H.
  -- rewrite H1 in *. clear a H1. destruct (xxx H); destruct H1, H1.
  --- rewrite H2 in *. clear x0 H2. exists (y :: x :: x1).
      split. apply perm_swap. 
      dependent destruction H1.
      pose proof ((lt_n_S _ _ (lt_n_S _ _ p)) : S (S i) < length (y :: x :: l)).
      pose proof (fun X => C (S (S i)) (y :: x :: l) l' H2 X). simpl replace in H3.
      setoid_rewrite replace_succ in H3. apply H3.
      cut (get H2 = get p). intro. rewrite H4. assumption.
      simpl get.
      setoid_rewrite get_succ. apply eq_refl. auto.
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
(* use https://coq.github.io/doc/master/stdlib/Coq.Sorting.Permutation.html *)

Lemma perm_Acc : forall l l', Permutation l l' -> Acc permle l -> Acc permle l'.
Proof.
  intros. induction H.
  - auto.
  - apply Acc_intro. intros. apply H0. destruct H1, H1. unfold permle.
    destruct (perm_lt_dx (perm_skip x H) H2). destruct H3. exists x1. split.
    transitivity x0; auto. auto.
  - apply Acc_intro. intros. apply H0. destruct H, H. unfold permle.
    destruct (perm_lt_dx (perm_swap x y l) H1). destruct H2. exists x1. split.
    transitivity x0; auto. auto.
  - auto.
Qed.

Theorem wf_perm : well_founded permle.
Proof.
    intro a. induction (wf_lst a). apply Acc_intro. intros.
    destruct H1, H1. apply (perm_Acc _ _ (Permutation_sym H1)). auto.
Qed.
End Wff2.

Arguments permle : default implicits.
Arguments wf_perm : default implicits.