(* Multiset Extension, Take I *)

Parameter A : Type.
Parameter lt : A -> A -> Prop.
Axiom wf_lt: well_founded lt.

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.omega.Omega.

Definition replace : forall {i: nat} {l: list A},
  i < length l -> list A -> list A.
Proof.
  induction i; destruct l.
  - simpl. omega.
  - intros. exact (X ++ l).
  - simpl. omega.
  - intros. refine (a :: IHi l (lt_S_n _ _ H) X).
Defined.
Definition get : forall {i: nat} {l: list A}, i < length l -> A.
Proof.
  induction i; destruct l.
  - simpl. omega.
  - intros. exact a.
  - simpl. omega.
  - intros. refine (IHi l (lt_S_n _ _ H)).
Defined.

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

Lemma get_succ: forall {i l x} (p: S i < length (x::l)),
  get p = get (lt_S_n _ _ p).
Proof.
  induction i; intros; destruct l; simpl length in *.
  - omega.
  - reflexivity.
  - omega.
  - simpl. pose proof (IHi l a (lt_S_n _ _ p)). simpl in H.
    tauto.
Qed.

Lemma replace_succ: forall {i l l' x} (p: S i < length (x::l)),
  replace p l' = x :: replace (lt_S_n _ _ p: i < length l) l'.
Proof.
  induction i; intros; destruct l; simpl length in *.
  - omega.
  - reflexivity.
  - omega.
  - simpl. pose proof (IHi l l' a (lt_S_n _ _ p)). simpl in H.
    tauto.
Qed.

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
