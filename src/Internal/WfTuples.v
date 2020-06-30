(* begin hide *)
Require Import Coq.Init.Wf.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Relation_Definitions.
Require Import Relation_Operators.
From Coq.Wellfounded Require Import Inclusion Inverse_Image Transitive_Closure.
Add LoadPath "src".
From Internal Require Wff2.
(* end hide *)

Section MultiWf.

(** Variant of Coq.Init.Wf.Fix_F_inv with iff instead of eq *)
Lemma Fix_F_inv_iff {A} {R: A -> A -> Prop} {Rwf: well_founded R} {F : forall x:A, (forall y:A, R y x -> Prop) -> Prop} : forall (F_ext :
forall (x:A) (f g:forall y:A, R y x -> Prop),
  (forall (y:A) (p:R y x), f y p <-> g y p) -> F x f <-> F x g)
  (x:A) (r s:Acc R x), Fix_F (fun _ => Prop) F r <-> Fix_F (fun _ => Prop) F s.
Proof.
intros. induction (Rwf x); intros.
rewrite <- (Fix_F_eq _ F r); rewrite <- (Fix_F_eq _ F s); intros.
  apply F_ext; auto.
Qed.

(** Variant of Coq.Init.Wf.Fix_eq *)
Lemma Fix_iff {A} {R: A -> A -> Prop} {Rwf: well_founded R} {F : forall x:A, (forall y:A, R y x -> Prop) -> Prop} : forall (F_ext :
forall (x:A) (f g:forall y:A, R y x -> Prop),
  (forall (y:A) (p:R y x), f y p <-> g y p) -> F x f <-> F x g) (x:A), Fix Rwf (fun _ => Prop) F x <-> F x (fun (y:A) (p: R y x) => Fix Rwf (fun _ => Prop) F y).
Proof.
  intros. unfold Fix.
  rewrite <- Fix_F_eq.
  apply F_ext; intros.
  apply (@Fix_F_inv_iff _ _ Rwf _ F_ext).
Qed.

(* 
TODO: use the multiset order extension in https://www21.in.tum.de/~nipkow/misc/multiset.ps
*)

Variable A: Type.
Variable lt: A -> A -> Prop.
Variable wf_lt: well_founded lt.
Local Infix "<" := lt.

Definition lltlp := (clos_trans _ (Wff2.ltlp lt)).
Definition wf_trans: well_founded lltlp.
Proof.
  apply wf_clos_trans. apply Wff2.wf_perm. apply wf_lt.
Qed.


(** 2 *)

Definition le12 : A -> A * A -> Prop := fun a bs =>
  match bs with (b1, b2) => a < b1 \/ a < b2 end.

Definition le22 : A * A -> A * A -> Prop := fun a bs =>
  match a with (a1, a2) => le12 a1 bs /\ le12 a2 bs end.
Local Infix "<<" := le22 (at level 50).

Definition list2 {A: Type} := fun x: prod A A => let (x1, x2) := x in 
  x1 :: x2 :: nil.

Lemma le2lst:
  forall x y, x << y -> lltlp (list2 x) (list2 y).
Proof.
  intros. destruct x, y. destruct H, H, H0; simpl list2.
   - apply (t_trans _ _ _ (a1 :: nil)); apply t_step.
     red. exists (a :: a0 :: nil). split; auto. 
     pose proof (Wff2.C _ lt O (a1 :: nil) (a :: a0 :: nil) ). simpl in H1. auto.
     exists (a1 :: nil). split; auto. 
     pose proof (Wff2.C _ lt 1 (a1 :: a2 :: nil) nil). simpl in H1. auto.
  - apply (t_trans _ _ _ (a1 :: a0 :: nil)); apply t_step.
    red. exists (a :: a0 :: nil). split; auto. 
    pose proof (Wff2.C _ lt O (a1 :: a0 :: nil) (a :: nil) ). simpl in H1. auto.
    exists (a1 :: a0 :: nil). split; auto. 
    pose proof (Wff2.C _ lt 1 (a1 :: a2 :: nil) (a0 :: nil)). simpl in H1. auto.
  - apply (t_trans _ _ _ (a0 :: a2 :: nil)); apply t_step.
    red. exists (a0 :: a :: nil). split. apply perm_swap.
    pose proof (Wff2.C _ lt 1 (a0 :: a2 :: nil) (a :: nil)). simpl in H1. auto.
    exists (a0 :: a2 :: nil). split; auto. 
    pose proof (Wff2.C _ lt O (a1 :: a2 :: nil) (a0 :: nil) ). simpl in H1. auto.
  - apply (t_trans _ _ _ (a2 :: nil)); apply t_step.
    red. exists (a :: a0 :: nil). split; auto. 
    pose proof (Wff2.C _ lt O (a2 :: nil) (a :: a0 :: nil) ). simpl in H1. auto.
    exists (a2 :: nil). split; auto. 
    pose proof (Wff2.C _ lt 0 (a1 :: a2 :: nil) nil). simpl in H1. auto.
Qed.

Theorem wf_two: well_founded le22.
Proof.
  apply (wf_incl _ _ (fun x y => lltlp (list2 x) (list2 y))).
  unfold inclusion. apply le2lst.
  apply (wf_inverse_image _ _ (lltlp) list2).
  apply wf_clos_trans.
  apply Wff2.wf_perm.
  apply wf_lt.
Qed.

Lemma wf_two_ind: forall P : A -> A -> Prop,
  (forall x1 x2,
    (forall y1 y2, (y1, y2) << (x1, x2) -> P y1 y2) -> P x1 x2)
      -> forall x y, P x y.
Proof.
  intros P H.
  cut (forall z, match z with (z1, z2) => P z1 z2 end).
  - intros. apply (H0 (x, y)).
  - apply (well_founded_ind wf_two).
    destruct x. intros. apply (H a a0). intros.
    apply (H0 (y1, y2)). assumption.
Qed.

(** 3 *)

Definition le13 : A -> A * A * A -> Prop := fun a bs =>
  match bs with (b1, b2, b3) => a < b1 \/ a < b2 \/ a < b3 end.

Definition le33 : A * A * A -> A * A * A -> Prop := fun a bs =>
  match a with (a1, a2, a3) => le13 a1 bs /\ le13 a2 bs /\ le13 a3 bs end.
Local Infix "<<<" := le33 (at level 50).

Definition list3 {A: Type} := fun x : A *A *A=> 
  match x with (x1, x2, x3) =>
  x1 :: x2 :: x3 :: nil end.

Lemma le3lst:
  forall x y, x <<< y -> lltlp (list3 x) (list3 y).
Proof.
  intros. destruct x, y, p, p0. destruct H, H, H0, H0, H1; simpl list3.
  - apply (t_trans _ _ _ (a3 :: nil)).
  -- apply t_step. red. exists (a1 :: a2 :: a :: nil). split. 
    reflexivity.
    pose proof (Wff2.C _ lt O (a3 :: nil) (a1 :: a2 :: a :: nil) ). simpl in H2. auto.
  -- apply (t_trans _ _ _ (a3 :: a0 :: nil)). apply t_step.
     exists (a3 :: nil). split; auto. 
     pose proof (Wff2.C _ lt 1 (a3 :: a0 :: nil) nil). simpl in H2. auto.
     apply t_step. exists (a3 :: a0 :: nil). split; auto. 
     pose proof (Wff2.C _ lt 1 (a3 :: a4 :: a0 :: nil) nil). simpl in H2. auto.
  -
Admitted.

Theorem wf_three: well_founded le33.
Proof.
  apply (wf_incl _ _ (fun x y => lltlp (list3 x) (list3 y))).
  unfold inclusion. apply le3lst.
  apply (wf_inverse_image _ _ (lltlp) list3).
  apply wf_clos_trans.
  apply Wff2.wf_perm.
  apply wf_lt.
Qed.

Lemma wf_three_ind:
  forall P : A -> A -> A -> Prop,
  (forall x1 x2 x3,
    (forall y1 y2 y3, (y1, y2, y3) <<< (x1, x2, x3) -> P y1 y2 y3) -> P x1 x2 x3)
    -> forall x y z, P x y z.
Proof.
  intros P H.
  cut (forall a, match a with (a1, a2, a3) => P a1 a2 a3 end).
  - intros. apply (H0 (x, y, z)).
  - apply (well_founded_ind wf_three).
    intros. destruct x, p. apply (H a0 a1 a). intros.
    apply (H0 (y1, y2, y3)). assumption.
Qed.

(* N *)
(* 
Fixpoint tupleN n : Type := match n with
  | O => A
  | S m => prod A (tupleN m)
  end.

Fixpoint le1M {m} : A -> tupleN m -> Prop :=
  match m with 
  | O => lt
  | S _ => fun a t => let (a', t') := t in a < a' /\ le1M a t'
  end.

Fixpoint leNM {n m} : tupleN n -> tupleN m -> Prop :=
  match n with 
  | O => le1M
  | S _ => fun t s => let (a, t') := t in le1M a s /\ leNM t' s
  end.

  (* Continue here *)
Definition listN {n} : tupleN n -> list A := match n with

Lemma le2lst:
  forall x y, x << y -> lltlp (list2 x) (list2 y).
Proof.
  intros. destruct x, y. destruct H, H, H0; simpl list2.
   - apply (t_trans _ _ _ (a1 :: nil)); apply t_step.
     red. exists (a :: a0 :: nil). split; auto. 
     pose proof (Wff2.C _ lt O (a1 :: nil) (a :: a0 :: nil) ). simpl in H1. auto.
     exists (a1 :: nil). split; auto. 
     pose proof (Wff2.C _ lt 1 (a1 :: a2 :: nil) nil). simpl in H1. auto.
  - apply (t_trans _ _ _ (a1 :: a0 :: nil)); apply t_step.
    red. exists (a :: a0 :: nil). split; auto. 
    pose proof (Wff2.C _ lt O (a1 :: a0 :: nil) (a :: nil) ). simpl in H1. auto.
    exists (a1 :: a0 :: nil). split; auto. 
    pose proof (Wff2.C _ lt 1 (a1 :: a2 :: nil) (a0 :: nil)). simpl in H1. auto.
  - apply (t_trans _ _ _ (a0 :: a2 :: nil)); apply t_step.
    red. exists (a0 :: a :: nil). split. apply perm_swap.
    pose proof (Wff2.C _ lt 1 (a0 :: a2 :: nil) (a :: nil)). simpl in H1. auto.
    exists (a0 :: a2 :: nil). split; auto. 
    pose proof (Wff2.C _ lt O (a1 :: a2 :: nil) (a0 :: nil) ). simpl in H1. auto.
  - apply (t_trans _ _ _ (a2 :: nil)); apply t_step.
    red. exists (a :: a0 :: nil). split; auto. 
    pose proof (Wff2.C _ lt O (a2 :: nil) (a :: a0 :: nil) ). simpl in H1. auto.
    exists (a2 :: nil). split; auto. 
    pose proof (Wff2.C _ lt 0 (a1 :: a2 :: nil) nil). simpl in H1. auto.
Qed. *)

End MultiWf.

Arguments le22 : default implicits.
Arguments le33 : default implicits.
Arguments wf_two : default implicits.
Arguments wf_three : default implicits.
Arguments wf_two_ind : default implicits.
Arguments wf_three_ind : default implicits.