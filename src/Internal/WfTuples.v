(* begin hide *)
Require Import Coq.Init.Wf.
Require Import Coq.Lists.List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
From Coq.Wellfounded Require Import Inclusion Inverse_Image Transitive_Closure.
Add LoadPath "src/Internal" as Internal.
From Internal Require Import WfDecr.
(* end hide *)

Section MultiWf.

Variable A: Type.
Variable lt: A -> A -> Prop.
Variable wf_lt: well_founded lt.
Local Infix "<" := lt.

(** 2 *)

Definition le12 : A -> A * A -> Prop := fun a bs =>
  match bs with (b1, b2) => a < b1 \/ a < b2 end.

Definition le22 : A * A -> A * A -> Prop := fun a bs =>
  match a with (a1, a2) => le12 a1 bs /\ le12 a2 bs end.
Local Infix "<<" := le22 (at level 50).

Definition list2 {A: Type} := fun x: prod A A => let (x1, x2) := x in 
  x1 :: x2 :: nil.

Lemma le2lst:
  forall x y, x << y -> decr lt (list2 x) (list2 y).
Proof.
  intros. destruct x, y.
  cut (forall a (b: list A), a :: b <> nil <-> True). intro Y.
  destruct H, H, H0; simpl list2; rewrite decr_unfold; simpl; rewrite Y; tauto.
  intros. pose proof (@nil_cons _ a3 b). clear wf_lt H. firstorder.
Qed.

Theorem wf_two: well_founded le22.
Proof.
  apply (wf_incl _ _ (fun x y => decr lt (list2 x) (list2 y))).
  unfold inclusion. apply le2lst.
  apply (wf_inverse_image _ _ (decr lt) list2).
  apply wf_decr. assumption.
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
  forall x y, x <<< y -> decr lt (list3 x) (list3 y).
Proof.
  intros. destruct x, y, p, p0.
  cut (forall a (b: list A), a :: b <> nil <-> True). intro Y.
  destruct H, H, H0, H0, H1; simpl list3; rewrite decr_unfold; simpl; rewrite Y; tauto.
  intros. pose proof (@nil_cons _ a5 b). clear wf_lt H. firstorder.
Qed.

Theorem wf_three: well_founded le33.
Proof.
  apply (wf_incl _ _ (fun x y => decr lt (list3 x) (list3 y))).
  unfold inclusion. apply le3lst.
  apply (wf_inverse_image _ _ (decr lt) list3).
  apply wf_decr. assumption.
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

End MultiWf.

Arguments le22 : default implicits.
Arguments le33 : default implicits.
Arguments wf_two : default implicits.
Arguments wf_three : default implicits.
Arguments wf_two_ind : default implicits.
Arguments wf_three_ind : default implicits.