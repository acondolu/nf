Require Import Coq.Init.Wf.

(* Definition le3 le a b :=
  match a, b with (a1, a2, a3)  *)


(* 
Section Wff.
Variables set : Type.
Variables le_set : set -> set -> Prop.

Require Import Coq.Program.Equality.

Inductive le_two : (set * set) -> (set * set) -> Prop :=
  | Aa : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
  | Bb : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | Bb' : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | Bb'' : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
.

Inductive le_many : forall X, (X -> set) -> (X -> set) -> Prop :=
  | Cmany : forall X f g, (forall x, exists y, le_set (f x) (g y)) -> le_many X f g 
.

Definition two2many {X} (x: X * X) : unit + unit -> X := match x with
  (a, b) => fun y => match y with
  | inl _ => a
  | inr _ => b
  end end.
Definition le_two' x y := le_many _ (two2many x) (two2many y).
Check le_two'.

Lemma le_two_sym : forall {x a b}, le_two x (a, b) -> le_two x (b, a).
Proof.
  intros.
  dependent destruction H. apply Bb; assumption.
  apply Aa; assumption. apply Bb''; assumption.
  apply Bb'; assumption.
Qed.

Lemma acc_le_two_sym : forall {a b}, Acc le_two (a, b) -> Acc le_two (b, a).
Proof.
  intros. dependent induction H. apply Acc_intro. intros.
  apply H0. apply le_two_sym. assumption.
Qed.

Axiom trans: forall a b c, le_set a b -> le_set b c -> le_set a c.

Lemma wf_le_two : well_founded le_set -> well_founded le_two.
Proof.
  intro wf_le_set.
  unfold well_founded.
  destruct a. revert s s0.
  apply (well_founded_ind wf_le_set (fun s => forall s0 : set, Acc le_two (s, s0))).
  intros.
  revert s0 x H.
  apply (well_founded_ind wf_le_set (fun s0 => forall x : set,
  (forall y : set, le_set y x -> forall s1 : set, Acc le_two (y, s1)) ->
  Acc le_two (x, s0))). intros.
  apply Acc_intro. intros. destruct y.
  dependent destruction H1.
  - apply (H s0 H2 s). intros. apply H0. apply (trans _ s _); assumption.
  - apply acc_le_two_sym. apply (H s H1 s0). intros. apply H0.
    apply (trans _ s0 _); assumption.
  - apply acc_le_two_sym. apply (H0 s0 H2). 
  - admit.
Admitted.

End Wff. *)
