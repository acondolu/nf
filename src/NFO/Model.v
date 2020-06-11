Add LoadPath "src/NFO/".
Require Import Bool.

Inductive set :=
  S : forall A (p : boolean A) (h: A -> set) X (f: X -> set), set.

Require Import Coq.Program.Tactics .
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.


Inductive le_set : set -> set -> Prop :=
  | le_f : forall A p h X f i, le_set (f i) (S A p h X f)
  | le_h : forall A p h X f i, le_set (h i) (S A p h X f)
.
Lemma wf_le_set : well_founded le_set.
Proof.
  unfold well_founded.
  induction a.
  apply Acc_intro. intros.
  dependent destruction H1.
  apply H0. apply H.
Qed.

Inductive le_two : (set * set) -> (set * set) -> Prop :=
  | AB : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
  | BA : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | AA : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | BB : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
.

Axiom wf_two: well_founded le_two.


Lemma wf_two_ind: forall P : set -> set -> Prop,
(forall x1 x2 : set,
 (forall y1 y2 : set, le_two (y1, y2) (x1, x2) -> P y1 y2) -> P x1 x2) ->
forall x y : set, P x y.
Proof.
  intros P H.
  cut (forall z, P (fst z) (snd z)).
  intros. apply (H0 (x, y)).
  apply (well_founded_ind wf_two).
  intros. destruct x. apply (H s s0). intros.
  apply (H0 (y1, y2)). assumption.
Qed.
