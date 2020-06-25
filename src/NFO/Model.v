Add LoadPath "src".
From NFO Require Import BoolExpr.

Inductive set :=
  S : forall A (p : @boolean A) (h: A -> set) X (f: X -> set), set.

Require Import Coq.Program.Tactics .
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.

Inductive lt : set -> set -> Prop :=
  | lt_f : forall A p h X f i, lt (f i) (S A p h X f)
  | lt_h : forall A p h X f i, lt (h i) (S A p h X f)
.
Infix "<" := lt.
Hint Constructors lt : Wff.

Lemma wf_lt : well_founded lt.
Proof. 
  unfold well_founded.
  induction a.
  apply Acc_intro. intros.
  dependent destruction H1; eauto.
Defined.
