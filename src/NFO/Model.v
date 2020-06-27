(* begin hide *)
From Coq.Program Require Import Tactics Wf Equality.
Add LoadPath "src".
From NFO Require Import BoolExpr.
(* end hide *)

Inductive set :=
  S : forall X Y (f: X -> set) (g: Y -> set) (e: @boolean Y), set.

Inductive lt : set -> set -> Prop :=
  | lt_f : forall X Y f g e x, lt (f x) (S X Y f g e)
  | lt_h : forall X Y f g e y, lt (g y) (S X Y f g e)
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
