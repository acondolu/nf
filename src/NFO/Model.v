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
(* 
Lemma le_f_rew : 
forall X Y f g e x, f x < @S X Y f g e <-> True.
Admitted.

Lemma le_g_rew : 
forall X Y f g e x, g x < @S X Y f g e <-> True.
Admitted. *)

(** TODO: Axuliary INTRODUCE! *)
Definition enum {X} f := S X False f (False_rect _) Bot.

(* TODO: rename to subsetA *)
Definition subsetA {X} P f :=
  @enum { x: X & P (f x) } (fun ex => f (projT1 ex)).
