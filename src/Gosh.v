Require Import Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Import Coq.Program.Equality.

Inductive set : nat -> Type :=
  (* reflect lattice structure *)
  | prop : forall i, Prop -> set i
  | binop : forall i,
      (Prop -> Prop -> Prop) -> (set i -> set i -> set i)
  (* sets *)
  | sin : forall i, nat -> set i -> set (S i)
.