(* begin hide *)
Add LoadPath "src/NFO" as NFO.
(* end hide *)
From NFO Require Import BoolExpr.

Inductive SET :=
  S : forall X Y (f: X -> SET) (g: Y -> SET) (e: @BExpr Y), SET.

(** TODO: Axuliary INTRODUCE! *)
Definition enum {X} f := S X False f (False_rect _) Bot.

(* TODO: rename to subsetA *)
Definition subsetA {X} P f :=
  @enum { x: X & P (f x) } (fun ex => f (projT1 ex)).
