Require Import Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Import Coq.Program.Equality.

(* Inductive next (X: Type) :=
  | Prev : X -> next X
  | New: (X -> Prop) -> ((X -> Prop) -> Prop) -> next X
. *)

Definition next X := 
  prodT (X -> Prop) ((X -> Prop) -> Prop)
.

Fixpoint u n := match n with
  | O => Prop
  | S m => next (u m)
end.

(* Definition eq0 (x y: u 0) : Prop := x <-> y.
Definition in0 {n} (x: u n) (y: u 0) : Prop := y. *)

Definition respects {X} P (f: X -> Prop) :=
  forall x y, P x y -> (f x <-> f y).

Definition eq_ext {X} f g := 
  forall x: X, f x <-> g x.

Definition eq_ext_2 {X} f g :=
  forall x y: (X -> Prop), eq_ext x y -> (f x <-> g y).

Definition respects_2 {X} P f g :=
  forall x y: (X -> Prop), P x y -> (f x <-> g y).

Definition Arrow X E := { f: X -> Prop | respects E f }.

Definition next' X E := 
  prodT (Arrow X E)
  { g: (Arrow X E) -> Prop | respects
    (fun a b => eq_ext (proj1_sig a) (proj1_sig b)) g }
  .

Definition eq_ext_2_arr {X E} f g :=
  forall x y: (Arrow X E), eq_ext (proj1_sig x) (proj1_sig y) -> (f x <-> g y).

Definition nextEeq X E (x y: next' X E): Prop :=
  eq_ext (proj1_sig (fst x)) (proj1_sig (fst y))
  /\
  eq_ext_2_arr (proj1_sig (snd x)) (proj1_sig (snd y)) 
.
Check nextEeq.

Fixpoint Eeq {n}: u n -> u n -> Prop := match n with
  | O => fun x y => x <-> y
  | S m => fun x y =>
    respects Eeq (fst x) -> respects eq_ext (snd x) ->
    respects Eeq (fst y) -> respects eq_ext (snd y) ->
    eq_ext (fst x) (fst y) /\ eq_ext_2 (snd x) (snd y) 
end.
Definition okay {n} : u n -> Prop := match n with
  | O => fun _ => True
  | S m => fun x => respects Eeq (fst x) /\ respects eq_ext (snd x)
end.

Definition prop {n} p : u n := match n with
  | O => p
  | S m => (fun _ => p, fun _ => p)
end.

Definition sin {n} : u n -> u (S n) := match n with
  | O => fun x => (Eeq x, fun _ => False)
  | S m => fun x => (Eeq x, fun _ => False)
end.

Axiom Iin: forall {n}, u n -> u n -> Prop.
Definition Ap {X} x (f: X -> Prop) := f x.

Definition cos {n} : u n -> u (S n) := match n with
  | O => fun x => (Iin x, Ap x)
  | S m => fun x => (Iin x, Ap x)
end.



Definition eq1 (x y: u 1) : Prop := match x, y with
  | (a, b), (c, d) =>
    (forall f, respects eq0 f -> (a f <-> c f))
    /\
    (forall f, respects f eq0 -> (b f <-> d f))
end.
