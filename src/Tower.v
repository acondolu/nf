Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.

Definition p := Prop.

(* Definition ite : Prop -> Three -> Three -> Three := fun p a b =>
  match classic p with
  | or_introl _ => a
  | or_intror _ => b
  end. *)

Inductive tree 
Inductive pow' X :=
  | Open
  | Closed
  | No : (X -> bool) -> (pow' X)
.
(* Hierarchy of powersets of rank n *)
Fixpoint tower n : Type := match n with
  | O => unit (* tt represents the empty set of rank 0 *)
  | S m => pow' (tower m)
end.

Definition lift0: tower 0 -> tower 1 := fun _ _ => No.
Definition univ n : tower (S n) := fun _ => Open.
Definition sing n : tower n -> tower (S n) :=
  fun x y => ite (eq y (eq x)) Closed No.
Definition cos n : tower n -> tower (S n) :=
  fun x y => ite (y x) Open No.

Fixpoint cum {n} : tower n -> tower (S n) := 
  match n with
  | O => lift0
  | S m =>
      fun x : (tower m -> Prop) -> Three =>
        fun y : tower (S m) -> Prop =>

  end
.

(* cumulativity *)
(* Fixpoint inj {n} : tower n -> tower (S n) := 
  match n with
  | O => fun _ => (fun _ => False, fun _ => False)
  | S m => fun x : tower (S m) =>
      (fun z: tower (S m) => snd x z \/
        exists z', z = (inj z') /\ fst x z',
        _)
  end. *)
