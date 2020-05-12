Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.

Definition p := Prop.

Definition pow' X :=
  prodT
    (X -> p) (* finite extension *)
      ((X -> p) -> p) (* infinite extension *)
.

(* Hierarchy of powersets of rank n *)
Fixpoint tower n : Type := match n with
  | O => unit (* tt represents the empty set of rank 0 *)
  | S m => pow' (tower m)
end.

(* cumulativity *)
(* Fixpoint inj {n} : tower n -> tower (S n) := 
  match n with
  | O => fun _ => (fun _ => False, fun _ => False)
  | S m => fun x : tower (S m) =>
      (fun z: tower (S m) => snd x z \/
        exists z', z = (inj z') /\ fst x z',
        _)
  end. *)
