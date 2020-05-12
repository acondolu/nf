 Add LoadPath "src/".
Require Import Tower.

(* Cumulative hierarchy *)
Definition V := { n: nat & tower n }.

Definition E : V := existT _ O tt.
Definition U : V := existT tower 1 (fun _ => True, fun _ => True).

Fixpoint complement n : tower (S n) -> tower (S n) := fun x =>
  (fun z => fst x z -> False, fun z => snd x z -> False)
.

Fixpoint union n : tower n -> tower n -> tower n := 
  match n with
  | O => fun _ _ => tt
  | S m => fun x y =>
      (fun z => fst x z \/ fst y z, fun z => snd x z \/ snd y z)
  end
.

Definition sin n : tower n -> tower (S n) := fun x =>
  (fun z => x = z, fun _ => False)
.

(* Definition cos n : tower n -> tower (S n) := fun x =>
  (fun z: tower n => x z, fun z => z x)
. *)