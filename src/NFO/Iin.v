Add LoadPath "src/NFO/".
Require Import Bool.
Require Import Model.
Require Import Eeq.

Definition iin_low {X} (y: set) (f: X -> set) :=
  exists x, eeq (f x) y.

Definition XOR a b := (a \/ b) /\ (a -> b -> False).

Require Import Coq.Wellfounded.Lexicographic_Product.

Require Import Eqdep.
Require Import Relation_Operators.
Require Import Transitive_Closure.

Program Fixpoint iin' (x: set * set) { wf (swapprod _ le_set) x } : Prop := match x with
| (x', S A' p' h' X' f') =>
          XOR
            (iin_low x' f')
            (let w a := iin' (h' a, x')
             in eval (boolean_map w p'))
end.
Next Obligation. apply sp_swap. apply right_sym. apply le_h. Qed.
Next Obligation. apply (wf_swapprod _ le_set wf_le_set). Qed.

Definition iin x y := iin' (x, y).
Axiom iin_unfold : forall x y,
iin x y = match (x, y) with (x, S A' p' h' X' f') =>
          XOR
            (iin_low x f')
            (let w a := iin (h' a) x
             in eval (boolean_map w p')) end.

