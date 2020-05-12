
Add LoadPath "src/".
Require Import Tower.

Definition orbF {X} (f g: X -> bool) x := andb (f x) (g x).

Definition set X := prodT (X -> bool) ((X -> bool) -> bool).

Definition lift n : set (tower n) -> set (tower (S n)) := fun x => match x with
  (a, b) => (orbF (@ liftn (S n) a) b, @liftn' (S (S n)) b)
end.





Definition V := { n: nat & set (tower n)}.

Definition U : V := existT _ O (fun _ => true, fun _ => true).
Definition E : V := existT _ O (fun _ => false, fun _ => false).