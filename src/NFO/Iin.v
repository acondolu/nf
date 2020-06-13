Add LoadPath "src/NFO/".
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Xor.

(* Membership on the `low` part of a NFO-set. *)
Definition iin_low {X} (y: set) (f: X -> set) :=
  exists x, eeq (f x) y.


Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.

Definition iin' : set * set -> Prop.
 refine ( Fix (wf_swapprod _ lt wf_lt) (fun _ => Prop) (
  fun x rec => (
    match x as x0 return (x = x0 -> Prop) with (x', S A' p' h' X' f')
  => fun eqx
  => Xor
    (iin_low x' f')
    (let w a := rec (h' a, x') _
      in eval (boolean_map w p'))
  end) eq_refl
 )).
rewrite eqx. apply sp_swap. apply right_sym. apply lt_h.
Defined.

(* Set membership *)
Definition iin x y := iin' (x, y).

(* apply prod_uncurry. *)

Lemma uncurry: forall {X Y} {P : X -> Y -> Prop},
  (forall a : X * Y, P (fst a) (snd a)) -> forall x y, P x y.
Proof. intros. apply (H (x, y)). Qed.

(* TODO: important *)
Lemma iin_unfold : forall x y,
  iin x y = match y with S A' p' h' X' f'
    => Xor
      (iin_low x f')
      (let w a := iin (h' a) x
       in eval (boolean_map w p')) end.
Proof.
  apply uncurry.
  apply (well_founded_ind ((wf_swapprod _ lt wf_lt))).
  intros.
  destruct x.
  destruct s0.
  simpl.
  unfold iin.
  destruct s.
  unfold iin' at 1.
Admitted.
