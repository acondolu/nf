Add LoadPath "src/NFO/".
Require Import Bool.
Require Import Model.
Require Import Eeq.
Require Import Xor.
Require Import Wff.

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
Proof. intros. apply (H (x, y)). Defined.

(* TODO: important *)
Lemma iin_unfold' : forall {x},
  iin' x
    <->
    match x with (x', S A' p' h' X' f') =>
    Xor
      (iin_low x' f')
      (let w a := iin' (h' a, x')
       in eval (boolean_map w p')) end.
Proof.
  apply (well_founded_ind ((wf_swapprod _ lt wf_lt))).
  destruct x. intros.
  unfold iin' at 1. rewrite Fix_iff. destruct s0. fold iin'. tauto.
  destruct x. intros. destruct s2. apply Xor_eq. tauto. apply boolean_map_extP.
  unfold FunExt.extP. split; intros; rewrite H0 in *; auto.
Qed.

Lemma iin_unfold {x A' p' h' X' f'} :
  iin x (S A' p' h' X' f')
    <->
    Xor
      (iin_low x f')
      (let w a := iin' (h' a, x)
       in eval (boolean_map w p')).
Proof. apply (@iin_unfold' (x, S A' p' h' X' f')). Qed.


Fixpoint iin_high {X} x (h: X -> set) (p : boolean X) := match p with
  | Bot _ => False
  | Atom _ a => iin (h a) x
  | Not _ p' => ~ iin_high x h p'
  | Or _ p1 p2 => iin_high x h p1 \/ iin_high x h p2
end.
