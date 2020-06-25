Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.

Add LoadPath "src".
From NFO Require Import Bool Model Eeq Xor Wff.

(* Membership on the `Aczel` part of a NFO-set. *)
Definition Ain {X} (y: set) (f: X -> set) :=
  exists x, eeq (f x) y.

Definition iin' : set * set -> Prop.
 refine ( Fix (wf_swapprod _ lt wf_lt) (fun _ => Prop) (
  fun x rec => (
    match x as x0 return (x = x0 -> Prop) with (x', S A' p' h' X' f')
  => fun eqx
  => Xor
    (Ain x' f')
    (let w a := rec (h' a, x') _
      in eval (boolean_map w p'))
  end) eq_refl
 )).
rewrite eqx. apply sp_swap. apply right_sym. apply lt_h.
Defined.

(* Set membership *)
Definition iin x y := iin' (x, y).

(* Temporary unfolding lemma for iin. 
   It will be improved in iin_unfold. *)
Lemma iin_def : forall {x},
  iin' x
    <->
    match x with (x', S A' p' h' X' f') =>
    Xor
      (Ain x' f')
      (let w a := iin' (h' a, x')
       in eval (boolean_map w p')) end.
Proof.
  apply (well_founded_ind ((wf_swapprod _ lt wf_lt))).
  destruct x. intros.
  unfold iin' at 1. rewrite Fix_iff. destruct s0. fold iin'. tauto.
  destruct x. intros. destruct s2. apply xor_iff. tauto. apply boolean_map_extP.
  unfold FunExt.extP. split; intros; rewrite H0 in *; auto.
Qed.

Lemma iin_unfold {x A' p' h' X' f'} :
  iin x (S A' p' h' X' f')
    <->
    Xor
      (Ain x f')
      (let w a := iin' (h' a, x)
       in eval (boolean_map w p')).
Proof. apply (@iin_def (x, S A' p' h' X' f')). Qed.


Fixpoint Qin {X} x (h: X -> set) (p : boolean) := match p with
  | Bot => False
  | Atom a => iin (h a) x
  | Not p' => ~ Qin x h p'
  | Or p1 p2 => Qin x h p1 \/ Qin x h p2
end.


Lemma Qin_aux {x A} {p: @boolean A} {h} :
  (let w a := iin (h a) x
  in eval (boolean_map w p))
  <-> Qin x h p.
Proof. induction p; simpl; tauto. Qed.

Lemma iin_unfold' {x A p h X f} :
  iin x (S A p h X f)
    <->
    Xor
      (Ain x f)
      (Qin x h p).
Proof.
  rewrite iin_unfold.
  apply xor_iff. tauto.
  apply Qin_aux.
Qed.
