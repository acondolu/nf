(* begin hide *)
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Add LoadPath "src".
From NFO Require Import BoolExpr Model Eeq Xor Wff.
(* end hide *)

(** TODO: rename to In *)

(* Membership on the `Aczel` part of a NFO-set. *)
Definition Ain {X} (y: set) (f: X -> set) := exists x, eeq (f x) y.

Local Definition iin' : set * set -> Prop.
 refine ( Fix (wf_swapprod _ lt wf_lt) (fun _ => Prop) (
  fun i rec => (
    match i as i0 return (i = i0 -> Prop) with (z, S X Y f g e)
  => fun eqx
  => Ain z f ⊻ ⟦ map (fun y => rec (g y, z) _) e ⟧ end) eq_refl
 )).
rewrite eqx. apply sp_swap. apply right_sym. eauto with Wff.
Defined.

(* Set membership *)
Definition iin: set -> set -> Prop.
  intros x y. exact (iin' (x, y)).
Defined.

(* Temporary unfolding lemma for iin. 
   It will be improved in iin_unfold. *)
Local Lemma iin_def : forall {x},
  iin' x
    <->
    match x with (x', S X Y f g e) =>
      Ain x' f ⊻ ⟦ map (fun y => iin' (g y, x')) e ⟧
    end.
Proof.
  apply (well_founded_ind ((wf_swapprod _ lt wf_lt))).
  destruct x. intros.
  unfold iin' at 1. rewrite Fix_iff. destruct s0. fold iin'. tauto.
  destruct x. intros. destruct s2. apply xor_iff. tauto. apply map_extP.
  unfold FunExt.extP. split; intros; rewrite H0 in *; auto.
Qed.

(** TODO: Important, comment *)
Fixpoint Qin {X} x (h: X -> set) (p : boolean) := match p with
  | Bot => False
  | Atom a => iin (h a) x
  | Not p' => ~ Qin x h p'
  | Or p1 p2 => Qin x h p1 \/ Qin x h p2
end.


(** TODO: rename *)
Lemma Bin_bexpr {I x f} {e: @boolean I}:
  ⟦ map (fun i => iin (f i) x) e ⟧ <-> Qin x f e.
Proof. induction e; simpl; tauto. Qed.

Lemma iin_unfold {x Y e g X f} :
  iin x (S X Y f g e) <-> Ain x f ⊻ Qin x g e.
Proof.
  unfold iin. rewrite iin_def.
  apply xor_iff. tauto.
  apply Bin_bexpr.
Qed.
