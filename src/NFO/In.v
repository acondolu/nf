(* begin hide *)
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Add LoadPath "src".
From Internal Require Import Misc FunExt.
From NFO Require Import BoolExpr Model Eq Xor Wf.
(* end hide *)

(** TODO: rename to In *)

(* Membership on the `Aczel` part of a NFO-set. *)
Definition Ain {X} (y: SET) (f: X -> SET) := exists x, EQ (f x) y.

Local Definition IN' : SET * SET -> Prop.
 refine ( Fix (wf_swapprod _ lt wf_lt) (fun _ => Prop) (
  fun i rec => (
    match i as i0 return (i = i0 -> Prop) with (z, S X Y f g e)
  => fun eqx
  => Ain z f ⊻ ⟦ map (fun y => rec (g y, z) _) e ⟧ end) eq_refl
 )).
rewrite eqx. apply sp_swap. apply right_sym. eauto with Wff.
Defined.

(* Set membership *)
Definition IN: SET -> SET -> Prop.
  intros x y. exact (IN' (x, y)).
Defined.

(* Temporary unfolding lemma for IN. 
   It will be improved in IN_unfold. *)
Local Lemma IN_def : forall {x},
  IN' x
    <->
    match x with (x', S X Y f g e) =>
      Ain x' f ⊻ ⟦ map (fun y => IN' (g y, x')) e ⟧
    end.
Proof.
  apply (well_founded_ind ((wf_swapprod _ lt wf_lt))).
  destruct x. intros.
  unfold IN' at 1. rewrite Fix_iff. destruct s0. fold IN'. tauto.
  destruct x. intros. destruct s2. apply xor_iff. tauto. apply map_extP.
  unfold FunExt.extP. split; intros; rewrite H0 in *; auto.
Qed.

(** TODO: Important, comment *)
Fixpoint Qin {X} x (h: X -> SET) (p : BExpr) := match p with
  | Bot => False
  | Atom a => IN (h a) x
  | Not p' => ~ Qin x h p'
  | Or p1 p2 => Qin x h p1 \/ Qin x h p2
end.


(** TODO: rename *)
Lemma Bin_bexpr {I x f} {e: @BExpr I}:
  ⟦ map (fun i => IN (f i) x) e ⟧ <-> Qin x f e.
Proof. induction e; simpl; tauto. Qed.

Lemma IN_unfold {x Y e g X f} :
  IN x (S X Y f g e) <-> Ain x f ⊻ Qin x g e.
Proof.
  unfold IN. rewrite IN_def.
  apply xor_iff. tauto.
  apply Bin_bexpr.
Qed.
Global Opaque IN.

(** Some random results about Qin *)

(** FIX & RENAME *)
Lemma xxx {X Y} {p} {h: X -> _} {f: SET -> Prop} (g: Y -> _):
  respects EQ f ->
    Qin (subsetA f (h ⨁ g)) h p <-> eval (map f (map h p)).
Proof.
  intro. induction p; simpl map; simpl Qin; simpl eval.
  - tauto.
  - unfold subsetA, enum. rewrite IN_unfold. simpl. unfold Ain.
    setoid_rewrite (ex_T_resp _ _ _ H).
    cut (exists x0, (h ⨁ g) x0 == h x). intro.
    unfold xor. tauto. exists (inl x). reflexivity.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

Lemma xxx_r {X Y} {p} {h: X -> _} {f: SET -> Prop} (g: Y -> _):
  respects EQ f ->
  Qin (subsetA f (g ⨁ h)) h p <-> eval (map f (map h p)).
Proof.
  intro. induction p; simpl; simpl map; simpl Qin; simpl eval.
  - tauto.
  - unfold subsetA, enum. rewrite IN_unfold. simpl. unfold Ain.
    setoid_rewrite (ex_T_resp _ _ _ H).
    cut (exists x0, (g ⨁ h) x0 == h x). intro.
    unfold xor. tauto. exists (inr x). reflexivity.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.