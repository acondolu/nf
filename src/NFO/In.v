(* begin hide *)
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
Add LoadPath "src".
From Internal Require Import Misc FunExt Common.
From NFO Require Import BoolExpr Model Eq Xor Wf.
(* end hide *)

(* Membership on the `Aczel` part of a NFO-set. *)
Notation AIN := (in_aczel EQ).

Local Definition IN' : SET * SET -> Prop.
 refine ( Fix (wf_swapprod _ lt wf_lt) (fun _ => Prop) (
  fun i rec => (
    match i as i0 return (i = i0 -> Prop) with (z, S X Y f g e)
  => fun eqx
  => AIN z f ⊻ ⟦ map (fun y => rec (g y, z) _) e ⟧ end) eq_refl
 )).
rewrite eqx. apply sp_swap. apply right_sym. eauto with Wff.
Defined.

(* Set membership *)
Definition IN s s' := IN' (s, s').

(* Temporary unfolding lemma for IN. 
   It will be improved in IN_unfold. *)
Local Lemma IN_def : forall {x},
  IN' x
    <->
    match x with (x', S X Y f g e) =>
      AIN x' f ⊻ ⟦ map (fun y => IN' (g y, x')) e ⟧
    end.
Proof.
  apply (well_founded_ind ((wf_swapprod _ lt wf_lt))).
  destruct x. intros.
  unfold IN' at 1. rewrite Fix_iff. destruct s0. fold IN'. tauto.
  destruct x. intros. destruct s2. apply xor_iff. tauto. apply map_extP.
  unfold FunExt.extP. split; intros; rewrite H0 in *; auto.
Qed.

(** TODO: Important, comment *)
Fixpoint IN_bexpr {Z} (R: Z -> Z -> Prop) y (p: BExpr) := match p with
  | Bot => False
  | Atom x => R x y
  | Not p' => ~ IN_bexpr R y p'
  | Or p1 p2 => IN_bexpr R y p1 \/ IN_bexpr R y p2
end.
Notation BIN := (IN_bexpr IN).

Lemma IN_bexpr_map Z (R: Z -> Z -> Prop) x e:
  ⟦ map (fun i => R i x) e ⟧ <-> IN_bexpr R x e.
Proof. induction e; simpl; tauto. Qed.

Lemma IN_bexpr_map2 {Z} (R: Z -> Z -> Prop) I f x (e: @BExpr I):
  ⟦ map (fun i => R (f i) x) e ⟧ <-> IN_bexpr R x (map f e).
Proof. induction e; simpl; tauto. Qed.

Lemma IN_unfold {x Y e g X f} :
  IN x (S X Y f g e) <-> AIN x f ⊻ BIN x (map g e).
Proof.
  unfold IN. rewrite IN_def.
  apply xor_iff. tauto.
  apply (IN_bexpr_map2 IN).
Qed.
Global Opaque IN.

(** Some random results about BIN. Not random. Used to prove extensionality of BIn. Move there? Explain *)

(** FIX & RENAME *)
Lemma xxx {X Y} {p} {h: X -> _} {f: SET -> Prop} (g: Y -> _):
  respects EQ f ->
    BIN (subsetA f (h ⨁ g)) (map h p) <-> eval (map f (map h p)).
Proof.
  intro. induction p; simpl map; simpl BIN; simpl eval.
  - tauto.
  - unfold subsetA, enum. rewrite IN_unfold. simpl. unfold AIN.
    setoid_rewrite (ex_T_resp _ _ _ H).
    cut (exists x0, (h ⨁ g) x0 == h x). intro.
    unfold xor. tauto. exists (inl x). reflexivity.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.

Lemma xxx_r {X Y} {p} {h: X -> _} {f: SET -> Prop} (g: Y -> _):
  respects EQ f ->
  BIN (subsetA f (g ⨁ h)) (map h p) <-> eval (map f (map h p)).
Proof.
  intro. induction p; simpl; simpl map; simpl BIN; simpl eval.
  - tauto.
  - unfold subsetA, enum. rewrite IN_unfold. simpl. unfold AIN.
    setoid_rewrite (ex_T_resp _ _ _ H).
    cut (exists x0, (g ⨁ h) x0 == h x). intro.
    unfold xor. tauto. exists (inr x). reflexivity.
  - rewrite IHp. tauto.
  - rewrite IHp1. rewrite IHp2. tauto.
Qed.
