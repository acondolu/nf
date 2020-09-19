(** * NFO.Sets : Set operators *)
(** In this module we define the following set constructors:
    emptyset, complement, singleton, co-singleton, exclusive
    disjunction. Union is defined separately, in [NFO.Union].
*)

(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Add LoadPath "src".
From Internal Require Import Misc FunExt.
From NFO Require Import Xor BoolExpr Model Eq In Morphism.
(* end hide *)

(** Empty set *)
Definition emptyset := enum (False_rect _).

Theorem emptyset_ok: forall x, ~ IN x emptyset.
Proof.
  unfold emptyset, enum. intro x. rewrite IN_unfold.
  unfold AIN, xor. setoid_rewrite ex_false. tauto.
Qed.

(** Set complement *)
Definition compl x := match x with
  S X Y f g e => S X Y f g (Not e)
end.

Theorem compl_ok: forall x y,
  IN x (compl y) <-> (IN x y -> False).
Proof.
  intros. destruct y. unfold compl. repeat rewrite IN_unfold.
  simpl BIN. setoid_rewrite xor_neg_commute. tauto.
Qed.

(** Singleton *)
Definition sin x := enum (fun _: unit => x).

Theorem sin_ok: forall x y, IN x (sin y) <-> EQ y x.
Proof.
  intros x y. unfold sin, enum. rewrite IN_unfold.
  simpl BIN. unfold AIN. setoid_rewrite ex_unit.
  apply xor_false_r.
Qed.

(** Co-singleton *)
Definition cosin x := S False unit (False_rect _) (fun _ => x) (Atom tt).

Theorem cosin_ok: forall x y, IN x (cosin y) <-> IN y x.
Proof.
  intros. unfold cosin. rewrite IN_unfold.
  setoid_rewrite ex_false. simpl BIN. apply xor_false_l.
Qed.

(** Exclusive disjunction *)

(** First, some auxiliary things *)


Lemma AIN_sum {X Y} (f: X + Y -> SET) x:
  AIN x f <-> AIN x (compose f inl) \/ AIN x (compose f inr).
Proof.
  unfold AIN, compose. split; intros.
  - destruct H, x0. left. eauto. right. eauto.
  - destruct H, H; eauto.
Qed.

Lemma AIN_sums {X X'} {f: X -> SET} {f': X' -> SET} {x}:
  AIN x (f ⨁ f') <-> (AIN x f) \/ (AIN x f').
Proof.
  setoid_rewrite AIN_sum. unfold compose, sumF. tauto.
Qed.

Lemma AIN_select {X} (f: X -> SET) (P: SET -> Prop) a:
  respects EQ P ->
    AIN a (select f (P ∘ f)) <-> P a /\ exists x, f x == a.
Proof.
  unfold AIN. intro H. setoid_rewrite (ex_T_resp P f a H). apply iff_refl.
Qed.

(** Xor of A-sets: *)

Definition AXor {X Y} (f: X -> SET) (g: Y -> SET)
  : sum {x & ~ exists y, EQ (g y) (f x)} {y & ~ exists x, EQ (f x) (g y)} -> SET
  := fun s => match s with
      | inl x => f (projT1 x)
      | inr y => g (projT1 y) 
    end.
Infix "^A^" := AXor (at level 50).

Local Definition bexpr_xor {A} (p p': @BExpr A) :=
  Or (Not (Or p (Not p'))) (Not (Or (Not p) p')).

(** TODO: Rename! *)
(** Xor of B-sets: *)
Definition QXor B C := 
  match B, C with S X Y f g e, S X' Y' f' g' e' =>
    S _ _
      (AXor f f')
        (g ⨁ g') (bexpr_xor (map inl e) (map inr e'))
  end.
Infix "^^^" := QXor (at level 50).

Lemma AXor_ok {X X'} {f: X -> SET} {f': X' -> SET} {x}:
  AIN x (AXor f f') <-> AIN x f ⊻ AIN x f'.
Proof.
  unfold AXor. setoid_rewrite AIN_sum. unfold compose; simpl.
  setoid_rewrite (AIN_select f (fun X => ~ exists y, f' y == X)).
  setoid_rewrite (AIN_select f' (fun X => ~ exists x, f x == X)).
  unfold xor, AIN. tauto.
  unfold respects. intros. setoid_rewrite H. tauto.
  unfold respects. intros. setoid_rewrite H. tauto.
Qed.

Lemma QXor_ok {X Y} {f: X -> SET} {g: Y -> SET} {z p q}:
  BIN z (map (f ⨁ g)
    (bexpr_xor (map inl p) (map inr q)))
  <-> BIN z (map f p) ⊻ BIN z (map g q).
Proof.
  unfold bexpr_xor. simpl BIN.
  setoid_rewrite map_compose.
  setoid_rewrite (@map_compose_inl _ _ _ f g).
  unfold xor. tauto.
Qed.

Theorem xor_ok: forall x y z,
  IN z (QXor x y) <-> IN z x ⊻ IN z y.
Proof.
  intros. destruct x, y. unfold QXor. setoid_rewrite IN_unfold.
  setoid_rewrite AXor_ok. setoid_rewrite QXor_ok.
  rewrite xor_pairs. tauto.
Qed.

(** LOL *)
Theorem xor_empty: forall x y, (x ^^^ y) == emptyset -> x == y.
  destruct x, y. unfold QXor, emptyset. setoid_rewrite EQ_unfold.
  apply and_morph.
  - setoid_rewrite Aext. setoid_rewrite AXor_ok.
    cut (forall x, AIN x (False_rect _) <-> False). intro.
    setoid_rewrite H. split; intros. split; try tauto. apply xor_neg. auto.
    apply xor_neg. rewrite H0. tauto. 
    unfold AIN. firstorder.
  - setoid_rewrite Bext. setoid_rewrite QXor_ok. simpl.
    split; intros. split. apply xor_neg. auto. tauto.
    apply xor_neg. rewrite H. tauto. 
Qed.