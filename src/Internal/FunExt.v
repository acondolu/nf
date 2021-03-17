(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Require Import Setoid.
Add LoadPath "src/Internal" as Internal.
From Internal Require Import Misc.
(* end hide *)

(** Extensionally equivalent predicates *)
Definition extP {X} P Q := forall x: X, P x <-> Q x.

(** Extensionally equivalent binary predicates *)
Definition extR {X Y} P Q := forall x: X, forall y: Y, P x y <-> Q x y.
(* Infix "≡" := extR (at level 80, right associativity). *)

(* TODO: rename 'respects' to 'morphism'? P maps R to iff *)
Definition respects {X} (R: X -> X -> Prop) (P: X -> Prop) :=
  forall x x', R x x' -> (P x <-> P x').

Lemma respects_ext {X} (R R': X -> X -> Prop) :
  extR R R' -> extP (respects R) (respects R').
Proof.
  unfold respects, extR, extP. intro.
  split; intros; apply H0; apply H; assumption.
Qed.


(* ...  *)

Lemma respects_swap {X Y Z R} :
  forall (f: X -> Z) (g: Y -> Z) h,
    respects (R ⨀ (f ⨁ g)) h
      -> respects (R ⨀ (g ⨁ f)) (h ∘ swap).
Proof.
  unfold respects. unfold compR, sumF. 
  intros. destruct x, x'; unfold compose; simpl; apply H; assumption.
Qed.

(*  *)

(* Lemma invert_sum_respects {X Y Z} f g (R: Z -> Z -> Prop) (P: X + Y -> Prop):
  Equivalence R ->
    respects R (invert_sum P (R ∘ f) (R ∘ g)).
Proof.
  unfold respects in *. intros. destruct H.
  split; intros; repeat destruct H; firstorder.
Qed. *)

Lemma invert_sum_respects {X Y Z} h (R: Z -> Z -> Prop) (P: X + Y -> Prop):
  Equivalence R ->
    respects R (fun z => exists u, P u /\ R z (h u)).
Proof.
  unfold respects, compR, compose. firstorder.
Qed.

Lemma invert_sum_respects_f {X Y Z f g} {R: Z -> Z -> Prop} {P: X + Y -> Prop}:
  Equivalence R ->
  respects (R ⨀ (f ⨁ g)) P ->
  let K := (fun z => exists u, P u /\ R z ((f ⨁ g) u)) in
  FunExt.extP (P ∘ inl) (K ∘ f).
Proof.
  unfold FunExt.extP. intros. unfold compose.
  split; firstorder.
Qed.

Lemma invert_sum_respects_g {X Y Z f g} {R: Z -> Z -> Prop} {P: X + Y -> Prop}:
  Equivalence R ->
  respects (R ⨀ (f ⨁ g)) P ->
  let K := (fun z => exists u, P u /\ R z ((f ⨁ g) u)) in
  FunExt.extP (P ∘ inr) (K ∘ g).
Proof.
  unfold FunExt.extP. intros. unfold compose.
  split; firstorder.
Qed.

(*  *)

Lemma ex_T_resp: forall {X Y R} P (f: X -> Y) y,
  respects R P ->
    (exists ex: {x: X & P (f x) : Prop}, R (f (projT1 ex)) y) <-> P y /\ exists x, R (f x) y.
Proof.
  intros. setoid_rewrite (ex_T (fun X => P (f X)) (fun X => R (f X) y)).
  split; intro H0; destruct H0. destruct H0; split; eauto. apply (H _ _ H1). auto.
  firstorder.
Qed.
