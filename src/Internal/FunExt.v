(* begin hide *)
From Coq.Program Require Import Basics Combinators.
Require Import Setoid.
Add LoadPath "src".
From Internal Require Import Aux.
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
