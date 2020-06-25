From Coq.Program Require Import Basics Combinators.

Add LoadPath "src".
From Internal Require Import Aux.

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

Lemma respects_swap {X Y Z P} :
  forall (f: X -> Z) (g: Y -> Z) h,
    respects (sum_i P f g) h
      -> respects (sum_i P g f) (compose h swap).
Proof.
  unfold respects.
  intros. destruct x, x'; unfold compose; simpl; apply H; apply (sum_i_sym H0).
Qed.
