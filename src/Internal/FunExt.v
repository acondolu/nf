(** Extensionally equivalent predicates *)
Definition extP {X} P Q := forall x: X, P x <-> Q x.

(** Extensionally equivalent binary predicates *)
Definition extP2 {X Y} P Q := forall x: X, forall y: Y, P x y <-> Q x y.

(* TODO: rename 'respects' to 'morphism'? P maps R to iff *)
Definition respects {X} (R: X -> X -> Prop) (P: X -> Prop) :=
  forall x x', R x x' -> (P x <-> P x').

Lemma respects_ext {X} (R R': X -> X -> Prop) :
  extP2 R R' -> extP (respects R) (respects R').
Proof.
  unfold respects, extP2, extP. intro.
  split; intros; apply H0; apply H; assumption.
Qed.
