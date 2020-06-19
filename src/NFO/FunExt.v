(* Extensionally equal functions *)
Definition ext {X Y} f g :=
  forall x: X, f x = (g x : Y).

(* Extensionally equivalent predicates *)
Definition extP {X} P Q :=
  forall x: X, P x <-> Q x.

(* Extensionally equivalent binary predicates *)
Definition extP2 {X Y} P Q :=
  forall x: X, forall y: Y, P x y <-> Q x y.

Definition respects {X} (R: X -> X -> Prop) (f: X -> Prop)  :=
  forall x x', R x x' -> (f x <-> f x').

Lemma respects_ext {X} (f: X -> Prop) (R1 R2: X -> X -> Prop) :
  extP2 R1 R2 -> extP (respects R1) (respects R2).
Proof.
  unfold respects, extP2, extP. intro. split; intros; apply H0; apply H; assumption.
Qed.