Add LoadPath "src/".
Require Import Simplest.
Require Import Sets.

Definition zf x := match x with
  | Pos _ => True
  | Neg _ => False
end.

Definition pred_sound P := forall x y, x ≡ y -> (P x <-> P y).

Definition compr: forall {x}, zf x -> (set -> Prop) -> set.
Proof.
  intros x zf P.
  destruct x; destruct zf.
  apply (@Pos {x : X & P (s x)}).
  intro. destruct X0. exact (s x).
Defined.

Lemma compr_ok: forall {x} P (zf: zf x) (pok: pred_sound P), forall z, iin z (compr zf P) <-> iin z x /\ P z.
Proof.
  intros. destruct x; destruct zf0.
  simpl iin. split; intros; destruct H.
  -  destruct x. split. exists x. assumption.
    apply (pok _ _ H). assumption.
  - destruct H. destruct (pok _ _ H). 
    exists (existT _ x (H2 H0)). assumption.
Qed. 

Lemma zf_empty: zf Ø.
Proof. simpl zf. auto. Qed.

Lemma zf_sing : forall x, zf (sing x).
Proof. unfold sing; simpl zf; tauto. Qed.

Lemma zf_neg: forall x, zf (neg x) <-> ~ zf x.
Proof.
  destruct x; unfold neg; simpl zf; tauto.
Qed.

Lemma zf_cap: forall x y, zf (x ⋂ y) <-> (zf x \/ zf y).
Proof.
  destruct x; destruct y; simpl cap; simpl zf; tauto.
Qed.

Lemma zf_cup: forall x y, zf (x ∪ y) <-> (zf x /\ zf y).
Proof.
  destruct x; destruct y; simpl cap; simpl zf; tauto.
Qed.


(* Definition pow X (f: X -> set) :=
  @Pos (X -> Prop)
    (fun s => @Pos { x : X & s x }
      (fun ex => match ex with existT _ x _ => f x end) )
.

Definition subset x y := forall z, iin z x -> iin z y.

Lemma subset_ex : forall x, isZF x -> exists y, forall z, iin z y <-> subset z x.
Proof.
  intros. destruct x; destruct H.
  exists (pow X s). intros. split.
  - unfold pow. simpl iin. intro. destruct H. unfold subset.
  intros. simpl iin.
  destruct z. destruct H0. destruct H. *)
