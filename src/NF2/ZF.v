Add LoadPath "src".
From NF2 Require Import Model Sets.

(* When sets are low *)
Lemma low_empty: low Ø.
Proof. simpl low. auto. Qed.

Lemma low_sing : forall x, low (sing x).
Proof. unfold sing; simpl low; tauto. Qed.

Lemma low_neg: forall x, low (neg x) <-> ~ low x.
Proof.
  destruct x; unfold neg; simpl low; tauto.
Qed.

Lemma low_cap: forall x y, low (x ⋂ y) <-> (low x \/ low y).
Proof.
  destruct x; destruct y; simpl cap; simpl low; tauto.
Qed.

Lemma low_cup: forall x y, low (x ∪ y) <-> (low x /\ low y).
Proof.
  destruct x; destruct y; simpl cap; simpl low; tauto.
Qed.

(* ZF axioms *)
(* WORK IN PROGRESS *)

(* 2. Regularity
      forall x, neq x empty -> exists y in x, y cap x = emptyset
      It does not hold, either for positive or negative sets.
      Ex.: x= {u}, y = u for positives. U minus {{}} for negatives.
*)

(* 3. Comprehension
      Yes for positive sets and sound formulas.
*)
Definition pred_sound P := forall x y, x ≡ y -> (P x <-> P y).
Definition compr: forall {x}, low x -> (set -> Prop) -> set.
Proof.
  intros x low P.
  destruct x; destruct low.
  apply (@Pos {x : X & P (s x)}).
  intro. destruct X0. exact (s x).
Defined.

Lemma compr_ok: forall {x} P (pos: low x) (pok: pred_sound P), forall z, iin z (compr pos P) <-> iin z x /\ P z.
Proof.
  intros. destruct x; destruct pos.
  simpl iin. split; intros; destruct H.
  -  destruct x. split. exists x. assumption.
    apply (pok _ _ H). assumption.
  - destruct H. destruct (pok _ _ H). 
    exists (existT _ x (H2 H0)). assumption.
Qed. 

(* 4. Pairing. OBVIOUS *)

(* 5. Union. Work in Progress *)
Lemma union_ax: forall x, exists y, forall z, iin z y <-> exists x', iin x' x /\ iin z x'.
Proof.
  destruct x.
  - admit.
  - exists 𝒰. intros. split; intro. simpl. admit. apply univ_ok.
Admitted.

  (* 
  6. REPLACEMENT
  7. INFINITY
  8. POWER SET
  9. WELL-ORDERING
  *)

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