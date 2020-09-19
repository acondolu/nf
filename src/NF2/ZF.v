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
  apply (@Low {x : X & P (s x)}).
  intro. destruct X0. exact (s x).
Defined.

Lemma compr_ok: forall {x} P (low: low x) (pok: pred_sound P), forall z, IN z (compr low P) <-> IN z x /\ P z.
Proof.
  intros. destruct x; destruct low.
  simpl IN. split; intros; destruct H.
  -  destruct x. split. exists x. assumption.
    apply (pok _ _ H). assumption.
  - destruct H. destruct (pok _ _ H). 
    exists (existT _ x (H2 H0)). assumption.
Qed. 

(* 4. Pairing. OBVIOUS *)

(* 5. Union. Work in Progress *)
Lemma union_ax: forall x, exists y, forall z, IN z y <-> exists x', IN x' x /\ IN z x'.
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

  From Internal Require Import Misc.
Definition pow {X} (f: X -> set) :=
  Low _ (fun P => Low _ (select f P))
.
Definition subset x y := forall z, IN z x -> IN z y.

Lemma subset_ex : forall x, low x -> exists y, forall z, IN z y <-> subset z x.
Proof.
  intros. destruct x; destruct H.
  exists (pow s). intros. unfold pow. simpl. split.
  - intros. destruct H, z, H. unfold subset. simpl IN.
  intros. destruct H1. destruct (H0 x0), x1. unfold select in H2. simpl in H2. exists x1. transitivity (s0 x0); auto. 
  - destruct z.
  -- intros. exists (fun x => exists x0, s x ≡ s0 x0).
     unfold select. split; intros.
     destruct x, e. exists x0. assumption.
     cut (exists x : X0, s0 x ≡ s0 y). intro. destruct (H (s0 y) H0). rewrite (ex_T (fun x => exists y, _) (fun x => s x ≡ s0 y)).
     firstorder.
     exists y. reflexivity.
  -- admit. (* requires similar to ext, but only one implication *)
Admitted.
