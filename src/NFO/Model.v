Add LoadPath "src/NFO/".
Require Import Bool.

Inductive set :=
  S : forall A (p : boolean A) (h: A -> set) X (f: X -> set), set.

Definition emptyset :=
  S False (Bot _) (False_rect _) False (False_rect _).

Definition compl x := match x with
  S A p h X f => S A (Not _ p) h X f
end.

Require Import Coq.Program.Tactics .
Require Import Coq.Program.Wf.
Require Import Coq.Program.Equality.


Inductive le_set : set -> set -> Prop :=
  | le_f : forall A p h X f i, le_set (f i) (S A p h X f)
  | le_h : forall A p h X f i, le_set (h i) (S A p h X f)
.
Lemma wf_le_set : well_founded le_set.
Proof.
  unfold well_founded.
  induction a.
  apply Acc_intro. intros.
  dependent destruction H1.
  apply H0. apply H.
Qed.

Inductive le_two : (set * set) -> (set * set) -> Prop :=
  | AB : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
  | BA : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | AA : forall a1 a2 b1 b2, le_set a1 b1 -> le_set a2 b1 -> le_two (a1, a2) (b1, b2)
  | BB : forall a1 a2 b1 b2, le_set a1 b2 -> le_set a2 b2 -> le_two (a1, a2) (b1, b2)
.

Axiom wf_two: well_founded le_two.

Program Fixpoint eeq' x { wf le_two x } := match x with
  | (S A p h X f, S A' p' h' X' f') =>
          (forall x, exists y, eeq' (f x, f' y))
          /\ (forall y, exists x, eeq' (f x, f' y))
          /\ let w (i j: A + A') := match i, j with
            | inl i', inl j' => eeq' (h i', h j')
            | inl i', inr j' => eeq' (h i', h' j')
            | inr i', inl j' => eeq' (h' i', h j')
            | inr i', inr j' => eeq' (h' i', h' j')
            end in 
            eeq_boolean (boolean_map inl p) (boolean_map inr p') w
end.
Next Obligation. apply AB; apply le_f. Qed.
Next Obligation. apply AB; apply le_f. Qed.
Next Obligation. apply AA; apply le_h. Qed.
Next Obligation. apply AB; apply le_h. Qed.
Next Obligation. apply BA; apply le_h. Qed.
Next Obligation. apply BB; apply le_h. Qed.
Next Obligation. apply wf_two. Qed.

Definition eeq x y := eeq' (x, y).

Axiom eeq_def : forall x y, eeq x y = match x, y with
  | S A p h X f, S A' p' h' X' f' =>
        (forall x, exists y, eeq (f x) (f' y))
        /\ (forall y, exists x, eeq (f x) (f' y))
        /\  
          eeq_boolean (boolean_map inl p) (boolean_map inr p') (sum_i eeq h h')
end.

Lemma eeq_refl : forall x, eeq x x.
Proof.
  induction x.
  rewrite eeq_def. split.
  intro. exists x. apply H0.
  split. intro x. exists x. apply H0.
  apply (eeq_boolean_refl p eeq h H).
Qed.

Lemma wf_two_ind: forall P : set -> set -> Prop,
(forall x1 x2 : set,
 (forall y1 y2 : set, le_two (y1, y2) (x1, x2) -> P y1 y2) -> P x1 x2) ->
forall x y : set, P x y.
Proof.
  intros P H.
  cut (forall z, P (fst z) (snd z)).
  intros. apply (H0 (x, y)).
  apply (well_founded_ind wf_two).
  intros. destruct x. apply (H s s0). intros.
  apply (H0 (y1, y2)). assumption.
Qed.

Lemma eeq_sym : forall x y, eeq x y -> eeq y x.
Proof.
  apply (wf_two_ind (fun x y => eeq x y -> eeq y x)). intros.
  destruct x1. destruct x2.
  rewrite eeq_def in *. destruct H0. destruct H1. 
  split.
  - intro x. destruct (H1 x). exists x0. apply H. apply AB ; apply le_f. assumption.
  - split. intro x0. destruct (H0 x0). exists x. apply H. apply AB ; apply le_f. assumption.
  revert H2. apply eeq_boolean_sym.
Qed.

Lemma eeq_trans : forall x y z, eeq x y -> eeq y z -> eeq x z.
Proof.
  apply (wf_two_ind (fun x y => forall z, eeq x y -> eeq y z -> eeq x z)). intros.
  destruct x1. destruct x2.
  rewrite eeq_def in *.
  destruct H0. destruct H2.
  destruct z. destruct H1. destruct H4. split.
  - intro x. destruct (H0 x). destruct (H1 x0). exists x1.
    apply (fun X => H _ _ X _ H6 H7).
    apply AB; apply le_f.
  - split.
  -- intro y. destruct (H4 y). destruct (H2 x). exists x0.
  apply (fun X => H _ _ X _ H7 H6).
  apply AB; apply le_f.
  -- apply (eeq_boolean_trans H3 H5).
Qed.
