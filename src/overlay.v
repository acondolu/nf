Require cumulative.

Import cumulative.Cumulative.

Require Import examples.

Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.PropExtensionality.

Definition 𝓥: Type := {x | self x}.

Definition In: 𝓥 -> 𝓥 -> Prop := fun x y =>
  match x, y with
  | exist _ x' _, exist _ y' _ => forall n, y' (S n) (x' n)
end.

(*
Theorem u_ext: forall x y, self x -> self y -> 
  x = y <-> forall z, z ∈ x <-> z ∈ y.
*)

Theorem v_extensionality: forall x y : 𝓥, 
  x = y <-> forall z, In z x <-> In z y.
Proof.
  pose proof u_ext.
  induction x. induction y.
  split; intros. induction z. simpl In.
  apply (H x x0); auto. injection H0; auto.
  destruct (H x x0 p p0).
  unfold In in H0.
  cut (x=x0). intros. fold 𝓥. destruct H3. cut (p = p0). intro.
  destruct H3. auto.
  apply (ext_prop_dep_proof_irrel_cic propositional_extensionality).
  apply H2. unfold iin. intro.
   intro sz. apply (H0 (exist _ z sz)). 
Qed.

(* Universal set *)
Definition Top : 𝓥 := exist _ Universe univ_self.
Lemma Top_correct : forall x, In x Top.
Proof.
  intro x. destruct x. unfold Top, In, Universe. auto.
Qed.

(* Empty set *)
Definition Bot : 𝓥 := exist _ Empty empty_self.
Lemma Bot_correct : forall x, In x Bot -> False.
Proof.
  intro x. destruct x. unfold Bot, In, Empty.
  exact (fun f => f O).
Qed.

(* Powerset 
Definition Powerset := exist _ Pow pow_self. *)
