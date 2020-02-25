Require Import Coq.Program.Tactics.
Require Coq.Program.Wf.
Require Import Coq.Program.Equality.

Add LoadPath "src/".
Require Base.
Require Lifting.

Module Type QuotSig.
Parameter 𝓥 : Type.
Parameter 𝓤 : 𝓥.
Parameter Ø : 𝓥.
Parameter Union: 𝓥 -> 𝓥 -> 𝓥.
Parameter Intersection: 𝓥 -> 𝓥 -> 𝓥.
Parameter Arrow: 𝓥 -> 𝓥 -> 𝓥.
Parameter Singleton: 𝓥 -> 𝓥.
Parameter CoSingleton: 𝓥 -> 𝓥.
Parameter IN: 𝓥 -> 𝓥 -> Prop.
Parameter EQ: 𝓥 -> 𝓥 -> Prop.

Parameter universe_ok: forall x: 𝓥, IN 𝓤 x.
Parameter empty_ok: forall x: 𝓥, ~ IN Ø x.
End QuotSig.

Module Quot <: QuotSig.

Private Inductive set : Type :=
  (* reflect lattice structure *)
  | prop : Prop -> set
  | binop : (Prop -> Prop -> Prop) -> (set -> set -> set)
  (* sets *)
  | sin : set -> set
  | cos : set -> set
.

Definition 𝓥 := set.
Definition 𝓤 := prop True.
Definition Ø := prop False.
Definition Union := binop or.
Definition Intersection := binop and.
Definition Arrow := binop (fun x y => x -> y).
Definition Singleton := sin.
Definition CoSingleton := cos.

Fixpoint undecorate {i} (x:Base.set i): set :=
match x with
  | Base.prop _ c => prop c
  | Base.binop _ P y z => binop P (undecorate y) (undecorate z)
  | Base.sin _ y => sin (undecorate y)
  | Base.cos _ y => cos (undecorate y)
end.

Inductive In : set -> set -> Prop :=
  | Cc : forall i x y, @Base.Iin i x y -> In (undecorate x) (undecorate y)
.
Definition IN := In.
(* Notation "A € B" := (In B A) (at level 85). *)
(* Lemma IN_' : forall x y, IN_ x y <-> exists i x y,  *)

Axiom Eq : set -> set -> Prop.
Definition EQ := Eq.

Axiom ex: forall x, exists i y, @undecorate i y = x.

Lemma mk_prop: forall p x, In (prop p) x <-> p.
Proof.
  intros p x. split; intro H.
  - dependent destruction H.
  dependent destruction x0; simpl undecorate in x.
   -- injection x. intro. destruct i.
   --- cbv in H. rewrite<- H0. exact H.
   --- cbv in H. rewrite<- H0. exact H. 
 -- discriminate x.
 -- discriminate x.
 -- discriminate x.
 - destruct (ex x). destruct H0.
   rewrite<- H0.
   cut (undecorate (Base.prop x0 p) = prop p).
   intros. rewrite<- H1. apply Cc.
   destruct x0. cbv. auto. cbv. auto.
   simpl undecorate. auto.
Qed.

Lemma universe_ok: forall x: 𝓥, In 𝓤 x.
Proof.
  intros. pose proof (mk_prop True).
  pose proof (H x). apply H0. auto.
Qed.

Lemma empty_ok: forall x: 𝓥, ~ In Ø x.
Proof.
  intros. pose proof (mk_prop False).
  pose proof (H x). intro. apply H0. auto.
Qed.

Lemma mk_binop:
  forall (P : Prop -> Prop -> Prop) x y z,
  P (In x z) (In y z) -> In (binop P x y) z. 
Admitted.

End Quot.