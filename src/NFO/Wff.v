(** * NFO.Wff : Well-founded orders on tuples *)
Add LoadPath "src".
From Internal Require Export WfTuples.
From NFO Require Import Model.

Infix "<<" := (le22 lt) (at level 50) : type_scope.
Infix "<<<" := (le33 lt) (at level 50) : type_scope.

Section Two.

Variables a a' b b': set.

Ltac auto2 := unfold le22; unfold le12; tauto.
Lemma AA : a < a' -> b < a' -> (a, b) << (a', b').
Proof. auto2. Qed.
Lemma AB : a < a' -> b < b' -> (a, b) << (a', b').
Proof. auto2. Qed.
Lemma BA : a < b' -> b < a' -> (a, b) << (a', b').
Proof. auto2. Qed.
Lemma BB : a < b' -> b < b' -> (a, b) << (a', b').
Proof. auto2. Qed.

End Two.

Hint Resolve AA AB BA BB: Wff.

Section Three.

Variables a a' b b' c c': set.

Ltac auto3 := unfold le33; unfold le13; tauto.

Lemma AAA : a < a' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma AAB : a < a' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma AAC : a < a' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABA : a < a' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABB : a < a' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABC : a < a' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACA : a < a' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACB : a < a' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACC : a < a' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

Lemma BAA : a < b' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAB : a < b' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAC : a < b' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBA : a < b' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBB : a < b' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBC : a < b' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCA : a < b' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCB : a < b' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCC : a < b' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

Lemma CAA : a < c' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAB : a < c' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAC : a < c' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBA : a < c' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBB : a < c' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBC : a < c' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCA : a < c' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCB : a < c' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCC : a < c' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

End Three.

Hint Resolve AAA AAB AAC ABA ABB ABC ACA ACB ACC BAA BAB BAC BBA BBB BBC BCA BCB BCC CAA CAB CAC CBA CBB CBC CCA CCB CCC : Wff.