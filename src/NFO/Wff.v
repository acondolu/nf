(** * NFO.Wff : Well-founded orders on tuples *)
From Internal Require Export WfTuples.
From NFO Require Import Model.

Infix "<<" := (le22 lt) (at level 50) : type_scope.
Infix "<<<" := (le33 lt) (at level 50) : type_scope.

(* begin hide *)
Ltac auto2 := unfold le22; unfold le12; tauto.
Lemma AA {a a' b b': set}: a < a' -> b < a' -> (a, b) << (a', b').
Proof. auto2. Qed. Hint Resolve AA : Wff.
Lemma AB {a a' b b'}: a < a' -> b < b' -> (a, b) << (a', b').
Proof. auto2. Qed. Hint Resolve AB : Wff.
Lemma BA {a a' b b'}: a < b' -> b < a' -> (a, b) << (a', b').
Proof. auto2. Qed. Hint Resolve BA : Wff.
Lemma BB {a a' b b'}: a < b' -> b < b' -> (a, b) << (a', b').
Proof. auto2. Qed. Hint Resolve BB : Wff.
(* end hide *)


(* begin hide *)
Ltac auto3 := unfold le33; unfold le13; tauto.
Hint Extern 1 (_ <<< _) => unfold le33; unfold le13; tauto : Wff.

Lemma AAA {a a' b b' c c'}: a < a' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma AAB {a a' b b' c c'}: a < a' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma AAC {a a' b b' c c'}: a < a' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABA {a a' b b' c c'}: a < a' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABB {a a' b b' c c'}: a < a' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ABC {a a' b b' c c'}: a < a' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACA {a a' b b' c c'}: a < a' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACB {a a' b b' c c'}: a < a' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma ACC {a a' b b' c c'}: a < a' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

Lemma BAA {a a' b b' c c'}: a < b' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAB {a a' b b' c c'}: a < b' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BAC {a a' b b' c c'}: a < b' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBA {a a' b b' c c'}: a < b' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBB {a a' b b' c c'}: a < b' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BBC {a a' b b' c c'}: a < b' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCA {a a' b b' c c'}: a < b' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCB {a a' b b' c c'}: a < b' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma BCC {a a' b b' c c'}: a < b' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

Lemma CAA {a a' b b' c c'}: a < c' -> b < a' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAB {a a' b b' c c'}: a < c' -> b < a' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CAC {a a' b b' c c'}: a < c' -> b < a' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBA {a a' b b' c c'}: a < c' -> b < b' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBB {a a' b b' c c'}: a < c' -> b < b' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CBC {a a' b b' c c'}: a < c' -> b < b' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCA {a a' b b' c c'}: a < c' -> b < c' -> c < a' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCB {a a' b b' c c'}: a < c' -> b < c' -> c < b' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.
Lemma CCC {a a' b b' c c'}: a < c' -> b < c' -> c < c' -> (a, b, c) <<< (a', b', c').
Proof. auto3. Qed.

Hint Resolve AAA AAB AAC ABA ABB ABC ACA ACB ACC BAA BAB BAC BBA BBB BBC BCA BCB BCC CAA CAB CAC CBA CBB CBC CCA CCB CCC : Wff.
(* end hide *)