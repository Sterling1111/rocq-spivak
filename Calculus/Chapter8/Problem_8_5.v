From Calculus.Chapter8 Require Import Prelude.
From Lib Require Import Rational.

Lemma lemma_8_5_a : ∀ x y, y - x > 1 -> ∃ k : ℤ, x < k < y.
Proof. Admitted.

Lemma lemma_8_5_b : ∀ x y, x < y -> ∃ r, rational r /\ x < r < y.
Proof. Admitted.

Lemma lemma_8_5_c : ∀ r s, rational r -> rational s -> r < s -> ∃ t, irrational t /\ r < t < s.
Proof. Admitted.

Lemma lemma_8_5_d : ∀ x y, x < y -> ∃ t, irrational t /\ x < t < y.
Proof. Admitted.
