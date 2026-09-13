From Calculus.Chapter14 Require Import Prelude.
From Lib Require Import Exponential.

Lemma lemma_14_26_i :
  ~ (∃ L, ∫ 0 ∞ (λ x, 1 / √(1 + x^3)) = L).
Abort.

Lemma lemma_14_26_ii :
  ~ (∃ L, ∫ 0 ∞ (λ x, x / (1 + x ^^ (3/2))) = L).
Abort.

Lemma lemma_14_26_iii :
  ~ (∃ L, ∫ 0 ∞ (λ x, 1 / (x * √(1 + x))) = L).
Abort.
