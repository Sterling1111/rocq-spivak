From Calculus.Chapter13 Require Import Prelude.

From Lib Require Import Binomial.

Definition c_13_18 (n : nat) := ∫ 0 1 (λ x, x^n).

Lemma lemma_13_18_a : ∀ (n : nat) a,
  0 < a -> ∫ 0 a (λ x, x^n) = c_13_18 n * a^(n+1).
Abort.

Lemma lemma_13_18_b : ∀ (n : nat) a,
  0 < a ->
  2^(n+1) * c_13_18 n * a^(n+1) =
  2 * a^(n+1) * (∑ 0 n (λ k,
    if Nat.even k then (choose n k)%nat * c_13_18 k else 0)).
Abort.

Lemma lemma_13_18_c : ∀ n : nat, c_13_18 n = 1 / (n+1)%nat.
Abort.
