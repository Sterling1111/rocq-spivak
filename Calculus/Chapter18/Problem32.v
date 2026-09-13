From Calculus.Chapter18 Require Import Prelude.

From Lib Require Import Products.

Definition compound_sequence (n : nat) := (1 + 1 / n)^n.

Lemma lemma_18_32_a : ∀ a x, 0 < a -> a <> 1 -> 0 < x ->
  (⟦ der x ⟧ (λ y, log_ a y) = (λ y, log_ a e / y)) /\
  ⟦ lim 0 ⟧ (λ h, log_ a ((1 + h/x) ^^ (1/h))) = log_ a e / x.
Abort.

Lemma lemma_18_32_b :
  compound_sequence 1 = 2 /\
  (∀ n, (2 <= n)%nat -> compound_sequence n =
    2 + sum_f 2 n (λ k, / (fact k) *
      prod_f 1 (k-1) (λ j, 1 - j / n))) /\
  (∀ n, (1 <= n)%nat -> compound_sequence n < compound_sequence (S n)).
Abort.

Lemma lemma_18_32_c :
  (∀ n, (1 <= n)%nat -> compound_sequence n < 3) /\
  is_lub (λ y, ∃ n, (1 <= n)%nat /\ y = compound_sequence n) e /\
  (∀ eps, eps > 0 -> ∃ N : nat, ∀ n,
    (N <= n)%nat -> (1 <= n)%nat -> 0 <= e - compound_sequence n < eps).
Abort.

Lemma lemma_18_32_d_bounds : ∀ n x,
  (1 <= n)%nat -> n <= x <= (S n) ->
  (1 + 1 / (S n))^n <= (1 + 1/x) ^^ x <= (1 + 1 / n)^(S n).
Abort.

Lemma lemma_18_32_d :
  (⟦ lim ∞ ⟧ (λ x, (1 + 1/x) ^^ x) = e) /\
  (⟦ lim -∞ ⟧ (λ x, (1 + 1/x) ^^ x) = e) /\
  (⟦ lim 0 ⟧ (λ h, (1 + h) ^^ (1/h)) = e).
Abort.
