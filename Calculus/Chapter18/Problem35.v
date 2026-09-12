From Calculus.Chapter18 Require Import Prelude.

From Lib Require Import Products.

Lemma lemma_18_35_a : convex_on exp ℝ /\ convex_on (λ x, - log x) (0, ∞).
Abort.

Lemma lemma_18_35_b : ∀ (n : nat) (p z : nat -> R),
  (1 <= n)%nat ->
  (∀ i, (1 <= i <= n)%nat -> p i > 0 /\ z i > 0) ->
  sum_f 1 n p = 1 ->
  prod_f 1 n (λ i, (z i) ^^ (p i)) <= sum_f 1 n (λ i, p i * z i).
Abort.

Lemma lemma_18_35_c : ∀ (n : nat) (z : nat -> R),
  (1 <= n)%nat -> (∀ i, (1 <= i <= n)%nat -> z i > 0) ->
  (prod_f 1 n z) ^^ (1 / n) <= sum_f 1 n z / n.
Abort.
