From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_10_a_i : ∀ x,
	arcsinh x = log (x + sqrt (1 + x ^ 2)).
Abort.

Lemma lemma_18_10_a_ii : ∀ x,
	x >= 1 ->
	arccosh x = log (x + sqrt (x ^ 2 - 1)).
Abort.

Lemma lemma_18_10_a_iii : ∀ x,
	|x| < 1 ->
	arctanh x = 1 / 2 * log ((1 + x) / (1 - x)).
Abort.

Lemma lemma_18_10_b_i : ∀ a b,
	∫ a b (λ x, 1 / sqrt (1 + x ^ 2)) = arcsinh b - arcsinh a.
Abort.

Lemma lemma_18_10_b_ii_pos : ∀ a b,
	1 < a -> 1 < b ->
	∫ a b (λ x, 1 / sqrt (x ^ 2 - 1)) = arccosh b - arccosh a.
Abort.

Lemma lemma_18_10_b_ii_neg : ∀ a b,
	a < -1 -> b < -1 ->
	∫ a b (λ x, 1 / sqrt (x ^ 2 - 1)) = arccosh (-a) - arccosh (-b).
Abort.

Lemma lemma_18_10_b_iii : ∀ a b,
	|a| < 1 -> |b| < 1 ->
	∫ a b (λ x, 1 / (1 - x ^ 2)) = arctanh b - arctanh a.
Abort.

Lemma lemma_18_10_b_iv : ∀ x,
	|x| < 1 ->
	1 / (1 - x ^ 2) = 1 / 2 * (1 / (1 - x) + 1 / (1 + x)).
Abort.