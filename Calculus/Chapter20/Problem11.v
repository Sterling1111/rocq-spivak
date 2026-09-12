From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_11_a : ⟦ lim 0 ⟧ (λ x, (exp x - 1 - x - x^2/2) / (x - sin x)) = 1.
Proof.
Abort.

Lemma lemma_20_11_b : ⟦ lim 0 ⟧ (λ x, (exp x / (1+x) - 1 - x^2/2) / (x - sin x)) = -2.
Abort.
Lemma lemma_20_11_c : ⟦ lim 0 ⟧ (λ x, 1 / (sin x)^2 - 1 / x^2) = 1/3.
Abort.
Lemma lemma_20_11_d : ⟦ lim 0 ⟧ (λ x, (1 - cos (x^2)) / (x^2 * (sin x)^2)) = 1/2.
Abort.
Lemma lemma_20_11_e : ⟦ lim 0 ⟧ (λ x, 1 / (sin x)^2 - 1 / sin (x^2)) = 1/3.
Abort.
Lemma lemma_20_11_f : ⟦ lim 0 ⟧ (λ x, (sin x * arctan x - x^2) / (1 - cos (x^2))) = -1.
Abort.
