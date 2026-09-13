From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_37_a_i : ∃ L, improper_left_19 0 1 (λ x, sin (x+1/x)) L.
Abort.
Lemma lemma_19_37_a_ii : ∃ L, improper_left_19 0 1 (λ x, sin (x+1/x)^2) L.
Abort.
Lemma lemma_19_37_b_i : limit_pinf_to_pinf (λ b, ∫ 1 b (λ x, sin (1/x))).
Abort.
Lemma lemma_19_37_b_ii : improper_integrable_pinf 1 (λ x, sin (1/x)^2).
Abort.
