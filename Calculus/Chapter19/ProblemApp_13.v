From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_13_a : improper_integral_pinf 1 (λ x, π*(1/x)^2) π.
Abort.

Lemma lemma_19_App_13_b :
  limit_pinf_to_pinf (λ b, 2*π * ∫ 1 b (λ x, (1/x)*√(1+1/x^4))).
Abort.

Lemma lemma_19_App_13_c : ∀ δ, 0 < δ ->
  ∃ N, 1 <= N /\ ∀ x, N < x -> 1/x < δ.
Abort.
