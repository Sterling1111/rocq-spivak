From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_38 : forall (n : ℕ) (a : ℕ -> ℝ),
  ∑ 0 n (λ i, a i / (i + 1)) = 0 ->
  exists x, x ∈ (0, 1) /\ ∑ 0 n (λ i, a i * x^i) = 0.
Proof.
  
Abort.
