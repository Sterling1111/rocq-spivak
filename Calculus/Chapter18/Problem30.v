From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_30 : ∀ n : nat,
  ⟦ lim ∞ ⟧ (λ x, e ^^ x / x ^ n) = ∞.
Proof.
  intros n.
  apply lhopital_pinf_0_0_pinf with (f' := λ x, e^^x) (g' := λ x, n * x ^ (n - 1)).
  auto_limit.
  Search (⟦ lim ∞ ⟧ _ = _).
Abort.
