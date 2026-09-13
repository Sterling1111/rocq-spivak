From Calculus.Chapter24 Require Import Prelude.

Definition Abel_summable (a : nat -> R) (L : R) : Prop :=
  ∃ f, (∀ x, 0 <= x < 1 -> ∑ 0 ∞ (λ n, a n * x^n) = (f x)) /\ ⟦ lim 1⁻ ⟧ f = L.

Lemma lemma_24_20 : ∃ a L,
  Abel_summable a L /\ ~ series_converges a.
Abort.
