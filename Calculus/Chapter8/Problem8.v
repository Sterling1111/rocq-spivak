From Calculus.Chapter8 Require Import Prelude.

Section section_8_8.

Variable f : ℝ → ℝ.
Hypothesis H1 : ∀ a b, a < b -> f a < f b.

Lemma lemma_8_8_a : ∀ a,
  ∃ L1 L2,
    ⟦ lim a⁺ ⟧ f = L1 /\
    ⟦ lim a⁻ ⟧ f = L2.
Proof. Abort.

Lemma lemma_8_8_b : ∀ a : ℝ,
  ¬ removably_discontinuous_at f a.
Proof. Abort.

Lemma lemma_8_8_c :
  (∀ a b c,
    a < b ->
    f a <= c <= f b ->
    ∃ x, x ∈ [a, b] /\ f x = c) ->
  continuous f.
Proof. Abort.

End section_8_8.