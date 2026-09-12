From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_17_a :
   ⟦ lim 0 ⟧ (λ y, log (1 + y) / y) = 1.
Proof.
Abort.

Lemma lemma_18_17_b :
   ⟦ lim ∞ ⟧ (λ x, x * log (1 + 1 / x)) = 1.
Abort.

Lemma lemma_18_17_c :
   ⟦ lim ∞ ⟧ (λ x, exp (x * log (1 + 1 / x))) = e.
Abort.

Lemma lemma_18_17_d : ∀ a,
   ⟦ lim ∞ ⟧ (λ x, exp (x * log (1 + a / x))) = e ^^ a.
Abort.

Lemma lemma_18_17_e : ∀ b,
   b > 0 ->
   ⟦ lim ∞ ⟧ (λ x, x * (b ^^ (1 / x) - 1)) = log b.
Abort.
