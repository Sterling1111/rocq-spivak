From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_20_a : ∀ x,
	x <> 0 ->
	⟦ der x ⟧ (λ x, log (|x|)) = (λ x, 1 / x).
Proof.
Abort.

Lemma lemma_18_20_b : ∀ f f',
	⟦ der ⟧ f = f' ->
	(∀ x, f x <> 0) ->
	⟦ der ⟧ (λ x, log (|f x|)) = f' / f.
Proof.
Abort.