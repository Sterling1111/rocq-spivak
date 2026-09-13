From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_20 : ∀ (n : nat) f g a,
  ⟦ Der ^ n a ⟧ (λ x, f x * g x) = ∑ 0 n (λ k, (n ∁ k) * ⟦ Der ^ k a ⟧ f * ⟦ Der ^ (n - k) a ⟧ g).
Proof.
Abort.