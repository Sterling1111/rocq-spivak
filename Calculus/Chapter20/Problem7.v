From Calculus.Chapter20 Require Import Prelude.

Definition taylor_coefficient (f : ℝ -> ℝ) (a : ℝ) (k : ℕ) :=
  ⟦ Der ^ k a ⟧ f / (fact k).

Lemma lemma_20_7_i : ∀ f g a k,
  nth_differentiable k f -> nth_differentiable k g ->
  taylor_coefficient (λ x, f x + g x) a k =
    taylor_coefficient f a k + taylor_coefficient g a k.
Abort.

Lemma lemma_20_7_ii : ∀ f g a k,
  nth_differentiable k f -> nth_differentiable k g ->
  taylor_coefficient (λ x, f x * g x) a k =
    ∑ 0 k (λ j, taylor_coefficient f a j * taylor_coefficient g a (k-j)).
Abort.

Lemma lemma_20_7_iii : ∀ f a k, nth_differentiable (S k) f ->
  taylor_coefficient (λ x, ⟦ Der x ⟧ f) a k = (S k) * taylor_coefficient f a (S k).
Abort.

Lemma lemma_20_7_iv : ∀ f a k,
  continuous f -> nth_differentiable k f ->
  taylor_coefficient (λ x, ∫ a x f) a 0 = 0 /\
  taylor_coefficient (λ x, ∫ a x f) a (S k) = taylor_coefficient f a k / (S k).
Abort.

Lemma lemma_20_7_v : ∀ f a k,
  continuous f -> nth_differentiable k f ->
  taylor_coefficient (λ x, ∫ 0 x f) a 0 = ∫ 0 a f /\
  taylor_coefficient (λ x, ∫ 0 x f) a (S k) = taylor_coefficient f a k / (S k).
Abort.
