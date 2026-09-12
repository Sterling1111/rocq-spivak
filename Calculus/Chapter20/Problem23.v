From Calculus.Chapter20 Require Import Prelude.

Definition schwarz_second_derivative (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ⟦ lim 0 ⟧ (λ h, (f (a+h) + f (a-h) - 2*f a) / h^2) = L.

Lemma lemma_20_23_a : ∀ f a,
  nth_differentiable_at 2 f a -> schwarz_second_derivative f a (⟦ Der ^ 2 a ⟧ f).
Abort.
Lemma lemma_20_23_b :
  let f := λ x, if Rle_dec 0 x then x^2 else -x^2 in
  schwarz_second_derivative f 0 0 /\ ~ nth_differentiable_at 2 f 0.
Abort.
Lemma lemma_20_23_c : ∀ f a L,
  (∃ δ, δ > 0 /\ ∀ x, |x-a| < δ -> f x <= f a) ->
  schwarz_second_derivative f a L -> L <= 0.
Abort.
Lemma lemma_20_23_d : ∀ f a,
  nth_differentiable_at 3 f a ->
  ⟦ lim 0 ⟧ (λ h, (f (a+h) - f (a-h) - 2*h*⟦ Der a ⟧ f) / h^3) =
    ⟦ Der ^ 3 a ⟧ f / 3.
Abort.
