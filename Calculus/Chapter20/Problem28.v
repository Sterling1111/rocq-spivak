From Calculus.Chapter20 Require Import Prelude.

Definition second_order_expansion (f f' m : ℝ -> ℝ) : Prop :=
  ∀ a, ⟦ lim a ⟧ (λ x, (f x - f a - f' a * (x-a) - m a / 2 * (x-a)^2) / (x-a)^2) = 0.

Lemma lemma_20_28_a :
  let f := λ x, if Req_EM_T x 0 then 0 else x^4 * sin (1/x^2) in
  (⟦ lim 0 ⟧ (λ x, f x / x^2) = 0) /\ ~ nth_differentiable_at 2 f 0 /\
  (∀ a, a <> 0 -> nth_differentiable_at 2 f a) /\
  (∃ f' m, ⟦ der ⟧ f = f' /\ m 0 = 0 /\
    (∀ a, a <> 0 -> m a = ⟦ Der ^ 2 a ⟧ f) /\
    second_order_expansion f f' m /\ ~ continuous_at m 0).
Abort.
Lemma lemma_20_28_b : ∀ f f',
  ⟦ der ⟧ f = f' -> second_order_expansion f f' (λ _, 0) ->
  ⟦ der ⟧ f' = (λ _, 0).
Abort.
Lemma lemma_20_28_c : ∀ f f' m,
  ⟦ der ⟧ f = f' -> second_order_expansion f f' m -> continuous m -> ⟦ der ⟧ f' = m.
Abort.
