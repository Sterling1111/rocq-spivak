From Calculus.Chapter19 Require Import Prelude.

Definition kernel_19 (φ : R -> R) : Prop :=
  (∀ x, 0 <= φ x) /\ integrable_on (-1) 1 φ /\
  (∀ x, 1 <= Rabs x -> φ x = 0) /\ ∫ (-1) 1 φ = 1.
Definition scaled_kernel_19 (φ : R -> R) (h x : R) := φ (x/h)/h.
Lemma lemma_19_26_a : ∀ φ h, kernel_19 φ -> 0 < h ->
  (∀ x, h <= Rabs x -> scaled_kernel_19 φ h x = 0) /\
  ∫ (-h) h (scaled_kernel_19 φ h) = 1.
Abort.
Lemma lemma_19_26_b : ∀ φ f, kernel_19 φ ->
  integrable_on (-1) 1 f -> continuous_at f 0 ->
  right_limit (λ h, ∫ (-1) 1 (λ x, scaled_kernel_19 φ h x * f x)) 0 (f 0) /\
  right_limit (λ h, ∫ (-h) h (λ x, scaled_kernel_19 φ h x * f x)) 0 (f 0).
Abort.
Lemma lemma_19_26_c :
  right_limit (λ h, ∫ (-1) 1 (λ x, h/(h^2+x^2))) 0 π.
Abort.
Lemma lemma_19_26_d : ∀ f, integrable_on (-1) 1 f -> continuous_at f 0 ->
  right_limit (λ h, ∫ (-1) 1 (λ x, h/(h^2+x^2)*f x)) 0 (π*f 0).
Abort.
