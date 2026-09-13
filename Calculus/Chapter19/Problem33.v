From Calculus.Chapter19 Require Import Prelude.

Fixpoint repeated_integral_19 (n : nat) (f : R -> R) (a : R) : R :=
  match n with O => f a | S k => ∫ 0 a (λ x, repeated_integral_19 k f x) end.
Lemma lemma_19_33 : ∀ f (n : nat) a, 0 <= a -> continuous_on f [0,a] ->
  ∫ 0 a (λ x, (a-x)^n / fact n * f x) = repeated_integral_19 (S n) f a.
Abort.
