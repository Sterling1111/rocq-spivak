From Calculus.Chapter19 Require Import Prelude.

Definition linear_interpolant_19 (f : R -> R) (a b x : R) :=
  f a + (f b-f a)*(x-a)/(b-a).
Definition trapezoid_19 (f : R -> R) (a b : R) (n : nat) :=
  let h := (b-a)/n in h * ((f a+f b)/2 + sum_first_19 (n-1) (λ i, f (a+i*h))).
Lemma lemma_19_47_a : ∀ f f' f'' a b m M,
  a < b -> derivative_on f f' [a,b] -> derivative_on f' f'' [a,b] ->
  continuous_on f'' [a,b] -> (∀ x, a <= x <= b -> m <= f'' x <= M) ->
  let I := ∫ a b (λ x, (x-a)*(x-b)) in
  M*I/2 <= ∫ a b (λ x, f x-linear_interpolant_19 f a b x) <= m*I/2.
Abort.

Lemma lemma_19_47_b : ∀ f f' f'' a b m M,
  a < b -> derivative_on f f' [a,b] -> derivative_on f' f'' [a,b] ->
  continuous_on f'' [a,b] -> (∀ x, a <= x <= b -> m <= f'' x <= M) ->
  -M*(b-a)^3/12 <= ∫ a b (λ x, f x-linear_interpolant_19 f a b x) <= -m*(b-a)^3/12.
Abort.

Lemma lemma_19_47_c : ∀ f f' f'' a b n,
  a < b -> (0 < n)%nat -> derivative_on f f' [a,b] -> derivative_on f' f'' [a,b] ->
  continuous_on f'' [a,b] -> ∃ c, a < c < b /\
  ∫ a b f = trapezoid_19 f a b n - (b-a)^3/(12*n^2)*f'' c.
Abort.
