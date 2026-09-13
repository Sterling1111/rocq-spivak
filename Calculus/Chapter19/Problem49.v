From Calculus.Chapter19 Require Import Prelude.

From Calculus.Chapter19 Require Import Problem48.
Definition hermite_data_19 (f Q : R -> R) (a b : R) :=
  cubic_19 Q /\ Q a = f a /\ Q b = f b /\ Q ((a+b)/2) = f ((a+b)/2) /\
  ⟦ Der ((a+b)/2) ⟧ Q = ⟦ Der ((a+b)/2) ⟧ f.
Definition four_derivatives_19 (f f1 f2 f3 f4 : R -> R) (a b : R) :=
  derivative_on f f1 [a,b] /\ derivative_on f1 f2 [a,b] /\
  derivative_on f2 f3 [a,b] /\ derivative_on f3 f4 [a,b].
Lemma lemma_19_49_a : ∀ f a b, a < b -> differentiable_at f ((a+b)/2) ->
  ∃ Q, hermite_data_19 f Q a b.
Abort.
Lemma lemma_19_49_b : ∀ f f1 f2 f3 f4 Q a b x, a < b ->
  four_derivatives_19 f f1 f2 f3 f4 a b -> hermite_data_19 f Q a b ->
  a <= x <= b -> ∃ ξ, a < ξ < b /\
  f x-Q x = (x-a)*(x-(a+b)/2)^2*(x-b)*f4 ξ/24.
Abort.
Lemma lemma_19_49_c : ∀ f f1 f2 f3 f4 a b, a < b ->
  four_derivatives_19 f f1 f2 f3 f4 a b -> continuous_on f4 [a,b] ->
  ∃ c, a < c < b /\
  ∫ a b f = (b-a)/6*(f a+4*f ((a+b)/2)+f b) - (b-a)^5/2880*f4 c.
Abort.
Lemma lemma_19_49_d : ∀ f f1 f2 f3 f4 a b n, a < b -> (0 < n)%nat ->
  four_derivatives_19 f f1 f2 f3 f4 a b -> continuous_on f4 [a,b] ->
  let h := (b-a)/(2*n) in ∃ c, a < c < b /\
  ∫ a b f = (b-a)/(6*n) * (f a +
    4*(∑ 1 n (λ i, f (a+(2*i-1)*h))) +
    2*(sum_first_19 (n-1) (λ i, f (a+2*i*h))) + f b) - (b-a)^5/(2880*n^4)*f4 c.
Abort.
