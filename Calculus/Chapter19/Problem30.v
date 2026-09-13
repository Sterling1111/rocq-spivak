From Calculus.Chapter19 Require Import Prelude.

From Calculus.Chapter19 Require Import Problem29.
Lemma lemma_19_30_i :
  has_length_19 (λ x, x) (λ x, (x^2+2)^^(3/2)/3) 0 1 (4/3).
Abort.

Lemma lemma_19_30_ii :
  has_length_19 (λ x, x) (λ x, x^3+1/(12*x)) 1 2 (169/24).
Abort.

Lemma lemma_19_30_iii : ∀ a, 0 < a ->
  has_length_19 (λ t, a^3*cos t^3) (λ t, a^3*sin t^3) 0 (2*π) (6*a^3).
Abort.

Lemma lemma_19_30_iv :
  has_length_19 (λ x, x) (λ x, log (cos x)) 0 (π/6) (log 3/2).
Abort.

Lemma lemma_19_30_v :
  has_length_19 (λ x, x) log 1 (exp 1)
    (√(exp 1^2+1) - √2 + log (exp 1/(1+√(exp 1^2+1))) + log (1+√2)).
Abort.

Lemma lemma_19_30_vi :
  has_length_19 (λ x, x) (λ x, arcsin (exp x)) (-log 2) 0 (log (2+√3)).
Abort.
