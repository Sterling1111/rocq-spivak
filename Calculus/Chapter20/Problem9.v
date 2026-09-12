From Calculus.Chapter20 Require Import Prelude.

From Lib Require Import Polynomial.

(* For polynomial p, P(n,a,p) is exactly truncation in powers of x-a. *)
Lemma lemma_20_9_a : ∀ n a f g,
  nth_differentiable n f -> nth_differentiable n g ->
  P(n,a,λ x, f x + g x) = (λ x, P(n,a,f) x + P(n,a,g) x).
Abort.

Lemma lemma_20_9_b : ∀ n a f g,
  nth_differentiable n f -> nth_differentiable n g ->
  P(n,a,λ x, f x * g x) = P(n,a,λ x, P(n,a,f) x * P(n,a,g) x).
Abort.

(* The limit is at the Taylor center a; the scan prints x -> 0 in (c). *)
Lemma lemma_20_9_c : ∀ n a lp lq r,
  (⟦ lim a ⟧ (λ x, r x / (x-a)^n) = 0) ->
  ⟦ lim a ⟧ (λ x, (polynomial lp (polynomial lq x + r x) -
    polynomial lp (polynomial lq x)) / (x-a)^n) = 0.
Abort.

Lemma lemma_20_9_c_truncation : ∀ n lp lq,
  P(n,0,polynomial lp) = (λ _, 0) -> polynomial lq 0 = 0 ->
  P(n,0,λ x, polynomial lp (polynomial lq x)) = (λ _, 0).
Abort.

Lemma lemma_20_9_d : ∀ n f g,
  nth_differentiable n f -> nth_differentiable n g -> g 0 = 0 ->
  P(n,0,λ x, f (g x)) = P(n,0,λ x, P(n,0,f) (P(n,0,g) x)).
Abort.

Lemma lemma_20_9_e : ∀ n a f g,
  nth_differentiable n f -> nth_differentiable n g ->
  P(n,a,λ x, f (g x)) = P(n,a,λ x, P(n,g a,f) (P(n,a,g) x)).
Abort.

Lemma lemma_20_9_f : ∀ n a g,
  nth_differentiable n g -> g a = 0 ->
  P(n,a,λ x, 1 / (1-g x)) = P(n,a,λ x, ∑ 0 n (λ k, (P(n,a,g) x)^k)).
Abort.
