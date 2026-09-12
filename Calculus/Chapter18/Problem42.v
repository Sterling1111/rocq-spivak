From Calculus.Chapter18 Require Import Prelude.

(* Coefficients are indexed in ascending order: a_0,...,a_n. *)
Definition characteristic (n : nat) (a : nat -> R) (x : R) :=
  sum_f_R0 (λ i, a i * x^i) n.
Definition solves_linear_ode (n : nat) (a : nat -> R) (y : R -> R) : Prop :=
  nth_differentiable n y /\
  ∀ x, sum_f_R0 (λ i, a i * ⟦ Der ^ i x ⟧ y) n = 0.

Lemma lemma_18_42_a : ∀ n a alpha,
  characteristic n a alpha = 0 ->
  solves_linear_ode n a (λ x, exp (alpha*x)).
Abort.

Lemma lemma_18_42_b : ∀ n a alpha,
  characteristic n a alpha = 0 ->
  (⟦ der alpha ⟧ (characteristic n a) = (λ _, 0)) ->
  solves_linear_ode n a (λ x, x * exp (alpha*x)).
Abort.

(* Vanishing derivatives of orders 0,...,r-1 express a root of
   multiplicity at least r, which is sufficient for this conclusion. *)
Lemma lemma_18_42_c : ∀ n a alpha r k,
  (1 <= r)%nat -> (k < r)%nat ->
  (∀ j, (j < r)%nat -> ⟦ der ^ j alpha ⟧ (characteristic n a) = (λ _, 0)) ->
  solves_linear_ode n a (λ x, x^k * exp (alpha*x)).
Abort.

Lemma lemma_18_42_d : ∀ n a m (c : nat -> R) (y : nat -> R -> R),
  (∀ i, (i <= m)%nat -> solves_linear_ode n a (y i)) ->
  solves_linear_ode n a (λ x, sum_f_R0 (λ i, c i * y i x) m).
Abort.
