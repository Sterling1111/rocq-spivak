From Calculus.Chapter20 Require Import Prelude.

(* The derivative hypotheses in this definition assert existence, rather than
   relying on the default value of the total derivative operator. *)
Definition ode_solution (n : ℕ) (a : ℕ -> ℝ) (f : ℝ -> ℝ) : Prop :=
  nth_differentiable n f /\
  ∀ x, ⟦ Der ^ n x ⟧ f = ∑ 0 (n-1) (λ j, a j * ⟦ Der ^ j x ⟧ f).

Definition previous_coefficient (a : ℕ -> ℝ) (j : ℕ) :=
  match j with O => 0 | S i => a i end.

Definition next_coefficients (n : ℕ) (a b : ℕ -> ℝ) (j : ℕ) :=
  previous_coefficient b j + b (n-1)%nat * a j.

Fixpoint iterated_coefficients (n : ℕ) (a : ℕ -> ℝ) (k : ℕ) : ℕ -> ℝ :=
  match k with
  | O => a
  | S i => next_coefficients n a (iterated_coefficients n a i)
  end.

Lemma lemma_20_26_a : ∀ n a f,
  (0 < n)%nat -> ode_solution n a f ->
  ⟦ der ^ (S n) ⟧ f =
    (λ x, ∑ 0 (n-1) (λ j, (previous_coefficient a j + a (n-1)%nat * a j) * ⟦ Der ^ j x ⟧ f)).
Abort.

Lemma lemma_20_26_b : ∀ n a f,
  (0 < n)%nat -> ode_solution n a f ->
  let b := next_coefficients n a a in
  ⟦ der ^ (n+2) ⟧ f =
    (λ x, ∑ 0 (n-1) (λ j, (previous_coefficient b j + b (n-1)%nat * a j) * ⟦ Der ^ j x ⟧ f)).
Abort.

(* Any N >= max(1,|a_0|,...,|a_(n-1)|) gives the stated estimates. *)
Lemma lemma_20_26_c : ∀ n a f N,
  (0 < n)%nat -> ode_solution n a f ->
  N >= 1 -> (∀ j, (j < n)%nat -> |a j| <= N) ->
  ∀ k,
    (∀ j, (j < n)%nat -> |iterated_coefficients n a k j| <= 2^k * N^(S k)) /\
    ⟦ der ^ (n+k) ⟧ f =
      (λ x, ∑ 0 (n-1) (λ j, iterated_coefficients n a k j * ⟦ Der ^ j x ⟧ f)).
Abort.

Lemma lemma_20_26_d : ∀ n a f N,
  (0 < n)%nat -> ode_solution n a f ->
  N >= 1 -> (∀ j, (j < n)%nat -> |a j| <= N) ->
  ∀ x, ∃ M, M > 0 /\ ∀ k, |⟦ Der ^ (n+k) x ⟧ f| <= M * 2^k * N^(S k).
Abort.

(* For Taylor's remainder the constant must work on the whole segment
   between 0 and x, not merely at the single point x of part (d). *)
Lemma lemma_20_26_e_bound : ∀ n a f N,
  (0 < n)%nat -> ode_solution n a f ->
  N >= 1 -> (∀ j, (j < n)%nat -> |a j| <= N) ->
  (∀ j, (j < n)%nat -> ⟦ Der ^ j 0 ⟧ f = 0) ->
  ∀ x, ∃ M, M > 0 /\ ∀ k,
    |f x| <= M * 2^(S k) * N^(k+2) * |x|^(n+k+1) / (fact (n+k+1)) /\
    M * 2^(S k) * N^(k+2) * |x|^(n+k+1) / (fact (n+k+1)) <=
      M * |2*N*x|^(n+k+1) / (fact (n+k+1)).
Abort.

Lemma lemma_20_26_e : ∀ n a f,
  (0 < n)%nat -> ode_solution n a f ->
  (∀ j, (j < n)%nat -> ⟦ Der ^ j 0 ⟧ f = 0) -> f = (λ _, 0).
Abort.

Lemma lemma_20_26_f : ∀ n a f g,
  (0 < n)%nat -> ode_solution n a f -> ode_solution n a g ->
  (∀ j, (j < n)%nat -> ⟦ Der ^ j 0 ⟧ f = ⟦ Der ^ j 0 ⟧ g) -> f = g.
Abort.
