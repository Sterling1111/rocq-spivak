From Calculus.Chapter23 Require Import Prelude.

From Lib Require Export Products.

Definition infinite_product_converges (b : sequence) : Prop :=
  (∀ n, (n > 0)%nat -> b n > 0) /\
  ∃ L, L <> 0 /\ ⟦ lim ⟧ (λ n, prod_f 1 n b) = L.

Lemma problem_23_28_a : ∀ b,
  infinite_product_converges b -> ⟦ lim ⟧ b = 1.
Abort.

Lemma problem_23_28_b : ∀ b,
  (∀ n, (n > 0)%nat -> b n > 0) ->
  (infinite_product_converges b <-> series_converges (λ n, log (b (S n)))).
Abort.

Lemma problem_23_28_c : ∀ a,
  (∀ n, (n > 0)%nat -> a n >= 0) ->
  (infinite_product_converges (λ n, 1 + a n) <->
   series_converges (λ n, a (S n))).
Abort.

Lemma problem_23_28_d_estimate :
  ∃ δ, 0 < δ < 1 /\ ∀ x, |x| < δ ->
    1/4 * x^2 <= x - log (1+x) <= 3/4 * x^2.
Abort.

Lemma problem_23_28_d_i : ∀ a,
  (∀ n, (n > 0)%nat -> a n > -1) ->
  series_converges (λ n, a (S n)) ->
  (series_converges (λ n, log (1 + a (S n))) <->
   series_converges (λ n, a (S n)^2)).
Abort.

Lemma problem_23_28_d_ii : ∀ a,
  (∀ n, (n > 0)%nat -> a n > -1) ->
  series_converges (λ n, a (S n)^2) ->
  (series_converges (λ n, log (1 + a (S n))) <->
   series_converges (λ n, a (S n))).
Abort.

Lemma problem_23_28_e :
  series_converges (λ n, (-1)^(n+2) / √(((n+2)%nat : ℝ))) /\
  ~ (∃ L, L <> 0 /\
      ⟦ lim ⟧ (λ N, prod_f 2 N (λ (n : ℕ), 1 + (-1)^n / √(n : ℝ))) = L).
Abort.

Definition product_counterexample (n : nat) : R :=
  let k := Nat.sqrt ((n-1)/2) in
  if Nat.odd n then 1 / (2*k+1)%nat else -1 / (2*k+2)%nat.

Lemma problem_23_28_f :
  ~ series_converges (λ n, product_counterexample (S n)) /\
  ⟦ lim ⟧ (λ N, prod_f 1 N (λ n, 1 + product_counterexample n)) = 1.
Abort.
