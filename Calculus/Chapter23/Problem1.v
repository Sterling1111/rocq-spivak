From Calculus.Chapter23 Require Import Prelude.


Lemma problem_23_1_i : ∀ θ,
  series_converges (λ n, sin ((S n)%nat * θ) / (S n)%nat^2).
Abort.

Lemma problem_23_1_ii :
  series_converges (λ n, (-1)^n / (2*n+1)%nat).
Abort.

Lemma problem_23_1_iii :
  ~ series_converges (λ n, if Nat.even n then 2 / (n / 2 + 2)%nat else -1 / (n / 2 + 2)%nat).
Abort.

Lemma problem_23_1_iv :
  series_converges (λ n, (-1)^(S n) * log ((S n)%nat) / (S n)%nat).
Abort.

Lemma problem_23_1_v :
  ~ series_converges (λ n, 1 / (((n+2)%nat^2 - 1) ^^ (1/3))).
Abort.

Lemma problem_23_1_vi :
  ~ series_converges (λ n, 1 / (((S n)%nat^2 + 1) ^^ (1/3))).
Abort.

Lemma problem_23_1_vii :
  series_converges (λ n, (S n)%nat^2 / (fact (S n))%nat).
Abort.

Lemma problem_23_1_viii :
  ~ series_converges (λ n, log ((S n)%nat) / (S n)%nat).
Abort.

Lemma problem_23_1_ix :
  ~ series_converges (λ n, 1 / log (((n+2)%nat : ℝ))).
Abort.

Lemma problem_23_1_x : ∀ k : R,
  ~ series_converges (λ n, 1 / (log (((n+2)%nat : ℝ))) ^^ k).
Abort.

Lemma problem_23_1_xi :
  series_converges (λ n, 1 / (log (((n+2)%nat : ℝ)))^(n+2)).
Abort.

Lemma problem_23_1_xii :
  series_converges (λ n, (-1)^(n+2) / (log (((n+2)%nat : ℝ)))^(n+2)).
Abort.

Lemma problem_23_1_xiii :
  ~ series_converges (λ n, (S n)%nat^2 / ((S n)%nat^3 + 1)).
Abort.

Lemma problem_23_1_xiv :
  ~ series_converges (λ n, sin (1 / (S n)%nat)).
Abort.

Lemma problem_23_1_xv :
  ~ series_converges (λ n, 1 / ((n+2)%nat * log (((n+2)%nat : ℝ)))).
Abort.

Lemma problem_23_1_xvi :
  series_converges (λ n, 1 / ((n+2)%nat * (log (((n+2)%nat : ℝ)))^2)).
Abort.

Lemma problem_23_1_xvii :
  series_converges (λ n, 1 / ((n+2)%nat^2 * log (((n+2)%nat : ℝ)))).
Abort.

Lemma problem_23_1_xviii :
  series_converges (λ n, (fact (S n))%nat / (S n)%nat^(S n)).
Abort.

Lemma problem_23_1_xix :
  series_converges (λ n, 2^(S n) * (fact (S n))%nat / (S n)%nat^(S n)).
Abort.

Lemma problem_23_1_xx :
  ~ series_converges (λ n, 3^(S n) * (fact (S n))%nat / (S n)%nat^(S n)).
Abort.
