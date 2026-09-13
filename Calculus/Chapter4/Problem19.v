From Calculus.Chapter4 Require Import Prelude.

(* p. 73: describe these graphs as fully as possible.
   Convention made explicit: digits are numbered AFTER the decimal point,
   starting at 1; for negative x use the digits of |x| and retain the sign
   in (v). Positive terminating magnitudes use the expansion ending in 9s.
   Zero has only its all-zero magnitude expansion. See REVIEW.md. *)
Local Definition strict_decimal_prefix (x : ℝ) (n : ℕ) : ℤ :=
  if Req_EM_T x 0 then 0%Z else (- Zfloor (- (10^n * |x|)) - 1)%Z.
Local Definition decimal_digit (x : ℝ) (n : ℕ) : ℕ :=
  Z.to_nat (Z.modulo (strict_decimal_prefix x n) 10).
Local Definition digit_places (x : ℝ) (d : ℕ) : Ensemble ℕ :=
  λ n, (1 <= n)%nat /\ decimal_digit x n = d.
Local Definition first_digit_at (x : ℝ) (d n : ℕ) : Prop :=
  n ∈ digit_places x d /\ ∀ k, (1 <= k < n)%nat -> decimal_digit x k <> d.

(* (i), (ii): first and second fractional digits. *)
Definition problem_4_19_i := graph (λ x, ((decimal_digit x 1)%nat : ℝ)).
Definition problem_4_19_ii := graph (λ x, ((decimal_digit x 2)%nat : ℝ)).

(* (iii): finite count of 7s, otherwise zero. *)
Definition problem_4_19_iii : Ensemble point := locus (λ x y,
  (∃ n : ℕ, card (digit_places x 7) = n /\ y = (n : ℝ)) \/
  (Infinite_set (digit_places x 7) /\ y = 0)).

(* (iv): zero for finitely many 7s, one for infinitely many. *)
Definition problem_4_19_iv : Ensemble point := locus (λ x y,
  (Finite_set (digit_places x 7) /\ y = 0) \/
  (Infinite_set (digit_places x 7) /\ y = 1)).

(* (v): replace all digits after the first 7 by zeros; no 7 leaves x unchanged. *)
Definition problem_4_19_v : Ensemble point := locus (λ x y,
  ((∀ n, (1 <= n)%nat -> decimal_digit x n <> 7%nat) /\ y=x) \/
  ∃ n : ℕ, first_digit_at x 7 n /\
    y = (if Rlt_dec x 0 then -1 else 1) * (strict_decimal_prefix x n)%Z / 10^n).

(* (vi): first position of 1, or zero if 1 never occurs. *)
Definition problem_4_19_vi : Ensemble point := locus (λ x y,
  ((∀ (n : ℕ), (1 <= n)%nat -> decimal_digit x n <> 1%nat) /\ y=0) \/
  ∃ n : ℕ, first_digit_at x 1 n /\ y=(n : ℝ)).
