From Lib Require Export Imports Limit Continuity Reals_util Notations Rational Sets Derivative Trigonometry Inverse Exponential Integral Tactics Interval Functions Sums Binomial Polynomial Taylor.
Export LimitNotations SetNotations IntervalNotations FunctionNotations DerivativeNotations SumNotations Choose_Notations IntegralNotations.
Open Scope R_scope.

(* Improper endpoints are limits of proper integrals, taken separately. *)
Definition improper_left_19 (a b : R) (f : R -> R) (L : R) : Prop :=
  a < b /\ (∀ c, a < c < b -> integrable_on c b f) /\
  right_limit (λ c, ∫ c b f) a L.
Definition improper_right_19 (a b : R) (f : R -> R) (L : R) : Prop :=
  a < b /\ (∀ c, a < c < b -> integrable_on a c f) /\
  left_limit (λ c, ∫ a c f) b L.
Definition improper_both_19 (a b : R) (f : R -> R) (L : R) : Prop :=
  ∃ c L1 L2, a < c < b /\ improper_left_19 a c f L1 /\
    improper_right_19 c b f L2 /\ L = L1 + L2.
Definition improper_positive_19 (f : R -> R) (L : R) : Prop :=
  ∃ L1 L2, improper_left_19 0 1 f L1 /\
    improper_integral_pinf 1 f L2 /\ L = L1 + L2.
Definition gamma_value_19 (x L : R) : Prop :=
  improper_positive_19 (λ t, exp (-t) * t ^^ (x-1)) L.
Definition gamma_19 (x : R) : R := epsilon (inhabits 0) (gamma_value_19 x).
Fixpoint product_19 (n : nat) (f : nat -> R) : R :=
  match n with O => 1 | S k => product_19 k f * f (S k) end.
Definition sequence_limit_19 (u : nat -> R) (L : R) :=
  ∀ ε, 0 < ε -> ∃ N, ∀ n, (N <= n)%nat -> Rabs (u n-L) < ε.

(* Unlike sum_f, this sum is zero when there are no terms. *)
Definition sum_first_19 (n : nat) (f : nat -> R) : R :=
  match n with O => 0 | S k => sum_f_R0 (λ i, f (S i)) k end.
