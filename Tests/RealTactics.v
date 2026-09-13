From Lib Require Import RealTactics.
Open Scope Real_scope.

Example real_numerals : 2 + 3 = 5.
Proof. solve_real. Qed.

Example real_negative_numerals : -12 + 5 = -7.
Proof. solve_real. Qed.

Example real_linear : forall x y : Real,
  2 * x + 3 <= y -> y < 7 -> x < 2.
Proof. real_lra. Qed.

Example real_equation : forall x : Real, 3 * x + 2 = 11 -> x = 3.
Proof. solve_real. Qed.

Example real_square_nonnegative : forall x : Real, 0 <= x ^ 2.
Proof. real_nra. Qed.

Example real_polynomial : forall x y : Real,
  (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2.
Proof. real_nra. Qed.

Example real_positive_product : forall x y : Real,
  x > 0 -> y > 0 -> x * y > 0.
Proof. real_nra. Qed.

Example real_reciprocal : forall x : Real, x <> 0 -> x / x = 1.
Proof. real_field. Qed.

Example real_denominator : forall x : Real,
  0 <= x -> 1 / (x + 1) + x / (x + 1) = 1.
Proof. solve_real. Qed.

Example real_inverse_zero : /0 = 0.
Proof. solve_real. Qed.

Example real_inverse_positive : forall x : Real, 0 < x -> 0 < /x.
Proof. solve_real. Qed.

Example real_inverse_bound : forall x : Real, 1 < x -> /x < 1.
Proof. solve_real. Qed.

Example real_absolute_value : forall x : Real, x <= Rabs x.
Proof. solve_real. Qed.

Example real_triangle : forall x y : Real,
  Rabs (x + y) <= Rabs x + Rabs y.
Proof. solve_real. Qed.

Example real_rational : Real_of_Q (1#2)%Q + Real_of_Q (1#3)%Q = Real_of_Q (5#6)%Q.
Proof. solve_real. Qed.

Example real_field_order : forall x y : Real,
  Field.le x y -> Field.gt (y + 1) x.
Proof. real_lra. Qed.

Example real_manual_transfer : forall x : Real, x + 1 > x.
Proof. real_lra. Qed.

Example real_ring : forall x y : Real, (x + y) * (x - y) = x * x - y * y.
Proof. intros. field. Qed.

Example real_native_field : forall x : Real, x <> 0 -> x / x = 1.
Proof. intros x Hx. field. exact Hx. Qed.

Example real_solver_rejects_false_claims : True.
Proof.
  Fail assert (H : (1 : Real) = 0) by solve_real.
  Fail assert (H : forall x : Real, x / x = 1) by solve_real.
  Fail assert (H : forall x : Real, x > 0) by real_lra.
  exact I.
Qed.
