From Lib Require Import Imports Notations Reals_util Sets Limit Continuity Tactics StdlibCompat
                        Derivative Integral Trigonometry Functions Interval Sums Exponential.

Import IntervalNotations SetNotations FunctionNotations DerivativeNotations LimitNotations IntegralNotations SumNotations.

Section Integral_Table.

Lemma integral_1 : forall n c, 
  n <> -1 -> 
  ∫ (fun x => x ^^ n) (0, ∞) = (fun x => 1 / (n + 1) * x ^^ (n + 1) + c).
Proof.
  intros n c H1.
  auto_int. solve_R. rewrite Rplus_minus_r. reflexivity.
Qed.

Lemma integral_2 : forall c, 
  ∫ (fun x => 1 / x) (0, ∞) = (fun x => ln x + c).
Proof.
  auto_int.
Qed.

Lemma integral_5 : forall a b c, 
  a <> 0 -> 
  ∫ (fun x => 1 / (a * x + b)) (-b/a, ∞) = (fun x => 1 / a * ln (|a * x + b|) + c).
Proof.
  auto_int.
Abort.

Lemma integral_6 : forall a c, 
  ∫ (fun x => 1 / (x + a) ^ 2) (-a, ∞) = (fun x => -1 / (x + a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_7 : forall a n c, 
  n <> -1 -> 
  ∫ (fun x => (x + a) ^^ n) (-a, ∞) = (fun x => (x + a) ^^ n * (a / (1 + n) + x / (1 + n)) + c).
Proof.
  intros a n c H1.
  auto_int. solve_R. f_equal. rewrite <- Rmult_plus_distr_l, Rplus_comm, Rmult_assoc. f_equal.
  rewrite <- Rpower_1 with (x := (a + x)) at 2; try lra. rewrite <- Rpower_plus; try lra.
  replace (n - 1 + 1) with n by lra. reflexivity.
Qed.

Lemma integral_8 : forall a n c, 
  n <> -1 -> 
  n <> -2 -> 
  ∫ (fun x => x * (x + a) ^^ n) (-a, ∞) = (fun x => (x + a) ^^ (1 + n) * (n * x + x - a) / ((n + 2) * (n + 1)) + c).
Proof.
  intros a n c H1 H2.
  auto_int. field_simplify. 2 : { solve_R. }
  replace (1 + n - 1) with n by lra.
  apply Rmult_eq_reg_r with (r := (n ^ 2 + 3 * n + 2)); solve_R.
  field_simplify. 
  replace ((x + a)^^(1 + n)) with ((x + a) * (x + a)^^n) by (rewrite Rpower_plus, Rpower_1; lra).
  lra.
Qed.

Lemma integral_9 : forall c, 
  ∫ (fun x => 1 / (1 + x ^ 2)) = (fun x => arctan x + c).
Proof.
  auto_int.
Qed.

Lemma integral_10 : forall a c, 
  a <> 0 -> 
  ∫ (fun x => 1 / (a ^ 2 + x ^ 2)) = (fun x => 1 / a * arctan (x / a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_11 : forall a c, 
  a <> 0 -> 
  ∫ (fun x => x / (a ^ 2 + x ^ 2)) = (fun x => 1 / 2 * ln (a ^ 2 + x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_12 : forall a c, 
  a <> 0 -> 
  ∫ (fun x => x ^ 2 / (a ^ 2 + x ^ 2)) = (fun x => x - a * arctan (x / a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_13 : forall a c, 
  a <> 0 -> 
  ∫ (fun x => x ^ 3 / (a ^ 2 + x ^ 2)) = (fun x => 1 / 2 * x ^ 2 - 1 / 2 * a ^ 2 * ln (a ^ 2 + x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_14 : forall a b c0 c, 
  a > 0 -> 
  4 * a * c0 - b ^ 2 > 0 -> 
  ∫ (fun x => 1 / (a * x ^ 2 + b * x + c0)) = (fun x => 2 / √(4 * a * c0 - b ^ 2) * arctan ((2 * a * x + b) / √(4 * a * c0 - b ^ 2)) + c).
Proof.
  intros a b c0 c H1 H2.
  auto_int. field_simplify.
  2 : {
    assert (H3 : 4 * a * (a * (x * x) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
    intro H4.
    rewrite H4 in H3.
    field_simplify in H3.
    assert (H5 : 4 * a ^ 2 * x ^ 2 + 4 * a * x * b + 4 * a * c0 = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by ring.
    rewrite H5 in H3.
    pose proof pow2_ge_0 (2 * a * x + b). lra.
  }
Abort.

Lemma integral_15 : forall a b c, 
  a <> b -> 
  ∫ (fun x => 1 / ((x + a) * (x + b))) (Rmax (-a) (-b), ∞) = (fun x => 1 / (b - a) * (ln (a + x) - ln (b + x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_16 : forall a c, 
  ∫ (fun x => x / (x + a) ^ 2) (-a, ∞) = (fun x => a / (a + x) + ln (a + x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_17 : forall a b c0 c, 
  a > 0 -> 
  4 * a * c0 - b ^ 2 > 0 -> 
  ∫ (fun x => x / (a * x ^ 2 + b * x + c0)) = (fun x => ln (a * x ^ 2 + b * x + c0) / (2 * a) - b / (a * √(4 * a * c0 - b ^ 2)) * arctan ((2 * a * x + b) / √(4 * a * c0 - b ^ 2)) + c).
Proof.
  intros a b c0 c H1 H2.
  auto_int. 
Abort.

Lemma integral_18 : forall a c, 
  ∫ (fun x => √(x - a)) (a, ∞) = (fun x => 2 / 3 * (x - a) ^^ (3 / 2) + c).
Proof.
  auto_int. field_simplify.
  replace (3 / 2 - 1) with (1 / 2) by lra.
  apply Rpower_sqrt; solve_R.
Qed.

Lemma integral_19_plus : forall a c, 
  ∫ (fun x => 1 / √(x + a)) (-a, ∞) = (fun x => 2 * √(x + a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_19_minus : forall a c, 
  ∫ (fun x => 1 / √(x - a)) (a, ∞) = (fun x => 2 * √(x - a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_20 : forall a c, 
  ∫ (fun x => 1 / √(a - x)) (-∞, a) = (fun x => -2 * √(a - x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_21 : forall a c, 
  ∫ (fun x => x * √(x - a)) (a, ∞) = (fun x => 2 / 3 * a * (x - a) ^^ (3 / 2) + 2 / 5 * (x - a) ^^ (5 / 2) + c).
Proof.
  auto_int. field_simplify.
  assert (H1 : 0 < x - a) by solve_R.
  replace (3 / 2 - 1) with (1 / 2) by lra.
  replace (5 / 2 - 1) with (1 + 1 / 2) by lra.
  rewrite Rpower_plus; auto.
  rewrite Rpower_1; try lra.
  repeat rewrite Rpower_sqrt; auto.
  lra.
Qed.

Lemma integral_22 : forall a b c, 
a > 0 -> 
∫ (fun x => √(a * x + b)) (-b/a, ∞) = (fun x => (2 * b / (3 * a) + 2 * x / 3) * √(b + a * x) + c).
Proof.
  intros a b c H1.
  auto_int.
  - solve_R. apply Rmult_lt_compat_r with (r := a) in H; field_simplify in H; nra.
  - assert (H2 : a * x + b > 0).
    { solve_R. apply Rmult_lt_compat_r with (r := a) in H; field_simplify in H; nra. }
    pose proof sqrt_lt_R0 (b + a * x) ltac:(lra) as H3.
    field_simplify; try lra.
    apply Rmult_eq_reg_r with (r := (54 * √(b + a * x))); try lra. field_simplify; try lra.
    replace (a * x + b) with (b + a * x) by lra.
    rewrite pow2_sqrt; try lra.
    replace (54 * √(b + a * x) * √(b + a * x)) with (54 * (b + a * x)).
    2 : { rewrite Rmult_assoc, sqrt_sqrt; nra. }
    lra.
Qed.

Lemma integral_23 : forall a b c, 
a > 0 -> 
∫ (fun x => (a * x + b) ^^ (3 / 2)) (-b/a, ∞) = (fun x => √(b + a * x) * (2 * b ^ 2 / (5 * a) + 4 * b * x / 5 + 2 * a * x ^ 2 / 5) + c).
Proof.
  intros a b c H1.
  auto_int.
  - solve_R. apply Rmult_lt_compat_r with (r := a) in H; field_simplify in H; nra.
  - assert (H2 : a * x + b > 0).
    { solve_R. apply Rmult_lt_compat_r with (r := a) in H; field_simplify in H; nra. }
    pose proof sqrt_lt_R0 (b + a * x) ltac:(lra) as H3.
    replace (3 / 2) with (1 + 1 / 2) by lra.
    rewrite Rpower_plus; auto.
    rewrite Rpower_1; try lra.
    rewrite Rpower_sqrt; auto.
    replace (a * x + b) with (b + a * x) by lra.
    field_simplify; try lra.
    replace (√(b + a * x) ^ 2) with (√(b + a * x) * √(b + a * x)) by ring.
    repeat rewrite sqrt_sqrt; try lra.
    apply Rmult_eq_reg_r with (r := 250 * √(b + a * x)); try lra.
    field_simplify; try lra.
    rewrite pow2_sqrt; lra.
Qed.

Lemma integral_24_plus : forall a c, 
a > 0 -> 
∫ (fun x => x / √(x + a)) (-a, ∞) = (fun x => 2 / 3 * (x - 2 * a) * √(x + a) + c).
Proof.
  intros a c H1.
  auto_int.
  solve_R.
  - rewrite Rmult_1_r, sqrt_sqrt; solve_R.
  - pose proof sqrt_lt_R0 (x + a) ltac:(lra). lra.
Qed.

Lemma integral_24_minus : forall a c, 
a > 0 -> 
∫ (fun x => x / √(x - a)) (a, ∞) = (fun x => 2 / 3 * (x + 2 * a) * √(x - a) + c).
Proof.
  intros a c H1.
  auto_int.
  solve_R.
  - rewrite Rmult_1_r, sqrt_sqrt; solve_R.
  - pose proof sqrt_lt_R0 (x - a) ltac:(lra). lra.
Qed.

Lemma integral_25 : forall a c, 
a > 0 -> 
∫ (fun x => √(x / (a - x))) (0, a) = (fun x => - √(x) * √(a - x) - a * arctan (√(x) * √(a - x) / (x - a)) + c).
Proof.
  auto_int. field_simplify.
Abort.

Lemma integral_26 : forall a c, 
a > 0 -> 
∫ (fun x => √(x / (x + a))) (0, ∞) = (fun x => √(x) * √(x + a) - a * ln (√(x) + √(x + a)) + c).
Proof. 
  auto_int.
  - pose proof sqrt_lt_R0 x ltac:(solve_R) as H3.
    pose proof sqrt_lt_R0 (x + a) ltac:(solve_R) as H4.
    lra.
  - admit.
Abort.

Lemma integral_27 : forall a b c, 
a > 0 -> 
∫ (fun x => x * √(a * x + b)) (-b/a, ∞) = (fun x => (-4 * b ^ 2 / (15 * a ^ 2) + 2 * b * x / (15 * a) + 2 * x ^ 2 / 5) * √(b + a * x) + c).
Proof.
  auto_int.
  - solve_R. apply Rmult_lt_compat_r with (r := a) in H0; field_simplify in H0; nra.
  - assert (H1 : b + a * x > 0).
    { solve_R. apply Rmult_lt_compat_r with (r := a) in H0; field_simplify in H0; nra. }
    assert (H2 : √(b + a * x) > 0) by (apply sqrt_lt_R0; lra).
    assert (H3 : √(b + a * x) ≠ 0) by lra.
    replace (a * x + b) with (b + a * x) by ring.
    apply Rmult_eq_reg_r with (r := 2 * √(b + a * x)); try nra.
    repeat rewrite sqrt_sqrt; try lra.
    field_simplify; solve_R.
Abort.

Lemma integral_28 : forall a b c, 
a > 0 -> b > 0 -> 
∫ (fun x => √(x) * √(a * x + b)) (0, ∞) = (fun x => (b * √(x) / (4 * a) + x ^^ (3 / 2) / 2) * √(b + a * x) - b ^ 2 * ln (2 * √(a) * √(x) + 2 * √(b + a * x)) / (4 * a ^^ (3 / 2)) + c).
Proof.
  auto_int.
  - assert (H4 : √a > 0) by (apply sqrt_lt_R0; lra).
    assert (H5 : √x > 0) by (apply sqrt_lt_R0; solve_R).
    assert (H6 : √(b + a * x) > 0) by (apply sqrt_lt_R0; solve_R).
    nra.
  - assert (H2 : a^^(3 / 2) > 0) by (apply Rpower_gt_0; lra). lra.
  - admit.
Abort.

Lemma integral_29 : forall a b c, 
a > 0 -> b > 0 -> 
∫ (fun x => x ^^ (3 / 2) * √(a * x + b)) (0, ∞) = (fun x => (- b ^ 2 * √(x) / (8 * a ^ 2) + b * x ^^ (3 / 2) / (12 * a) + x ^^ (5 / 2) / 3) * √(b + a * x) - b ^ 3 * ln (2 * √(a) * √(x) + 2 * √(b + a * x)) / (8 * a ^^ (5 / 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_30_plus : forall a c, 
∫ (fun x => √(x ^ 2 + a ^ 2)) = (fun x => 1 / 2 * x * √(x ^ 2 + a ^ 2) + 1 / 2 * a ^ 2 * ln (x + √(x ^ 2 + a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_30_minus : forall a c, 
a > 0 -> 
∫ (fun x => √(x ^ 2 - a ^ 2)) (a, ∞) = (fun x => 1 / 2 * x * √(x ^ 2 - a ^ 2) - 1 / 2 * a ^ 2 * ln (x + √(x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_31 : forall a c, 
a > 0 -> 
∫ (fun x => √(a ^ 2 - x ^ 2)) (-a, a) = (fun x => 1 / 2 * x * √(a ^ 2 - x ^ 2) - 1 / 2 * a ^ 2 * arctan (x * √(a ^ 2 - x ^ 2) / (x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_32_plus : forall a c, 
∫ (fun x => x * √(x ^ 2 + a ^ 2)) = (fun x => 1 / 3 * (x ^ 2 + a ^ 2) ^^ (3 / 2) + c).
Proof.
  auto_int.
Abort.

Lemma integral_32_minus : forall a c, 
a > 0 -> 
∫ (fun x => x * √(x ^ 2 - a ^ 2)) (a, ∞) = (fun x => 1 / 3 * (x ^ 2 - a ^ 2) ^^ (3 / 2) + c).
Proof.
  auto_int.
Abort.

Lemma integral_33_plus : forall a c, 
∫ (fun x => 1 / √(x ^ 2 + a ^ 2)) = (fun x => ln (x + √(x ^ 2 + a ^ 2)) + c).
Proof.
  auto_int. 
Abort.

Lemma integral_33_minus : forall a c, 
a > 0 -> 
∫ (fun x => 1 / √(x ^ 2 - a ^ 2)) (a, ∞) = (fun x => ln (x + √(x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
  - assert (H1 : x ^ 2 > a^2) by (simpl; solve_R).
    pose proof sqrt_lt_R0 (x * (x * 1) - a * (a * 1)) ltac:(solve_R); solve_R.
  - assert (H1 : x ^ 2 > a^2) by (simpl; solve_R). 
    pose proof sqrt_lt_R0 (x * (x * 1) - a * (a * 1)) ltac:(solve_R); solve_R.
    repeat rewrite Rmult_1_r in H2. solve_R.
Qed.

Lemma integral_34 : forall a c, 
a > 0 -> 
∫ (fun x => 1 / √(a ^ 2 - x ^ 2)) (-a, a) = (fun x => arcsin (x / a) + c).
Proof.
  auto_int.
Abort.

Lemma integral_35_plus : forall a c, 
∫ (fun x => x / √(x ^ 2 + a ^ 2)) = (fun x => √(x ^ 2 + a ^ 2) + c).
Proof.
  auto_int.
Abort.

Lemma integral_35_minus : forall a c, 
a > 0 -> 
∫ (fun x => x / √(x ^ 2 - a ^ 2)) (a, ∞) = (fun x => √(x ^ 2 - a ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_36 : forall a c, 
a > 0 -> 
∫ (fun x => x / √(a ^ 2 - x ^ 2)) (-a, a) = (fun x => - √(a ^ 2 - x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_37_plus : forall a c, 
a > 0 -> 
∫ (fun x => x ^ 2 / √(x ^ 2 + a ^ 2)) = (fun x => 1 / 2 * x * √(x ^ 2 + a ^ 2) - 1 / 2 * a ^ 2 * ln (x + √(x ^ 2 + a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_37_minus : forall a c, 
a > 0 -> 
∫ (fun x => x ^ 2 / √(x ^ 2 - a ^ 2)) (a, ∞) = (fun x => 1 / 2 * x * √(x ^ 2 - a ^ 2) + 1 / 2 * a ^ 2 * ln (x + √(x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_38 : forall a c, 
a > 0 -> 
∫ (fun x => x ^ 2 / √(a ^ 2 - x ^ 2)) (-a, a) = (fun x => - 1 / 2 * x * √(a ^ 2 - x ^ 2) - 1 / 2 * a ^ 2 * arctan (x * √(a ^ 2 - x ^ 2) / (x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_39 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (fun x => √(a * x ^ 2 + b * x + c0)) = (fun x => (b / (4 * a) + x / 2) * √(a * x ^ 2 + b * x + c0) + (4 * a * c0 - b ^ 2) / (8 * a ^^ (3 / 2)) * ln ((2 * a * x + b) / √(a) + 2 * √(a * x ^ 2 + b * x + c0)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_40 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (fun x => x * √(a * x ^ 2 + b * x + c0)) = (fun x => (x ^ 3 / 3 + b * x / (12 * a) + (8 * a * c0 - 3 * b ^ 2) / (24 * a ^ 2)) * √(a * x ^ 2 + b * x + c0) - b * (4 * a * c0 - b ^ 2) / (16 * a ^^ (5 / 2)) * ln ((2 * a * x + b) / √(a) + 2 * √(a * x ^ 2 + b * x + c0)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_41 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (fun x => 1 / √(a * x ^ 2 + b * x + c0)) = (fun x => 1 / √(a) * ln ((2 * a * x + b) / √(a) + 2 * √(a * x ^ 2 + b * x + c0)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_42 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (fun x => x / √(a * x ^ 2 + b * x + c0)) = (fun x => 1 / a * √(a * x ^ 2 + b * x + c0) - b / (2 * a ^^ (3 / 2)) * ln ((2 * a * x + b) / √(a) + 2 * √(a * x ^ 2 + b * x + c0)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_43 : forall c, 
∫ (fun x => ln x) (0, ∞) = (fun x => x * ln x - x + c).
Proof.
  auto_int.
Qed.

Lemma integral_44 : forall a c, 
a > 0 -> 
∫ (fun x => ln (a * x) / x) (0, ∞) = (fun x => 1 / 2 * (ln (a * x)) ^ 2 + c).
Proof.
  auto_int.
Qed.

Lemma integral_45 : forall a b c, 
a > 0 -> 
∫ (fun x => ln (a * x + b)) (-b/a, ∞) = (fun x => (a * x + b) / a * ln (a * x + b) - x + c).
Proof.
  auto_int.
Abort.

Lemma integral_46 : forall a b c, 
a <> 0 -> 
b <> 0 -> 
∫ (fun x => ln (a ^ 2 * x ^ 2 + b ^ 2)) = (fun x => x * ln (a ^ 2 * x ^ 2 + b ^ 2) + 2 * b / a * arctan (a * x / b) - 2 * x + c).
Proof.
  auto_int.
Qed.

Lemma integral_47 : forall a b c, 
a > 0 -> 
b > 0 -> 
∫ (fun x => ln (a ^ 2 - b ^ 2 * x ^ 2)) (-a/b, a/b) = (fun x => x * ln (a ^ 2 - b ^ 2 * x ^ 2) + 2 * a / b * arctan (b * x / a) - 2 * x + c).
Proof.
  auto_int.
Abort.

Lemma integral_48 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (fun x => ln (a * x ^ 2 + b * x + c0)) = (fun x => 1 / a * √(4 * a * c0 - b ^ 2) * arctan ((2 * a * x + b) / √(4 * a * c0 - b ^ 2)) - 2 * x + (b / (2 * a) + x) * ln (a * x ^ 2 + b * x + c0) + c).
Proof.
  auto_int.
Abort.

Lemma integral_49 : forall a b c, 
a > 0 -> 
∫ (fun x => x * ln (a * x + b)) (-b/a, ∞) = (fun x => b / (2 * a) * x - 1 / 4 * x ^ 2 + 1 / 2 * (x ^ 2 - b ^ 2 / a ^ 2) * ln (a * x + b) + c).
Proof.
  auto_int.
Abort.

Lemma integral_50 : forall a b c, 
a > 0 -> 
b > 0 -> 
∫ (fun x => x * ln (a ^ 2 - b ^ 2 * x ^ 2)) (-a/b, a/b) = (fun x => - 1 / 2 * x ^ 2 + 1 / 2 * (x ^ 2 - a ^ 2 / b ^ 2) * ln (a ^ 2 - b ^ 2 * x ^ 2) + c).
Proof.
  auto_int.
Abort.

Lemma integral_51 : forall a c, 
a <> 0 -> 
∫ (fun x => exp (a * x)) = (fun x => 1 / a * exp (a * x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_53 : forall c, 
∫ (fun x => x * exp x) = (fun x => (x - 1) * exp x + c).
Proof.
  auto_int.
Qed.

Lemma integral_54 : forall a c, 
a <> 0 -> 
∫ (fun x => x * exp (a * x)) = (fun x => (x / a - 1 / a ^ 2) * exp (a * x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_55 : forall c, 
∫ (fun x => x ^ 2 * exp x) = (fun x => exp x * (x ^ 2 - 2 * x + 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_56 : forall a c, 
a <> 0 -> 
∫ (fun x => x ^ 2 * exp (a * x)) = (fun x => exp (a * x) * (x ^ 2 / a - 2 * x / a ^ 2 + 2 / a ^ 3) + c).
Proof.
  auto_int.
Qed.

Lemma integral_57 : forall c, 
∫ (fun x => x ^ 3 * exp x) = (fun x => exp x * (x ^ 3 - 3 * x ^ 2 + 6 * x - 6) + c).
Proof.
  auto_int.
Qed.

Lemma integral_60 : forall c, 
∫ (fun x => sin x) = (fun x => - cos x + c).
Proof.
  auto_int.
Qed.

Lemma integral_61 : forall c, 
∫ (fun x => (sin x) ^ 2) = (fun x => x / 2 - 1 / 4 * sin (2 * x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_62 : forall c, 
∫ (fun x => (sin x) ^ 3) = (fun x => - 3 / 4 * cos x + 1 / 12 * cos (3 * x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_63 : forall c, 
∫ (fun x => cos x) = (fun x => sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_64 : forall c, 
∫ (fun x => (cos x) ^ 2) = (fun x => x / 2 + 1 / 4 * sin (2 * x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_65 : forall c, 
∫ (fun x => (cos x) ^ 3) = (fun x => 3 / 4 * sin x + 1 / 12 * sin (3 * x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_66 : forall c, 
∫ (fun x => sin x * cos x) = (fun x => -1 / 2 * (cos x) ^ 2 + c).
Proof.
  auto_int.
Qed.

Lemma integral_67 : forall c, 
∫ (fun x => (sin x) ^ 2 * cos x) = (fun x => 1 / 4 * sin x - 1 / 12 * sin (3 * x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_68 : forall c, 
∫ (fun x => sin x * (cos x) ^ 2) = (fun x => -1 / 4 * cos x - 1 / 12 * cos (3 * x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_69 : forall c, 
∫ (fun x => (sin x) ^ 2 * (cos x) ^ 2) = (fun x => x / 8 - 1 / 32 * sin (4 * x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_70 : forall c, 
∫ (fun x => tan x) = (fun x => - ln (cos x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_71 : forall c, 
∫ (fun x => (tan x) ^ 2) = (fun x => - x + tan x + c).
Proof.
  auto_int.
Abort.

Lemma integral_72 : forall c, 
∫ (fun x => (tan x) ^ 3) = (fun x => ln (cos x) + 1 / 2 * (sec x) ^ 2 + c).
Proof.
  auto_int.
Abort.

Lemma integral_73 : forall c, 
∫ (fun x => sec x) = (fun x => ln (sec x + tan x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_74 : forall c, 
∫ (fun x => (sec x) ^ 2) = (fun x => tan x + c).
Proof.
  auto_int.
Abort.

Lemma integral_75 : forall c, 
∫ (fun x => (sec x) ^ 3) = (fun x => 1 / 2 * sec x * tan x + 1 / 2 * ln (sec x + tan x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_76 : forall c, 
∫ (fun x => sec x * tan x) = (fun x => sec x + c).
Proof.
  auto_int.
Abort.

Lemma integral_77 : forall c, 
∫ (fun x => (sec x) ^ 2 * tan x) = (fun x => 1 / 2 * (sec x) ^ 2 + c).
Proof.
  auto_int.
Abort.

Lemma integral_78 : forall n c, 
n <> 0 -> 
∫ (fun x => (sec x) ^^ n * tan x) = (fun x => 1 / n * (sec x) ^^ n + c).
Proof.
  auto_int.
Abort.

Lemma integral_79 : forall c, 
∫ (fun x => csc x) = (fun x => ln (csc x - cot x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_80 : forall c, 
∫ (fun x => (csc x) ^ 2) = (fun x => - cot x + c).
Proof.
  auto_int.
Abort.

Lemma integral_81 : forall c, 
∫ (fun x => (csc x) ^ 3) = (fun x => -1 / 2 * cot x * csc x + 1 / 2 * ln (csc x - cot x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_82 : forall n c, 
n <> 0 -> 
∫ (fun x => (csc x) ^^ n * cot x) = (fun x => -1 / n * (csc x) ^^ n + c).
Proof.
  auto_int.
Abort.

Lemma integral_83 : forall c, 
∫ (fun x => sec x * csc x) = (fun x => ln (tan x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_84 : forall c, 
∫ (fun x => x * cos x) = (fun x => cos x + x * sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_85 : forall a c, 
a <> 0 -> 
∫ (fun x => x * cos (a * x)) = (fun x => 1 / a ^ 2 * cos (a * x) + 1 / a * x * sin (a * x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_86 : forall c, 
∫ (fun x => x ^ 2 * cos x) = (fun x => 2 * x * cos x + (x ^ 2 - 2) * sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_87 : forall a c, 
a <> 0 -> 
∫ (fun x => x ^ 2 * cos (a * x)) = (fun x => 2 / a ^ 2 * x * cos (a * x) + (a ^ 2 * x ^ 2 - 2) / a ^ 3 * sin (a * x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_90 : forall c, 
∫ (fun x => x * sin x) = (fun x => - x * cos x + sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_91 : forall a c, 
a <> 0 -> 
∫ (fun x => x * sin (a * x)) = (fun x => - x / a * cos (a * x) + 1 / a ^ 2 * sin (a * x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_92 : forall c, 
∫ (fun x => x ^ 2 * sin x) = (fun x => (2 - x ^ 2) * cos x + 2 * x * sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_93 : forall a c, 
a <> 0 -> 
∫ (fun x => x ^ 3 * sin (a * x)) = (fun x => (3 * a ^ 2 * x ^ 2 - 6) / a ^ 4 * sin (a * x) + (6 * x - a ^ 2 * x ^ 3) / a ^ 3 * cos (a * x) + c).
Proof.
  auto_int. all: repeat (apply Rmult_integral_contrapositive; split); solve_R.
Qed.

Lemma integral_95 : forall c, 
∫ (fun x => exp x * sin x) = (fun x => 1 / 2 * exp x * (sin x - cos x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_96 : forall a b c, 
b ^ 2 + a ^ 2 <> 0 -> 
∫ (fun x => exp (b * x) * sin (a * x)) = (fun x => 1 / (b ^ 2 + a ^ 2) * exp (b * x) * (b * sin (a * x) - a * cos (a * x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_97 : forall c, 
∫ (fun x => exp x * cos x) = (fun x => 1 / 2 * exp x * (sin x + cos x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_98 : forall a b c, 
b ^ 2 + a ^ 2 <> 0 -> 
∫ (fun x => exp (b * x) * cos (a * x)) = (fun x => 1 / (b ^ 2 + a ^ 2) * exp (b * x) * (a * sin (a * x) + b * cos (a * x)) + c).
Proof.
  auto_int.
Qed.  

Lemma integral_99 : forall c, 
∫ (fun x => x * exp x * sin x) = (fun x => 1 / 2 * exp x * (cos x - x * cos x + x * sin x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_100 : forall c, 
∫ (fun x => x * exp x * cos x) = (fun x => 1 / 2 * exp x * (x * cos x - sin x + x * sin x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_101 : forall c, 
∫ (fun x => cosh x) = (fun x => sinh x + c).
Proof.
  auto_int.
Abort.

Lemma integral_102 : forall a b c, 
a ^ 2 - b ^ 2 <> 0 -> 
∫ (fun x => exp (a * x) * cosh (b * x)) = (fun x => exp (a * x) / (a ^ 2 - b ^ 2) * (a * cosh (b * x) - b * sinh (b * x)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_103 : forall c, 
∫ (fun x => sinh x) = (fun x => cosh x + c).
Proof.
  auto_int.
Abort.

Lemma integral_104 : forall a b c, 
a ^ 2 - b ^ 2 <> 0 -> 
∫ (fun x => exp (a * x) * sinh (b * x)) = (fun x => exp (a * x) / (a ^ 2 - b ^ 2) * (- b * cosh (b * x) + a * sinh (b * x)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_105 : forall c, 
∫ (fun x => exp x * tanh x) = (fun x => exp x - 2 * arctan (exp x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_106 : forall a c, 
a <> 0 -> 
∫ (fun x => tanh (a * x)) = (fun x => 1 / a * ln (cosh (a * x)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_107 : forall a b c, 
a ^ 2 + b ^ 2 <> 0 -> 
∫ (fun x => cos (a * x) * cosh (b * x)) = (fun x => 1 / (a ^ 2 + b ^ 2) * (a * sin (a * x) * cosh (b * x) + b * cos (a * x) * sinh (b * x)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_108 : forall a b c, 
a ^ 2 + b ^ 2 <> 0 -> 
∫ (fun x => cos (a * x) * sinh (b * x)) = (fun x => 1 / (a ^ 2 + b ^ 2) * (b * cos (a * x) * cosh (b * x) + a * sin (a * x) * sinh (b * x)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_109 : forall a b c, 
a ^ 2 + b ^ 2 <> 0 -> 
∫ (fun x => sin (a * x) * cosh (b * x)) = (fun x => 1 / (a ^ 2 + b ^ 2) * (- a * cos (a * x) * cosh (b * x) + b * sin (a * x) * sinh (b * x)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_110 : forall a b c, 
a ^ 2 + b ^ 2 <> 0 -> 
∫ (fun x => sin (a * x) * sinh (b * x)) = (fun x => 1 / (a ^ 2 + b ^ 2) * (b * cosh (b * x) * sin (a * x) - a * cos (a * x) * sinh (b * x)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_111 : forall a c, 
a <> 0 -> 
∫ (fun x => sinh (a * x) * cosh (a * x)) = (fun x => (- 2 * a * x + sinh (2 * a * x)) / (4 * a) + c).
Proof.
  auto_int.
Abort.

Lemma integral_112 : forall a b c, 
b ^ 2 - a ^ 2 <> 0 -> 
∫ (fun x => sinh (a * x) * cosh (b * x)) = (fun x => (b * cosh (b * x) * sinh (a * x) - a * cosh (a * x) * sinh (b * x)) / (b ^ 2 - a ^ 2) + c).
Proof.
  auto_int.
Abort.

End Integral_Table.
