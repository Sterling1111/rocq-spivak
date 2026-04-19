From Lib Require Import Imports Notations Reals_util Sets Limit Continuity Tactics StdlibCompat
                        Derivative Integral Trigonometry Functions Interval Sums Exponential.

Import IntervalNotations SetNotations FunctionNotations DerivativeNotations LimitNotations IntegralNotations SumNotations.

Section Integral_Table.

Lemma integral_1 : forall n c, 
  n <> -1 -> 
  ∫ (λ x, x ^^ n) (0, ∞) = (λ x, 1 / (n + 1) * x ^^ (n + 1) + c).
Proof.
  intros n c H1.
  auto_int. solve_R. rewrite Rplus_minus_r. reflexivity.
Qed.

Lemma integral_2 : forall c, 
  ∫ (λ x, 1 / x) (0, ∞) = (λ x, ln x + c).
Proof.
  auto_int.
Qed.

Lemma integral_5 : forall a b c, 
  a <> 0 -> 
  ∫ (λ x, 1 / (a * x + b)) (-b/a, ∞) = (λ x, 1 / a * ln (|a * x + b|) + c).
Proof.
  auto_int.
Abort.

Lemma integral_6 : forall a c, 
  ∫ (λ x, 1 / (x + a) ^ 2) (-a, ∞) = (λ x, -1 / (x + a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_7 : forall a n c, 
  n <> -1 -> 
  ∫ (λ x, (x + a) ^^ n) (-a, ∞) = (λ x, (x + a) ^^ n * (a / (1 + n) + x / (1 + n)) + c).
Proof.
  intros a n c H1.
  auto_int. solve_R. f_equal. rewrite <- Rmult_plus_distr_l, Rplus_comm, Rmult_assoc. f_equal.
  rewrite <- Rpower_1 with (x := (a + x)) at 2; try lra. rewrite <- Rpower_plus; try lra.
  replace (n - 1 + 1) with n by lra. reflexivity.
Qed.

Lemma integral_8 : forall a n c, 
  n <> -1 -> 
  n <> -2 -> 
  ∫ (λ x, x * (x + a) ^^ n) (-a, ∞) = (λ x, (x + a) ^^ (1 + n) * (n * x + x - a) / ((n + 2) * (n + 1)) + c).
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
  ∫ (λ x, 1 / (1 + x ^ 2)) = (λ x, arctan x + c).
Proof.
  auto_int.
Qed.

Lemma integral_10 : forall a c, 
  a <> 0 -> 
  ∫ (λ x, 1 / (a ^ 2 + x ^ 2)) = (λ x, 1 / a * arctan (x / a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_11 : forall a c, 
  a <> 0 -> 
  ∫ (λ x, x / (a ^ 2 + x ^ 2)) = (λ x, 1 / 2 * ln (a ^ 2 + x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_12 : forall a c, 
  a <> 0 -> 
  ∫ (λ x, x ^ 2 / (a ^ 2 + x ^ 2)) = (λ x, x - a * arctan (x / a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_13 : forall a c, 
  a <> 0 -> 
  ∫ (λ x, x ^ 3 / (a ^ 2 + x ^ 2)) = (λ x, 1 / 2 * x ^ 2 - 1 / 2 * a ^ 2 * ln (a ^ 2 + x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_14 : forall a b c0 c, 
  a > 0 -> 
  4 * a * c0 - b ^ 2 > 0 -> 
  ∫ (λ x, 1 / (a * x ^ 2 + b * x + c0)) = (λ x, 2 / √(4 * a * c0 - b ^ 2) * arctan ((2 * a * x + b) / √(4 * a * c0 - b ^ 2)) + c).
Proof.
  intros a b c0 c H1 H2.
  auto_int. field_simplify.
  - rewrite pow2_sqrt; try lra.
    assert (H3 : 4 * a * c0 - b * b + 4 * a ^ 2 * x ^ 2 + 4 * a * x * b + b ^ 2 = 4 * a * (a * x ^ 2 + x * b + c0)) by ring.
    rewrite H3.
    assert (H4 : a * x ^ 2 + x * b + c0 <> 0).
    { assert (H5 : 4 * a * (a * (x * x) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
      replace (a * (x * x) + b * x + c0) with (a * x ^ 2 + x * b + c0) in H5 by ring.
      intro H6. rewrite H6 in H5.
      assert (H7 : 4 * a * 0 = 0) by ring. rewrite H7 in H5.
      pose proof pow2_ge_0 (2 * a * x + b). lra.
    }
    apply Rmult_eq_reg_r with (r := a * x ^ 2 + x * b + c0); try lra.
    apply Rmult_eq_reg_r with (r := 4 * a * (a * x ^ 2 + x * b + c0)); try nra.
    field_simplify; try nra.
  - assert (H3 : 4 * a * (a * (x * x) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
    replace (a * (x * x) + b * x + c0) with (a * x ^ 2 + x * b + c0) in H3 by ring.
    intro H4.
    replace (a * (x * x) + b * x + c0) with (a * x ^ 2 + x * b + c0) in H4 by ring.
    rewrite H4 in H3.
    assert (H5 : 4 * a * 0 = 0) by ring. rewrite H5 in H3.
    pose proof pow2_ge_0 (2 * a * x + b). lra.
  - split.
    + assert (H3 : 0 < √(4 * a * c0 - b * b)).
      { apply sqrt_lt_R0. lra. }
      lra.
    + pose proof pow2_ge_0 (2 * a * x + b).
      assert (H4: √(4 * a * c0 - b * b) * √(4 * a * c0 - b * b) = 4 * a * c0 - b ^ 2).
      { rewrite sqrt_sqrt; lra. }
      nra.
Qed.

Lemma integral_15 : forall a b c, 
  a <> b -> 
  ∫ (λ x, 1 / ((x + a) * (x + b))) (Rmax (-a) (-b), ∞) = (λ x, 1 / (b - a) * (ln (a + x) - ln (b + x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_16 : forall a c, 
  ∫ (λ x, x / (x + a) ^ 2) (-a, ∞) = (λ x, a / (a + x) + ln (a + x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_17 : forall a b c0 c, 
  a > 0 -> 
  4 * a * c0 - b ^ 2 > 0 -> 
  ∫ (λ x, x / (a * x ^ 2 + b * x + c0)) = (λ x, ln (a * x ^ 2 + b * x + c0) / (2 * a) - b / (a * √(4 * a * c0 - b ^ 2)) * arctan ((2 * a * x + b) / √(4 * a * c0 - b ^ 2)) + c).
Proof.
  intros a b c0 c H1 H2.
  auto_int. 
  - assert (H3 : 4 * a * (a * (x * (x * 1)) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
    pose proof pow2_ge_0 (2 * a * x + b).
    nra.
  - field_simplify.
    + rewrite pow2_sqrt; try lra.
      assert (H3 : a * x ^ 2 + x * b + c0 <> 0).
      { assert (H5 : 4 * a * (a * (x * x) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
        replace (a * (x * x) + b * x + c0) with (a * x ^ 2 + x * b + c0) in H5 by ring.
        pose proof pow2_ge_0 (2 * a * x + b). nra.
      }
      assert (H4 : 8 * a ^ 4 * x ^ 4 + 16 * a ^ 3 * x ^ 3 * b + 8 * a ^ 3 * x ^ 2 * c0 + 10 * a ^ 2 * x ^ 2 * b ^ 2 + 2 * a ^ 2 * x ^ 2 * (4 * a * c0 - b * b) + 8 * a ^ 2 * x * b * c0 + 2 * a * x * b ^ 3 + 2 * a * x * b * (4 * a * c0 - b * b) + 2 * a * b ^ 2 * c0 + 2 * a * c0 * (4 * a * c0 - b * b) = 8 * a^2 * (a * x^2 + x * b + c0)^2) by ring.
      rewrite H4.
      assert (H5 : 8 * a ^ 3 * x ^ 3 + 8 * a ^ 2 * x ^ 2 * b + 2 * a * x * b ^ 2 + 2 * a * x * (4 * a * c0 - b * b) - 4 * a * b * c0 + b ^ 3 + b * (4 * a * c0 - b * b) = 8 * a ^ 2 * x * (a * x ^ 2 + x * b + c0)) by ring.
      rewrite H5.
      field. nra.
    + assert (H5 : 4 * a * (a * (x * x) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
      replace (a * (x * x) + b * x + c0) with (a * x ^ 2 + x * b + c0) in H5 by ring.
      pose proof pow2_ge_0 (2 * a * x + b). nra.
    + split.
      * assert (H3 : 0 < √(4 * a * c0 - b * b)). { apply sqrt_lt_R0. lra. } lra.
      * split.
        -- pose proof pow2_ge_0 (2 * a * x + b).
           assert (H4: √(4 * a * c0 - b * b) * √(4 * a * c0 - b * b) = 4 * a * c0 - b ^ 2).
           { rewrite sqrt_sqrt; lra. }
           nra.
        -- split.
           ++ lra.
           ++ assert (H5 : 4 * a * (a * (x * x) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
              replace (a * (x * x) + b * x + c0) with (a * x ^ 2 + x * b + c0) in H5 by ring.
              pose proof pow2_ge_0 (2 * a * x + b). nra.
Qed.

Lemma integral_18 : forall a c, 
  ∫ (λ x, √(x - a)) (a, ∞) = (λ x, 2 / 3 * (x - a) ^^ (3 / 2) + c).
Proof.
  auto_int. field_simplify.
  replace (3 / 2 - 1) with (1 / 2) by lra.
  apply Rpower_sqrt; solve_R.
Qed.

Lemma integral_19_plus : forall a c, 
  ∫ (λ x, 1 / √(x + a)) (-a, ∞) = (λ x, 2 * √(x + a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_19_minus : forall a c, 
  ∫ (λ x, 1 / √(x - a)) (a, ∞) = (λ x, 2 * √(x - a) + c).
Proof.
  auto_int.
Qed.

Lemma integral_20 : forall a c, 
  ∫ (λ x, 1 / √(a - x)) (-∞, a) = (λ x, -2 * √(a - x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_21 : forall a c, 
  ∫ (λ x, x * √(x - a)) (a, ∞) = (λ x, 2 / 3 * a * (x - a) ^^ (3 / 2) + 2 / 5 * (x - a) ^^ (5 / 2) + c).
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
∫ (λ x, √(a * x + b)) (-b/a, ∞) = (λ x, (2 * b / (3 * a) + 2 * x / 3) * √(b + a * x) + c).
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
∫ (λ x, (a * x + b) ^^ (3 / 2)) (-b/a, ∞) = (λ x, √(b + a * x) * (2 * b ^ 2 / (5 * a) + 4 * b * x / 5 + 2 * a * x ^ 2 / 5) + c).
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
∫ (λ x, x / √(x + a)) (-a, ∞) = (λ x, 2 / 3 * (x - 2 * a) * √(x + a) + c).
Proof.
  intros a c H1.
  auto_int.
  solve_R.
  - rewrite Rmult_1_r, sqrt_sqrt; solve_R.
  - pose proof sqrt_lt_R0 (x + a) ltac:(lra). lra.
Qed.

Lemma integral_24_minus : forall a c, 
a > 0 -> 
∫ (λ x, x / √(x - a)) (a, ∞) = (λ x, 2 / 3 * (x + 2 * a) * √(x - a) + c).
Proof.
  intros a c H1.
  auto_int.
  solve_R.
  - rewrite Rmult_1_r, sqrt_sqrt; solve_R.
  - pose proof sqrt_lt_R0 (x - a) ltac:(lra). lra.
Qed.

Lemma integral_25 : forall a c, 
a > 0 -> 
∫ (λ x, √(x / (a - x))) (0, a) = (λ x, - √(x) * √(a - x) - a * arctan (√(x) * √(a - x) / (x - a)) + c).
Proof.
  auto_int. field_simplify.
  assert (H1 : √x ^ 4 * √(a - x) ^ 2 - √x ^ 2 * √(a - x) ^ 4 + 2 * √x ^ 2 * √(a - x) ^ 2 * a - √x ^ 2 * a * x + √x ^ 2 * x ^ 2 + √(a - x) ^ 2 * a * x - √(a - x) ^ 2 * x ^ 2 = √x ^ 2 * √(a - x) ^ 2 * (√x ^ 2 - √(a - x) ^ 2 + 2 * a) - a * x * (√x ^ 2 - √(a - x) ^ 2) + x ^ 2 * (√x ^ 2 - √(a - x) ^ 2)) by ring.
  rewrite H1. clear H1.
  assert (H1 : 2 * √x ^ 3 * √(a - x) ^ 3 + 2 * √x * √(a - x) * a ^ 2 - 4 * √x * √(a - x) * a * x + 2 * √x * √(a - x) * x ^ 2 = 2 * √x * √(a - x) * (√x ^ 2 * √(a - x) ^ 2 + a ^ 2 - 2 * a * x + x ^ 2)) by ring.
  rewrite H1. clear H1.
  repeat rewrite pow2_sqrt; try solve_R.
  assert (H2 : -2 * (x * (x * 1)) * a + 2 * x * (a * (a * 1)) = 2 * a * x * (a - x)) by ring.
  rewrite H2. clear H2.
  assert (H2 : -2 * x * a * √x * √(a - x) * √(x / (a - x)) + 2 * (a * (a * 1)) * √x * √(a - x) * √(x / (a - x)) = 2 * a * (a - x) * √x * √(a - x) * √(x / (a - x))) by ring.
  rewrite H2. clear H2.
  rewrite sqrt_div; try solve_R.
  assert (H2 : √x * (√x * 1) = x).
  { replace (√x * (√x * 1)) with (√x ^ 2) by ring. apply pow2_sqrt. solve_R. }
  rewrite H2. ring.
  - apply Rgt_not_eq, sqrt_lt_R0; solve_R.
  - split.
    + replace (x * (a - x) + a * (a * 1) - 2 * a * x + x * (x * 1)) with (a * (a - x)) by ring.
      apply Rgt_not_eq; solve_R.
    + split; apply Rgt_not_eq, sqrt_lt_R0; solve_R.
  - split.
    + apply Rlt_not_eq. solve_R.
    + split.
      * apply Rgt_not_eq, sqrt_lt_R0; solve_R.
      * split.
        -- apply Rgt_not_eq, sqrt_lt_R0; solve_R.
        -- replace (√x * √(a - x) * (√x * √(a - x))) with (x * (a - x)).
           ++ replace ((x - a) * (x - a) + x * (a - x)) with (a * (a - x)) by ring.
              apply Rgt_not_eq; solve_R.
           ++ assert (H3 : √x * √(a - x) * (√x * √(a - x)) = √x ^ 2 * √(a - x) ^ 2) by ring.
              rewrite H3. repeat rewrite pow2_sqrt; solve_R.
Qed.

Lemma integral_26 : forall a c, 
a > 0 -> 
∫ (λ x, √(x / (x + a))) (0, ∞) = (λ x, √(x) * √(x + a) - a * ln (√(x) + √(x + a)) + c).
Proof. 
  auto_int.
  - pose proof sqrt_lt_R0 x ltac:(solve_R) as H3.
    pose proof sqrt_lt_R0 (x + a) ltac:(solve_R) as H4.
    lra.
  - field_simplify.
    assert (H1 : √x ^ 3 + √x ^ 2 * √(x + a) + √x * √(x + a) ^ 2 - √x * a + √(x + a) ^ 3 - √(x + a) * a = (√x + √(x + a)) * (√x ^ 2 + √(x + a) ^ 2 - a)) by ring.
    rewrite H1. clear H1.
    repeat rewrite pow2_sqrt; try solve_R.
    assert (H1 : 2 * √x * x * √(x / (x + a)) + 2 * √x * a * √(x / (x + a)) + 2 * √(x + a) * x * √(x / (x + a)) = 2 * √x * (x + a) * √(x / (x + a)) + 2 * x * √(x + a) * √(x / (x + a))) by ring.
    rewrite H1. clear H1.
    rewrite sqrt_div; try solve_R.
    assert (H2 : √x * (√x * 1) = x).
    { replace (√x * (√x * 1)) with (√x ^ 2) by ring. apply pow2_sqrt. solve_R. }
    rewrite H2.
    assert (H3 : √(x + a) * (√(x + a) * 1) = x + a).
    { replace (√(x + a) * (√(x + a) * 1)) with (√(x + a) ^ 2) by ring. apply pow2_sqrt. solve_R. }
    rewrite H3. ring.
    apply Rgt_not_eq, sqrt_lt_R0; solve_R.
    apply Rgt_not_eq.
    assert (H2 : 0 < 2 * x * √(x + a)) by (apply Rmult_lt_0_compat; try solve_R; apply sqrt_lt_R0; solve_R).
    assert (H3 : 0 < 2 * √x * (x + a)) by (apply Rmult_lt_0_compat; try solve_R; apply Rmult_lt_0_compat; try solve_R; apply sqrt_lt_R0; solve_R).
    lra.
    split. 1 : apply Rgt_not_eq, sqrt_lt_R0; solve_R.
    split. 1 : apply Rgt_not_eq, sqrt_lt_R0; solve_R.
    apply Rgt_not_eq.
    assert (H2 : 0 < √x) by (apply sqrt_lt_R0; solve_R).
    assert (H3 : 0 < √(x + a)) by (apply sqrt_lt_R0; solve_R).
    lra.
Qed.

Lemma integral_27 : forall a b c, 
a > 0 -> 
∫ (λ x, x * √(a * x + b)) (-b/a, ∞) = (λ x, (-4 * b ^ 2 / (15 * a ^ 2) + 2 * b * x / (15 * a) + 2 * x ^ 2 / 5) * √(b + a * x) + c).
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
    assert (H4 : √(b + a * x) * (√(b + a * x) * 1) = b + a * x).
    { replace (√(b + a * x) * (√(b + a * x) * 1)) with (√(b + a * x) ^ 2) by ring. apply pow2_sqrt. lra. }
    rewrite H4. ring.
Qed.

Lemma integral_28 : forall a b c, 
a > 0 -> b > 0 -> 
∫ (λ x, √(x) * √(a * x + b)) (0, ∞) = (λ x, (b * √(x) / (4 * a) + x ^^ (3 / 2) / 2) * √(b + a * x) - b ^ 2 * ln (2 * √(a) * √(x) + 2 * √(b + a * x)) / (4 * a ^^ (3 / 2)) + c).
Proof.
  intros a b c Ha Hb.
  auto_int.
  - pose proof sqrt_lt_R0 a Ha.
    pose proof sqrt_lt_R0 x ltac:(solve_R).
    pose proof sqrt_lt_R0 (b + a * x) ltac:(solve_R).
    nra.
  - apply Rgt_not_eq.
    apply Rmult_gt_0_compat; try lra.
    apply Rpower_gt_0; lra.
  - replace (3 / 2 - 1) with (1 / 2) by lra.
    repeat rewrite Rpower_sqrt; try solve_R.
    replace (a ^^ (3 / 2)) with (a * √a).
    2 : { replace (3 / 2) with (1 + 1 / 2) by lra. rewrite Rpower_plus; solve_R. rewrite Rpower_1; try lra. rewrite Rpower_sqrt; solve_R. }
    replace (x ^^ (3 / 2)) with (x * √x).
    2 : { replace (3 / 2) with (1 + 1 / 2) by lra. rewrite Rpower_plus; solve_R. rewrite Rpower_1; try lra. rewrite Rpower_sqrt; solve_R. }
    field_simplify.
    2 : { repeat split; try apply Rgt_not_eq; try apply sqrt_lt_R0; try solve_R; try (apply Rpower_gt_0; solve_R).
      pose proof sqrt_lt_R0 a Ha. pose proof sqrt_lt_R0 x ltac:(solve_R). pose proof sqrt_lt_R0 (b + a * x) ltac:(solve_R). nra. }
    replace (a * x + b) with (b + a * x) by lra.
    replace (√a ^ 2) with a by (rewrite pow2_sqrt; solve_R).
    replace (√x ^ 2) with x by (rewrite pow2_sqrt; solve_R).
    replace (√(b + a * x) ^ 2) with (b + a * x) by (rewrite pow2_sqrt; solve_R).
    replace (√x ^ 3) with (x * √x) by (replace (√x ^ 3) with (√x ^ 2 * √x) by ring; rewrite pow2_sqrt; try solve_R; ring).
    replace (√(b + a * x) ^ 3) with ((b + a * x) * √(b + a * x)) by (replace (√(b + a * x) ^ 3) with (√(b + a * x) ^ 2 * √(b + a * x)) by ring; rewrite pow2_sqrt; try solve_R; ring).
    replace (128 * (x * √x) * a ^ 2 * √(b + a * x) * a * √(b + a * x)) with (128 * a ^ 3 * x * (b + a * x) * √x) by (replace (128 * (x * √x) * a ^ 2 * √(b + a * x) * a * √(b + a * x)) with (128 * a ^ 3 * x * √x * (√(b + a * x) ^ 2)) by ring; rewrite pow2_sqrt; solve_R).
    ring.
Qed.

Lemma integral_29 : forall a b c, 
a > 0 -> b > 0 -> 
∫ (λ x, x ^^ (3 / 2) * √(a * x + b)) (0, ∞) = (λ x, (- b ^ 2 * √(x) / (8 * a ^ 2) + b * x ^^ (3 / 2) / (12 * a) + x ^^ (5 / 2) / 3) * √(b + a * x) + b ^ 3 * ln (2 * √(a) * √(x) + 2 * √(b + a * x)) / (8 * a ^^ (5 / 2)) + c).
Proof.
  intros a b c H1 H2.
  auto_int.
  - pose proof sqrt_lt_R0 a H1.
    pose proof sqrt_lt_R0 x ltac:(solve_R).
    pose proof sqrt_lt_R0 (b + a * x) ltac:(solve_R).
    nra.
  - apply Rgt_not_eq.
    apply Rmult_gt_0_compat; try lra.
    apply Rpower_gt_0; lra.
  - replace (3 / 2 - 1) with (1 / 2) by lra.
    replace (5 / 2 - 1) with (3 / 2) by lra.
    replace (x ^^ (1 / 2)) with (√x).
    2 : { rewrite Rpower_sqrt; try solve_R. }
    replace (x ^^ (3 / 2)) with (x * √x).
    2 : { replace (3 / 2) with (1 + 1 / 2) by lra. rewrite Rpower_plus; try solve_R. rewrite Rpower_1; try lra. rewrite Rpower_sqrt; try solve_R. }
    replace (x ^^ (5 / 2)) with (x^2 * √x).
    2 : { replace (5 / 2) with (1 + 1 + 1 / 2) by lra. rewrite Rpower_plus; try solve_R. rewrite Rpower_plus; try solve_R. repeat rewrite Rpower_1; try lra. rewrite Rpower_sqrt; try solve_R. }
    replace (a ^^ (5 / 2)) with (a^2 * √a).
    2 : { replace (5 / 2) with (1 + 1 + 1 / 2) by lra. rewrite Rpower_plus; try solve_R. rewrite Rpower_plus; try solve_R. repeat rewrite Rpower_1; try lra. rewrite Rpower_sqrt; try solve_R. }
    field_simplify.
    replace (a * x + b) with (b + a * x) by lra.
    2 : { repeat split; try apply Rgt_not_eq; try apply sqrt_lt_R0; try solve_R; try (apply Rpower_gt_0; solve_R). pose proof sqrt_lt_R0 a H1. pose proof sqrt_lt_R0 x ltac:(solve_R). pose proof sqrt_lt_R0 (b + a * x) ltac:(solve_R). nra. }
    replace (√a ^ 2) with a by (rewrite pow2_sqrt; solve_R).
    replace (√x ^ 2) with x by (rewrite pow2_sqrt; solve_R).
    replace (√(b + a * x) ^ 2) with (b + a * x) by (rewrite pow2_sqrt; solve_R).
    replace (√x ^ 3) with (x * √x) by (replace (√x ^ 3) with (√x ^ 2 * √x) by ring; rewrite pow2_sqrt; try solve_R; ring).
    replace (√(b + a * x) ^ 3) with ((b + a * x) * √(b + a * x)) by (replace (√(b + a * x) ^ 3) with (√(b + a * x) ^ 2 * √(b + a * x)) by ring; rewrite pow2_sqrt; try solve_R; ring).
    assert (H_denom : 248832 * x * a ^ 2 * √(b + a * x) * a + 248832 * √x * a ^ 2 * (b + a * x) * √a <> 0).
    {
      assert (0 < x) by solve_R.
      assert (0 < a) by lra.
      assert (0 < b + a*x) by (pose proof sqrt_lt_R0 (b + a * x) ltac:(solve_R); nra).
      assert (0 < √x) by (apply sqrt_lt_R0; lra).
      assert (0 < √a) by (apply sqrt_lt_R0; lra).
      assert (0 < √(b + a * x)) by (apply sqrt_lt_R0; lra).
      apply Rgt_not_eq.
      apply Rplus_lt_0_compat; repeat apply Rmult_lt_0_compat; try lra.
    }
    apply Rmult_eq_reg_r with (r := 248832 * x * a ^ 2 * √(b + a * x) * a + 248832 * √x * a ^ 2 * (b + a * x) * √a); try lra.
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r; try lra.
    ring_simplify.
    replace (√x ^ 2) with x by (rewrite pow2_sqrt; solve_R).
    replace (√(b + a * x) ^ 2) with (b + a * x) by (rewrite pow2_sqrt; solve_R).
    ring.
Qed.

Lemma integral_30_plus : forall a c, 
∫ (λ x, √(x ^ 2 + a ^ 2)) = (λ x, 1 / 2 * x * √(x ^ 2 + a ^ 2) + 1 / 2 * a ^ 2 * ln (x + √(x ^ 2 + a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_30_minus : forall a c, 
a > 0 -> 
∫ (λ x, √(x ^ 2 - a ^ 2)) (a, ∞) = (λ x, 1 / 2 * x * √(x ^ 2 - a ^ 2) - 1 / 2 * a ^ 2 * ln (x + √(x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_31 : forall a c, 
a > 0 -> 
∫ (λ x, √(a ^ 2 - x ^ 2)) (-a, a) = (λ x, 1 / 2 * x * √(a ^ 2 - x ^ 2) - 1 / 2 * a ^ 2 * arctan (x * √(a ^ 2 - x ^ 2) / (x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_32_plus : forall a c, 
∫ (λ x, x * √(x ^ 2 + a ^ 2)) = (λ x, 1 / 3 * (x ^ 2 + a ^ 2) ^^ (3 / 2) + c).
Proof.
  auto_int.
Abort.

Lemma integral_32_minus : forall a c, 
a > 0 -> 
∫ (λ x, x * √(x ^ 2 - a ^ 2)) (a, ∞) = (λ x, 1 / 3 * (x ^ 2 - a ^ 2) ^^ (3 / 2) + c).
Proof.
  auto_int.
Abort.

Lemma integral_33_plus : forall a c, 
∫ (λ x, 1 / √(x ^ 2 + a ^ 2)) = (λ x, ln (x + √(x ^ 2 + a ^ 2)) + c).
Proof.
  auto_int. 
Abort.

Lemma integral_33_minus : forall a c, 
a > 0 -> 
∫ (λ x, 1 / √(x ^ 2 - a ^ 2)) (a, ∞) = (λ x, ln (x + √(x ^ 2 - a ^ 2)) + c).
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
∫ (λ x, 1 / √(a ^ 2 - x ^ 2)) (-a, a) = (λ x, arcsin (x / a) + c).
Proof.
  auto_int.
Abort.

Lemma integral_35_plus : forall a c, 
  a <> 0 ->
  ∫ (λ x, x / √(x ^ 2 + a ^ 2)) = (λ x, √(x ^ 2 + a ^ 2) + c).
Proof.
  intros a c H1. auto_int.
Qed.

Lemma integral_35_minus : forall a c, 
a > 0 -> 
∫ (λ x, x / √(x ^ 2 - a ^ 2)) (a, ∞) = (λ x, √(x ^ 2 - a ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_36 : forall a c, 
a > 0 -> 
∫ (λ x, x / √(a ^ 2 - x ^ 2)) (-a, a) = (λ x, - √(a ^ 2 - x ^ 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_37_plus : forall a c, 
a > 0 -> 
∫ (λ x, x ^ 2 / √(x ^ 2 + a ^ 2)) = (λ x, 1 / 2 * x * √(x ^ 2 + a ^ 2) - 1 / 2 * a ^ 2 * ln (x + √(x ^ 2 + a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_37_minus : forall a c, 
a > 0 -> 
∫ (λ x, x ^ 2 / √(x ^ 2 - a ^ 2)) (a, ∞) = (λ x, 1 / 2 * x * √(x ^ 2 - a ^ 2) + 1 / 2 * a ^ 2 * ln (x + √(x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_38 : forall a c, 
a > 0 -> 
∫ (λ x, x ^ 2 / √(a ^ 2 - x ^ 2)) (-a, a) = (λ x, - 1 / 2 * x * √(a ^ 2 - x ^ 2) - 1 / 2 * a ^ 2 * arctan (x * √(a ^ 2 - x ^ 2) / (x ^ 2 - a ^ 2)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_39 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (λ x, √(a * x ^ 2 + b * x + c0)) = (λ x, (b / (4 * a) + x / 2) * √(a * x ^ 2 + b * x + c0) + (4 * a * c0 - b ^ 2) / (8 * a ^^ (3 / 2)) * ln ((2 * a * x + b) / √(a) + 2 * √(a * x ^ 2 + b * x + c0)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_40 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (λ x, x * √(a * x ^ 2 + b * x + c0)) = (λ x, (x ^ 3 / 3 + b * x / (12 * a) + (8 * a * c0 - 3 * b ^ 2) / (24 * a ^ 2)) * √(a * x ^ 2 + b * x + c0) - b * (4 * a * c0 - b ^ 2) / (16 * a ^^ (5 / 2)) * ln ((2 * a * x + b) / √(a) + 2 * √(a * x ^ 2 + b * x + c0)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_41 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (λ x, 1 / √(a * x ^ 2 + b * x + c0)) = (λ x, 1 / √(a) * ln ((2 * a * x + b) / √(a) + 2 * √(a * x ^ 2 + b * x + c0)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_42 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (λ x, x / √(a * x ^ 2 + b * x + c0)) = (λ x, 1 / a * √(a * x ^ 2 + b * x + c0) - b / (2 * a ^^ (3 / 2)) * ln ((2 * a * x + b) / √(a) + 2 * √(a * x ^ 2 + b * x + c0)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_43 : forall c, 
∫ (λ x, ln x) (0, ∞) = (λ x, x * ln x - x + c).
Proof.
  auto_int.
Qed.

Lemma integral_44 : forall a c, 
a > 0 -> 
∫ (λ x, ln (a * x) / x) (0, ∞) = (λ x, 1 / 2 * (ln (a * x)) ^ 2 + c).
Proof.
  auto_int.
Qed.

Lemma integral_45 : forall a b c, 
a > 0 -> 
∫ (λ x, ln (a * x + b)) (-b/a, ∞) = (λ x, (a * x + b) / a * ln (a * x + b) - x + c).
Proof.
  intros a b c H1. auto_int.
  - solve_R. apply Rmult_lt_compat_r with (r := a) in H; field_simplify in H; nra.
  - solve_R. apply Rmult_lt_compat_r with (r := a) in H; field_simplify in H; nra.
Qed.

Lemma integral_46 : forall a b c, 
a <> 0 -> 
b <> 0 -> 
∫ (λ x, ln (a ^ 2 * x ^ 2 + b ^ 2)) = (λ x, x * ln (a ^ 2 * x ^ 2 + b ^ 2) + 2 * b / a * arctan (a * x / b) - 2 * x + c).
Proof.
  auto_int.
Qed.

Lemma integral_47 : forall a b c, 
a > 0 -> 
b > 0 -> 
∫ (λ x, ln (a ^ 2 - b ^ 2 * x ^ 2)) (-a/b, a/b) = (λ x, x * ln (a ^ 2 - b ^ 2 * x ^ 2) + 2 * a / b * arctan (b * x / a) - 2 * x + c).
Proof.
  auto_int.
Abort.

Lemma integral_48 : forall a b c0 c, 
a > 0 -> 
4 * a * c0 - b ^ 2 > 0 -> 
∫ (λ x, ln (a * x ^ 2 + b * x + c0)) = (λ x, 1 / a * √(4 * a * c0 - b ^ 2) * arctan ((2 * a * x + b) / √(4 * a * c0 - b ^ 2)) - 2 * x + (b / (2 * a) + x) * ln (a * x ^ 2 + b * x + c0) + c).
Proof.
  intros a b c0 c H1 H2. auto_int.
  - assert (H3 : 4 * a * (a * (x * (x * 1)) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
    pose proof pow2_ge_0 (2 * a * x + b). nra.
  - field_simplify.
    + rewrite pow2_sqrt; try lra.
      assert (H3 : a * (x * x) + b * x + c0 <> 0).
      { assert (H5 : 4 * a * (a * (x * x) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
        pose proof pow2_ge_0 (2 * a * x + b). nra.
      }
      assert (H4 : 8 * a ^ 4 * x ^ 4 + 16 * a ^ 3 * x ^ 3 * b + 8 * a ^ 3 * x ^ 2 * c0 + 2 * a ^ 2 * (4 * a * c0 - b * b) * x ^ 2 + 10 * a ^ 2 * x ^ 2 * b ^ 2 + 8 * a ^ 2 * x * b * c0 + 2 * a * (4 * a * c0 - b * b) * x * b + 2 * a * (4 * a * c0 - b * b) * c0 + 2 * a * x * b ^ 3 + 2 * a * b ^ 2 * c0 = 8 * a^2 * (a * (x*x) + b*x + c0)^2) by ring.
      rewrite H4.
      assert (H5 : 8 * a ^ 4 * x ^ 4 * ln (a * (x * x) + b * x + c0) + 16 * a ^ 3 * x ^ 3 * b * ln (a * (x * x) + b * x + c0) + 8 * a ^ 3 * x ^ 2 * ln (a * (x * x) + b * x + c0) * c0 - 16 * a ^ 3 * x ^ 2 * c0 + 2 * a ^ 2 * (4 * a * c0 - b * b) * x ^ 2 * ln (a * (x * x) + b * x + c0) + 4 * a ^ 2 * (4 * a * c0 - b * b) * x ^ 2 + 10 * a ^ 2 * x ^ 2 * b ^ 2 * ln (a * (x * x) + b * x + c0) + 4 * a ^ 2 * x ^ 2 * b ^ 2 + 8 * a ^ 2 * x * b * ln (a * (x * x) + b * x + c0) * c0 - 16 * a ^ 2 * x * b * c0 + 2 * a * (4 * a * c0 - b * b) * x * b * ln (a * (x * x) + b * x + c0) + 4 * a * (4 * a * c0 - b * b) * x * b + 2 * a * (4 * a * c0 - b * b) * ln (a * (x * x) + b * x + c0) * c0 + 2 * a * x * b ^ 3 * ln (a * (x * x) + b * x + c0) + 4 * a * x * b ^ 3 + 2 * a * b ^ 2 * ln (a * (x * x) + b * x + c0) * c0 - 4 * a * b ^ 2 * c0 + (4 * a * c0 - b * b) * b ^ 2 + b ^ 4 = 8 * a^2 * (a * (x*x) + b*x + c0)^2 * ln (a * (x * x) + b * x + c0)) by ring.
      rewrite H5.
      field. nra.
    + split.
      * assert (H5 : 4 * a * (a * (x * x) + b * x + c0) = (2 * a * x + b) ^ 2 + (4 * a * c0 - b ^ 2)) by lra.
        pose proof pow2_ge_0 (2 * a * x + b). nra.
      * split. { nra. }
        split.
        -- assert (H3 : 0 < √(4 * a * c0 - b * b)). { apply sqrt_lt_R0. lra. } lra.
        -- pose proof pow2_ge_0 (2 * a * x + b).
           assert (H4: √(4 * a * c0 - b * b) * √(4 * a * c0 - b * b) = 4 * a * c0 - b ^ 2).
           { rewrite sqrt_sqrt; lra. }
           nra.
Qed.

Lemma integral_49 : forall a b c, 
a > 0 -> 
∫ (λ x, x * ln (a * x + b)) (-b/a, ∞) = (λ x, b / (2 * a) * x - 1 / 4 * x ^ 2 + 1 / 2 * (x ^ 2 - b ^ 2 / a ^ 2) * ln (a * x + b) + c).
Proof.
  auto_int.
Abort.

Lemma integral_50 : forall a b c, 
a > 0 -> 
b > 0 -> 
∫ (λ x, x * ln (a ^ 2 - b ^ 2 * x ^ 2)) (-a/b, a/b) = (λ x, - 1 / 2 * x ^ 2 + 1 / 2 * (x ^ 2 - a ^ 2 / b ^ 2) * ln (a ^ 2 - b ^ 2 * x ^ 2) + c).
Proof.
  auto_int.
Abort.

Lemma integral_51 : forall a c, 
a <> 0 -> 
∫ (λ x, exp (a * x)) = (λ x, 1 / a * exp (a * x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_53 : forall c, 
∫ (λ x, x * exp x) = (λ x, (x - 1) * exp x + c).
Proof.
  auto_int.
Qed.

Lemma integral_54 : forall a c, 
a <> 0 -> 
∫ (λ x, x * exp (a * x)) = (λ x, (x / a - 1 / a ^ 2) * exp (a * x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_55 : forall c, 
∫ (λ x, x ^ 2 * exp x) = (λ x, exp x * (x ^ 2 - 2 * x + 2) + c).
Proof.
  auto_int.
Qed.

Lemma integral_56 : forall a c, 
a <> 0 -> 
∫ (λ x, x ^ 2 * exp (a * x)) = (λ x, exp (a * x) * (x ^ 2 / a - 2 * x / a ^ 2 + 2 / a ^ 3) + c).
Proof.
  auto_int.
Qed.

Lemma integral_57 : forall c, 
∫ (λ x, x ^ 3 * exp x) = (λ x, exp x * (x ^ 3 - 3 * x ^ 2 + 6 * x - 6) + c).
Proof.
  auto_int.
Qed.

Lemma integral_60 : forall c, 
∫ (λ x, sin x) = (λ x, - cos x + c).
Proof.
  auto_int.
Qed.

Lemma integral_61 : forall c, 
∫ (λ x, (sin x) ^ 2) = (λ x, x / 2 - 1 / 4 * sin (2 * x) + c).
Proof.
  auto_int. rewrite cos_2x_3. solve_R.
Qed.

Lemma integral_62 : forall c, 
∫ (λ x, (sin x) ^ 3) = (λ x, - 3 / 4 * cos x + 1 / 12 * cos (3 * x) + c).
Proof.
  auto_int. rewrite sin_3x. solve_R.
Qed.

Lemma integral_63 : forall c, 
∫ (λ x, cos x) = (λ x, sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_64 : forall c, 
∫ (λ x, (cos x) ^ 2) = (λ x, x / 2 + 1 / 4 * sin (2 * x) + c).
Proof.
  auto_int. rewrite cos_2x_2. solve_R.
Qed.

Lemma integral_65 : forall c, 
∫ (λ x, (cos x) ^ 3) = (λ x, 3 / 4 * sin x + 1 / 12 * sin (3 * x) + c).
Proof.
  auto_int. rewrite cos_3x. solve_R.
Qed.

Lemma integral_66 : forall c, 
∫ (λ x, sin x * cos x) = (λ x, -1 / 2 * (cos x) ^ 2 + c).
Proof.
  auto_int.
Qed.

Lemma integral_67 : forall c, 
∫ (λ x, (sin x) ^ 2 * cos x) = (λ x, 1 / 4 * sin x - 1 / 12 * sin (3 * x) + c).
Proof.
  auto_int. rewrite cos_3x. pose proof pythagorean_identity x as H1.
  replace (sin x * sin x) with (1 - (cos x)^2 ); solve_R.
Qed.

Lemma integral_68 : forall c, 
∫ (λ x, sin x * (cos x) ^ 2) = (λ x, -1 / 4 * cos x - 1 / 12 * cos (3 * x) + c).
Proof.
  auto_int.
  rewrite sin_3x. 
  pose proof pythagorean_identity x as H1.
  replace (cos x * cos x) with (1 - (sin x)^2); solve_R.
Qed.

Lemma integral_69 : forall c, 
∫ (λ x, (sin x) ^ 2 * (cos x) ^ 2) = (λ x, x / 8 - 1 / 32 * sin (4 * x) + c).
Proof.
  auto_int.
  replace (4 * x) with (2 * (2 * x)) by lra.
  rewrite cos_2x_3.
  rewrite sin_2x.
  solve_R.
Qed.

Lemma integral_70 : forall c, 
∫ (λ x, tan x) (0, π / 2) = (λ x, - ln (cos x) + c).
Proof.
  auto_int.
  - pose proof π_pos; lra.
  - apply cos_gt_0_on_open_pi_2; solve_R.
  - unfold tan. lra.
Qed.

Lemma integral_71 : forall c, 
∫ (λ x, (tan x) ^ 2) (0, π / 2) = (λ x, - x + tan x + c).
Proof.
  auto_int.
  - pose proof π_pos; lra.
  - pose proof cos_gt_0_on_open_pi_2 x; solve_R.
  - unfold tan. pose proof pythagorean_identity x. solve_R.
    pose proof cos_gt_0_on_open_pi_2 x; solve_R.
Qed.

Lemma integral_72 : forall c, 
∫ (λ x, (tan x) ^ 3) (0, π / 2) = (λ x, ln (cos x) + 1 / 2 * (sec x) ^ 2 + c).
Proof.
  auto_int. 2, 3 : pose proof cos_gt_0_on_open_pi_2 x; solve_R.
  - pose proof π_pos; lra.  
  - unfold sec, tan. pose proof cos_gt_0_on_open_pi_2 x; field_simplify; try solve [solve_R].
    pose proof pythagorean_identity x. replace (cos x ^ 2) with (1 - (sin x)^2); solve_R.
Qed.

Lemma integral_73 : forall c, 
∫ (λ x, sec x) (0, π / 2) = (λ x, ln (sec x + tan x) + c).
Proof.
  auto_int. 2, 3 : pose proof cos_gt_0_on_open_pi_2 x; solve_R.
  - pose proof π_pos; lra.
  - unfold sec, tan. pose proof cos_gt_0_on_open_pi_2 x. 
    pose proof sin_bounds x. pose proof pythagorean_identity x. solve_R.
    assert (H3 : cos x > 0) by (apply H0; exact H).
    replace (1 / cos x + sin x / cos x) with ((1 + sin x) / cos x) by (field; lra).
    apply Rdiv_pos_pos; nra.
  - unfold sec, tan. pose proof cos_gt_0_on_open_pi_2 x. pose proof sin_bounds x.
    pose proof pythagorean_identity x. solve_R.
Qed.

Lemma integral_74 : forall c, 
∫ (λ x, (sec x) ^ 2) (0, π / 2) = (λ x, tan x + c).
Proof.
  auto_int. 2 : pose proof cos_gt_0_on_open_pi_2 x; solve_R.
  - pose proof π_pos; lra.
  - unfold sec. pose proof cos_gt_0_on_open_pi_2 x. field; solve_R.
Qed.

Lemma integral_75 : forall c, 
∫ (λ x, (sec x) ^ 3) (0, π / 2) = (λ x, 1 / 2 * sec x * tan x + 1 / 2 * ln (sec x + tan x) + c).
Proof.
  auto_int. 2, 3, 4, 5 : pose proof cos_gt_0_on_open_pi_2 x; solve_R.
  - pose proof π_pos; lra.
  - unfold sec, tan. pose proof cos_gt_0_on_open_pi_2 x as H1. pose proof sin_bounds x as H2.
    pose proof pythagorean_identity x as H3. solve_R.
    assert (H4 : cos x > 0) by (apply H1; exact H).
    replace (1 / cos x + sin x / cos x) with ((1 + sin x) / cos x) by (field; lra).
    apply Rdiv_pos_pos; nra.
  - unfold sec, tan. pose proof cos_gt_0_on_open_pi_2 x as H1. pose proof sin_bounds x as H2.
    pose proof pythagorean_identity x as H3. solve_R.
Qed.

Lemma integral_76 : forall c, 
∫ (λ x, sec x * tan x) (0, π / 2) = (λ x, sec x + c).
Proof.
  auto_int.
  - pose proof π_pos; lra.
  - pose proof cos_gt_0_on_open_pi_2 x. solve_R.
Qed.

Lemma integral_77 : forall c, 
∫ (λ x, (sec x) ^ 2 * tan x) (0, π / 2) = (λ x, 1 / 2 * (sec x) ^ 2 + c).
Proof.
  auto_int.
  - pose proof π_pos; lra.
  - pose proof cos_gt_0_on_open_pi_2 x. solve_R.
Qed.

Lemma integral_78 : forall n c, 
n <> 0 -> 
∫ (λ x, (sec x) ^^ n * tan x) (0, π / 2) = (λ x, 1 / n * (sec x) ^^ n + c).
Proof.
  auto_int.
  - pose proof π_pos; lra.
  - pose proof cos_gt_0_on_open_pi_2 x. solve_R.
  - unfold sec. pose proof cos_gt_0_on_open_pi_2 x. apply Rdiv_pos_pos; solve_R.
  - unfold sec, tan. pose proof cos_gt_0_on_open_pi_2 x.
    pose proof sin_bounds x. pose proof pythagorean_identity x. solve_R.
    assert (H4 : cos x > 0) by (apply H1; exact H0).
    assert (H5 : 1 / cos x > 0) by (apply Rdiv_pos_pos; lra).
    replace ((1 / cos x) ^^ n) with ((1 / cos x) ^^ (n - 1) * (1 / cos x) ^^ 1).
    2: { rewrite <- Rpower_plus; try lra. f_equal; lra. }
    rewrite Rpower_1; try lra.
    field; lra.
Qed.

Lemma integral_79 : forall c, 
∫ (λ x, csc x) (0, π / 2) = (λ x, ln (csc x - cot x) + c).
Proof.
  auto_int.
  - pose proof π_pos; lra.
  - unfold csc, cot, tan.
    assert (H1 : sin x > 0) by (apply sin_gt_0; pose proof π_pos; solve_R).
    pose proof pythagorean_identity x. pose proof cos_bounds x.
    pose proof cos_gt_0_on_open_pi_2 x.
    replace (1 / sin x - 1 / (sin x / cos x)) with ((1 - cos x) / sin x) by solve_R.
    apply Rdiv_pos_pos; nra.
  - unfold csc, cot, tan.
    assert (H1 : sin x > 0) by (apply sin_gt_0; pose proof π_pos; solve_R).
    pose proof pythagorean_identity x. pose proof cos_bounds x.
    pose proof cos_gt_0_on_open_pi_2 x.
    replace (1 / sin x - 1 / (sin x / cos x)) with ((1 - cos x) / sin x) by solve_R.
    apply Rgt_not_eq. apply Rdiv_pos_pos; nra.
Qed.

Lemma integral_80 : forall c, 
∫ (λ x, (csc x) ^ 2) (0, π / 2) = (λ x, - cot x + c).
Proof.
  auto_int. pose proof π_pos; lra.
Qed.

Lemma integral_81 : forall c, 
∫ (λ x, (csc x) ^ 3) (0, π / 2) = (λ x, -1 / 2 * cot x * csc x + 1 / 2 * ln (csc x - cot x) + c).
Proof.
  auto_int.
  - pose proof π_pos; lra.
  - unfold csc, cot, tan.
    assert (H1 : sin x > 0) by (apply sin_gt_0; pose proof π_pos; solve_R).
    pose proof cos_bounds x. pose proof pythagorean_identity x.
    assert (H4 : cos x > 0) by (apply cos_gt_0_on_open_pi_2; exact H).
    replace (1 / sin x - 1 / (sin x / cos x)) with ((1 - cos x) / sin x) by (field; lra).
    apply Rdiv_pos_pos; nra.
  - unfold csc, cot, tan.
    assert (H1 : sin x > 0) by (apply sin_gt_0; pose proof π_pos; solve_R).
    pose proof pythagorean_identity x as H2.
    pose proof cos_gt_0_on_open_pi_2 x as H3.
    assert (H4 : 1 / sin x - 1 / (sin x / cos x) <> 0).
    {
      replace (1 / sin x - 1 / (sin x / cos x)) with ((1 - cos x) / sin x) by solve_R.
      apply Rgt_not_eq; apply Rdiv_pos_pos; nra. 
    }
    assert (H5 : cos x > 0) by (apply H3; exact H).
    assert (H6 : sin x / cos x <> 0) by (apply Rgt_not_eq; apply Rdiv_pos_pos; nra).
    replace (-1 / 2 * - (1 / sin x * (1 / sin x)) * (1 / sin x) + -1 / 2 * (1 / (sin x / cos x)) * - (1 / sin x * (1 / (sin x / cos x))) + 1 / 2 * ((- (1 / sin x * (1 / (sin x / cos x))) - - (1 / sin x * (1 / sin x))) / (1 / sin x - 1 / (sin x / cos x)))) 
    with ((sin x ^ 2 + cos x ^ 2 + 1) / (2 * (sin x * (sin x * sin x)))) by (field; nra).
    rewrite H2.
    field; nra.
Qed.

Lemma integral_82 : forall n c, 
n <> 0 -> 
∫ (λ x, (csc x) ^^ n * cot x) (0, π / 2) = (λ x, -1 / n * (csc x) ^^ n + c).
Proof.
  auto_int.
Abort.

Lemma integral_83 : forall c, 
∫ (λ x, sec x * csc x) (0, π / 2) = (λ x, ln (tan x) + c).
Proof.
  auto_int.
Abort.

Lemma integral_84 : forall c, 
∫ (λ x, x * cos x) = (λ x, cos x + x * sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_85 : forall a c, 
a <> 0 -> 
∫ (λ x, x * cos (a * x)) = (λ x, 1 / a ^ 2 * cos (a * x) + 1 / a * x * sin (a * x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_86 : forall c, 
∫ (λ x, x ^ 2 * cos x) = (λ x, 2 * x * cos x + (x ^ 2 - 2) * sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_87 : forall a c, 
a <> 0 -> 
∫ (λ x, x ^ 2 * cos (a * x)) = (λ x, 2 / a ^ 2 * x * cos (a * x) + (a ^ 2 * x ^ 2 - 2) / a ^ 3 * sin (a * x) + c).
Proof.
  intros. auto_int.
  repeat (apply Rmult_integral_contrapositive; split); try lra.
Qed.

Lemma integral_90 : forall c, 
∫ (λ x, x * sin x) = (λ x, - x * cos x + sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_91 : forall a c, 
a <> 0 -> 
∫ (λ x, x * sin (a * x)) = (λ x, - x / a * cos (a * x) + 1 / a ^ 2 * sin (a * x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_92 : forall c, 
∫ (λ x, x ^ 2 * sin x) = (λ x, (2 - x ^ 2) * cos x + 2 * x * sin x + c).
Proof.
  auto_int.
Qed.

Lemma integral_93 : forall a c, 
a <> 0 -> 
∫ (λ x, x ^ 3 * sin (a * x)) = (λ x, (3 * a ^ 2 * x ^ 2 - 6) / a ^ 4 * sin (a * x) + (6 * x - a ^ 2 * x ^ 3) / a ^ 3 * cos (a * x) + c).
Proof.
  auto_int. all: repeat (apply Rmult_integral_contrapositive; split); solve_R.
Qed.

Lemma integral_95 : forall c, 
∫ (λ x, exp x * sin x) = (λ x, 1 / 2 * exp x * (sin x - cos x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_96 : forall a b c, 
b ^ 2 + a ^ 2 <> 0 -> 
∫ (λ x, exp (b * x) * sin (a * x)) = (λ x, 1 / (b ^ 2 + a ^ 2) * exp (b * x) * (b * sin (a * x) - a * cos (a * x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_97 : forall c, 
∫ (λ x, exp x * cos x) = (λ x, 1 / 2 * exp x * (sin x + cos x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_98 : forall a b c, 
b ^ 2 + a ^ 2 <> 0 -> 
∫ (λ x, exp (b * x) * cos (a * x)) = (λ x, 1 / (b ^ 2 + a ^ 2) * exp (b * x) * (a * sin (a * x) + b * cos (a * x)) + c).
Proof.
  auto_int.
Qed.  

Lemma integral_99 : forall c, 
∫ (λ x, x * exp x * sin x) = (λ x, 1 / 2 * exp x * (cos x - x * cos x + x * sin x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_100 : forall c, 
∫ (λ x, x * exp x * cos x) = (λ x, 1 / 2 * exp x * (x * cos x - sin x + x * sin x) + c).
Proof.
  auto_int.
Qed.

Lemma integral_101 : forall c, 
∫ (λ x, cosh x) = (λ x, sinh x + c).
Proof.
  auto_int.
Qed.

Lemma integral_102 : forall a b c, 
a ^ 2 - b ^ 2 <> 0 -> 
∫ (λ x, exp (a * x) * cosh (b * x)) = (λ x, exp (a * x) / (a ^ 2 - b ^ 2) * (a * cosh (b * x) - b * sinh (b * x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_103 : forall c, 
∫ (λ x, sinh x) = (λ x, cosh x + c).
Proof.
  auto_int.
Qed.

Lemma integral_104 : forall a b c, 
a ^ 2 - b ^ 2 <> 0 -> 
∫ (λ x, exp (a * x) * sinh (b * x)) = (λ x, exp (a * x) / (a ^ 2 - b ^ 2) * (- b * cosh (b * x) + a * sinh (b * x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_105 : forall c, 
∫ (λ x, exp x * tanh x) = (λ x, exp x - 2 * arctan (exp x) + c).
Proof.
  auto_int. 
  unfold tanh, sinh, cosh.
Abort.

Lemma integral_106 : forall a c, 
a <> 0 -> 
∫ (λ x, tanh (a * x)) = (λ x, 1 / a * ln (cosh (a * x)) + c).
Proof.
  auto_int.
Abort.

Lemma integral_107 : forall a b c, 
a ^ 2 + b ^ 2 <> 0 -> 
∫ (λ x, cos (a * x) * cosh (b * x)) = (λ x, 1 / (a ^ 2 + b ^ 2) * (a * sin (a * x) * cosh (b * x) + b * cos (a * x) * sinh (b * x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_108 : forall a b c, 
a ^ 2 + b ^ 2 <> 0 -> 
∫ (λ x, cos (a * x) * sinh (b * x)) = (λ x, 1 / (a ^ 2 + b ^ 2) * (b * cos (a * x) * cosh (b * x) + a * sin (a * x) * sinh (b * x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_109 : forall a b c, 
a ^ 2 + b ^ 2 <> 0 -> 
∫ (λ x, sin (a * x) * cosh (b * x)) = (λ x, 1 / (a ^ 2 + b ^ 2) * (- a * cos (a * x) * cosh (b * x) + b * sin (a * x) * sinh (b * x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_110 : forall a b c, 
a ^ 2 + b ^ 2 <> 0 -> 
∫ (λ x, sin (a * x) * sinh (b * x)) = (λ x, 1 / (a ^ 2 + b ^ 2) * (b * cosh (b * x) * sin (a * x) - a * cos (a * x) * sinh (b * x)) + c).
Proof.
  auto_int.
Qed.

Lemma integral_111 : forall a c, 
a <> 0 -> 
∫ (λ x, sinh (a * x) * cosh (a * x)) = (λ x, (- 2 * a * x + sinh (2 * a * x)) / (4 * a) + c).
Proof.
  auto_int.
Abort.

Lemma integral_112 : forall a b c, 
b ^ 2 - a ^ 2 <> 0 -> 
∫ (λ x, sinh (a * x) * cosh (b * x)) = (λ x, (b * cosh (b * x) * sinh (a * x) - a * cosh (a * x) * sinh (b * x)) / (b ^ 2 - a ^ 2) + c).
Proof.
  auto_int.
Abort.

End Integral_Table.