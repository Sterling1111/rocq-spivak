From Calculus.Chapter13 Require Import Prelude.

Definition fi x := x^2 / 2 + 2.
Definition gi x := x^2.

Definition p_fi := ltac:(plot fi (-3) 3 with (i_size 2000 1000)).
Definition p_gi := ltac:(plot gi (-3) 3 with (i_size 2000 1000)).

Plot p_fi as "Calculus/Chapter13/Problem8/fi.gp".
Plot p_gi as "Calculus/Chapter13/Problem8/gi.gp".

Lemma lemma_13_8_i : ∫ (-2) 2 (λ x, (x^2 / 2 + 2) - x^2) = 16 / 3.
Proof.
  auto_int.
Qed.

Definition fii x := x^2.
Definition gii x := -x^2.

Definition p_fii := ltac:(plot fii (-2) 2 with (i_size 2000 1000)).
Definition p_gii := ltac:(plot gii (-2) 2 with (i_size 2000 1000)).

Plot p_fii as "Calculus/Chapter13/Problem8/fii.gp".
Plot p_gii as "Calculus/Chapter13/Problem8/gii.gp".

Lemma lemma_13_8_ii : ∫ (-1) 1 (λ x, x^2 - (-x^2)) = 4 / 3.
Proof.
  auto_int.
Qed.

Definition fiii x := 1 - x^2.
Definition giii x := x^2.

Definition p_fiii := ltac:(plot fiii (-1) 1 with (i_size 2000 1000)).
Definition p_giii := ltac:(plot giii (-1) 1 with (i_size 2000 1000)).

Plot p_fiii as "Calculus/Chapter13/Problem8/fiii.gp".
Plot p_giii as "Calculus/Chapter13/Problem8/giii.gp".

Lemma lemma_13_8_iii : ∫ (-(1 / √2)) (1 / √2) (λ x, (1 - x^2) - x^2) = (2 * √2) / 3.
Proof.
  auto_int;
  pose proof sqrt_lt_R0 2;
  pose proof Rdiv_pos_pos 1 (√2); 
  pose proof sqrt_sqrt 2; try nra.
  apply Rmult_eq_reg_r with (r := √2); solve_R.
Qed.

Definition fiv x := x^2.
Definition giv x := 1 - x^2.
Definition hiv : (R -> R) := (λ _, 2).

Definition p_fiv := ltac:(plot fiv (-2) 2 with (i_size 2000 1000)).
Definition p_giv := ltac:(plot giv (-2) 2 with (i_size 2000 1000)).
Definition p_hiv := ltac:(plot hiv (-2) 2 with (i_size 2000 1000)).

Plot p_fiv as "Calculus/Chapter13/Problem8/fiv.gp".
Plot p_giv as "Calculus/Chapter13/Problem8/giv.gp".
Plot p_hiv as "Calculus/Chapter13/Problem8/hiv.gp".

Lemma lemma_13_8_iv : ∫ (-√2) (√2) (λ x, 2 - x^2) - ∫ (-(1 / √2)) (1 / √2) (λ x, (1 - x^2) - x^2) = 2 * √2.
Proof.
  assert (H1 : ∫ (-√2) (√2) (λ x, 2 - x^2) = (8 * √2) / 3).
  { auto_int; admit. }
  assert (H2 : ∫ (-(1 / √2)) (1 / √2) (λ x, 1 - x^2 - x^2) = (2 * √2) / 3).
  { auto_int; admit. }
  rewrite H1, H2.
  lra.
Admitted.

Definition fv x := x^2.
Definition gv x := x^2 - 2*x + 4.

Definition p_fv := ltac:(plot fv (-1) 3 with (i_size 2000 1000)).
Definition p_gv := ltac:(plot gv (-1) 3 with (i_size 2000 1000)).

Plot p_fv as "Calculus/Chapter13/Problem8/fv.gp".
Plot p_gv as "Calculus/Chapter13/Problem8/gv.gp".

Lemma lemma_13_8_v : ∫ 0 2 (λ x, (x^2 - 2*x + 4) - x^2) = 4.
Proof.
  auto_int.
Qed.

Definition fvi x := √x.
Definition gvi x := x^2.

Definition p_fvi := ltac:(plot fvi 0 3 with (i_size 2000 1000)).
Definition p_gvi := ltac:(plot gvi 0 3 with (i_size 2000 1000)).

Plot p_fvi as "Calculus/Chapter13/Problem8/fvi.gp".
Plot p_gvi as "Calculus/Chapter13/Problem8/gvi.gp".

Lemma lemma_13_8_vi : 2 * √2 - ∫ 0 (√2) (λ y, y^2) = (4 * √2) / 3.
Proof.
  assert (H1 : ∫ 0 (√2) (λ y, y^2) = (2 * √2) / 3).
  { auto_int; admit. }
  rewrite H1.
  lra.
Admitted.