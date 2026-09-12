From Calculus.Chapter8 Require Import Prelude Problem1.

Definition almost_upper_bound (A : Ensemble ℝ) (x : ℝ) :=
  Finite_set (fun y => y ∈ A /\ y > x).

Definition almost_lower_bound (A : Ensemble ℝ) (x : ℝ) :=
  Finite_set (fun y => y ∈ A /\ y < x).

Lemma lemma_8_18_a_i : ∀ x,
  (almost_upper_bound problem_8_1_i_set x <-> 0 < x) /\
  (almost_lower_bound problem_8_1_i_set x <-> x <= 0).
Proof. Abort.

Lemma lemma_8_18_a_ii : ∀ x,
  (almost_upper_bound problem_8_1_ii_set x <-> 0 < x) /\
  (almost_lower_bound problem_8_1_ii_set x <-> x < 0).
Proof. Abort.

Lemma lemma_8_18_a_iii : ∀ x,
  (almost_upper_bound problem_8_1_iii_set x <-> 0 < x) /\
  (almost_lower_bound problem_8_1_iii_set x <-> x <= 0).
Proof. Abort.

Lemma lemma_8_18_a_iv : ∀ x,
  (almost_upper_bound problem_8_1_iv_set x <-> √2 <= x) /\
  (almost_lower_bound problem_8_1_iv_set x <-> x <= 0).
Proof. Abort.

Lemma lemma_8_18_a_v : ∀ x,
  ~ almost_upper_bound problem_8_1_v_set x /\
  ~ almost_lower_bound problem_8_1_v_set x.
Proof. Abort.

Lemma lemma_8_18_a_vi : ∀ x,
  (almost_upper_bound problem_8_1_vi_set x <-> ((-1 + √5) / 2) <= x) /\
  (almost_lower_bound problem_8_1_vi_set x <-> x <= ((-1 - √5) / 2)).
Proof. Abort.

Lemma lemma_8_18_a_vii : ∀ x,
  (almost_upper_bound problem_8_1_vii_set x <-> 0 <= x) /\
  (almost_lower_bound problem_8_1_vii_set x <-> x <= ((-1 - √5) / 2)).
Proof. Abort.

Lemma lemma_8_18_a_viii : ∀ x,
  (almost_upper_bound problem_8_1_viii_set x <-> 1 < x) /\
  (almost_lower_bound problem_8_1_viii_set x <-> x <= -1).
Proof. Abort.

Lemma lemma_8_18_b_1 : ∀ A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  (fun x => almost_upper_bound A x) ≠ ∅.
Proof. Abort.

Lemma lemma_8_18_b_2 : ∀ A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  has_lower_bound (fun x => almost_upper_bound A x).
Proof. Abort.

Definition lim_sup (A : Ensemble ℝ) (l : ℝ) :=
  is_glb (fun x => almost_upper_bound A x) l.

Lemma lemma_8_18_c_i : lim_sup problem_8_1_i_set 0.
Proof. Abort.

Lemma lemma_8_18_c_ii : lim_sup problem_8_1_ii_set 0.
Proof. Abort.

Lemma lemma_8_18_c_iii : lim_sup problem_8_1_iii_set 0.
Proof. Abort.

Lemma lemma_8_18_c_iv : lim_sup problem_8_1_iv_set √2.
Proof. Abort.

Lemma lemma_8_18_c_v : ∀ l, ~ lim_sup problem_8_1_v_set l.
Proof. Abort.

Lemma lemma_8_18_c_vi : lim_sup problem_8_1_vi_set ((-1 + √5) / 2).
Proof. Abort.

Lemma lemma_8_18_c_vii : lim_sup problem_8_1_vii_set 0.
Proof. Abort.

Lemma lemma_8_18_c_viii : lim_sup problem_8_1_viii_set 1.
Proof. Abort.

Definition lim_inf (A : Ensemble ℝ) (l : ℝ) :=
  is_lub (fun x => almost_lower_bound A x) l.

Lemma lemma_8_18_d_i : lim_inf problem_8_1_i_set 0.
Proof. Abort.

Lemma lemma_8_18_d_ii : lim_inf problem_8_1_ii_set 0.
Proof. Abort.

Lemma lemma_8_18_d_iii : lim_inf problem_8_1_iii_set 0.
Proof. Abort.

Lemma lemma_8_18_d_iv : lim_inf problem_8_1_iv_set 0.
Proof. Abort.

Lemma lemma_8_18_d_v : ∀ l, ~ lim_inf problem_8_1_v_set l.
Proof. Abort.

Lemma lemma_8_18_d_vi : lim_inf problem_8_1_vi_set ((-1 - √5) / 2).
Proof. Abort.

Lemma lemma_8_18_d_vii : lim_inf problem_8_1_vii_set ((-1 - √5) / 2).
Proof. Abort.

Lemma lemma_8_18_d_viii : lim_inf problem_8_1_viii_set (-1).
Proof. Abort.
