From Calculus.Chapter8 Require Import Prelude.

Definition problem_8_1_i_set : Ensemble ℝ :=
  fun x => ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n.

Definition problem_8_1_ii_set : Ensemble ℝ :=
  fun x => ∃ n : ℤ, n ≠ 0%Z /\ x = 1 / n.

Definition problem_8_1_iii_set : Ensemble ℝ :=
  fun x => x = 0 \/ ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n.

Definition problem_8_1_iv_set : Ensemble ℝ :=
  fun x => 0 <= x /\ x <= √2 /\ rational x.

Definition problem_8_1_v_set : Ensemble ℝ :=
  fun x => x * x + x + 1 > 0.

Definition problem_8_1_vi_set : Ensemble ℝ :=
  fun x => x * x + x - 1 < 0.

Definition problem_8_1_vii_set : Ensemble ℝ :=
  fun x => x < 0 /\ x * x + x - 1 < 0.

Definition problem_8_1_viii_set : Ensemble ℝ :=
  fun x => ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n + (-1) ^ n.

Lemma lemma_8_1_i :
  is_lub problem_8_1_i_set 1 /\
  1 ∈ problem_8_1_i_set /\
  is_glb problem_8_1_i_set 0 /\
  0 ∉ problem_8_1_i_set.
Proof. Abort.

Lemma lemma_8_1_ii :
  is_lub problem_8_1_ii_set 1 /\
  1 ∈ problem_8_1_ii_set /\
  is_glb problem_8_1_ii_set (-1) /\
  (-1) ∈ problem_8_1_ii_set.
Proof. Abort.

Lemma lemma_8_1_iii :
  is_lub problem_8_1_iii_set 1 /\
  1 ∈ problem_8_1_iii_set /\
  is_glb problem_8_1_iii_set 0 /\
  0 ∈ problem_8_1_iii_set.
Proof. Abort.

Lemma lemma_8_1_iv :
  is_lub problem_8_1_iv_set (√2) /\
  (√2) ∉ problem_8_1_iv_set /\
  is_glb problem_8_1_iv_set 0 /\
  0 ∈ problem_8_1_iv_set.
Proof. Abort.

Lemma lemma_8_1_v :
  (∀ r : ℝ, ¬ is_lub problem_8_1_v_set r) /\
  (∀ r : ℝ, ¬ is_glb problem_8_1_v_set r).
Proof. Abort.

Lemma lemma_8_1_vi :
  is_lub problem_8_1_vi_set ((-1 + √5) / 2) /\
  ((-1 + √5) / 2) ∉ problem_8_1_vi_set /\
  is_glb problem_8_1_vi_set ((-1 - √5) / 2) /\
  ((-1 - √5) / 2) ∉ problem_8_1_vi_set.
Proof. Abort.

Lemma lemma_8_1_vii :
  is_lub problem_8_1_vii_set 0 /\
  0 ∉ problem_8_1_vii_set /\
  is_glb problem_8_1_vii_set ((-1 - √5) / 2) /\
  ((-1 - √5) / 2) ∉ problem_8_1_vii_set.
Proof. Abort.

Lemma lemma_8_1_viii :
  is_lub problem_8_1_viii_set (3 / 2) /\
  (3 / 2) ∈ problem_8_1_viii_set /\
  is_glb problem_8_1_viii_set (-1) /\
  (-1) ∉ problem_8_1_viii_set.
Proof. Abort.
