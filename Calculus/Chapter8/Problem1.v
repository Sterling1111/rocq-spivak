From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_1_i :
  let A := (λ x : ℝ, ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\
  is_glb A 0 /\ 0 ∉ A.
Proof. 
  intros A. repeat split; unfold A.
  - intros x [n [H1 H2]]. subst. solve_R.
  - admit.
Abort.

Lemma lemma_8_1_ii :
  let A := (λ x : ℝ, ∃ n : ℤ, n ≠ 0%Z /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\
  is_glb A (-1) /\ (-1) ∈ A.
Proof.
  intros A. repeat split; unfold A.
  - intros x [n [H1 H2]]. subst. solve_R.
Abort.

Lemma lemma_8_1_iii :
  let A := (λ x : ℝ,
    x = 0 \/ ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\
  is_glb A 0 /\ 0 ∈ A.
Proof. Abort.

Lemma lemma_8_1_iv :
  let A := (λ x : ℝ,
    0 ≤ x /\ x ≤ √2 /\ rational x) in
  is_lub A (√2) /\ (√2) ∉ A /\
  is_glb A 0 /\ 0 ∈ A.
Proof. Abort.

Lemma lemma_8_1_v :
  let A := (λ x : ℝ, x * x + x + 1 ≥ 0) in
  (∀ r : ℝ, ¬ is_lub A r) /\
  (∀ r : ℝ, ¬ is_glb A r).
Proof. Abort.

Lemma lemma_8_1_vi :
  let A := (λ x : ℝ, x * x + x - 1 < 0) in
  is_lub A ((-1 + √5) / 2) /\
  ((-1 + √5) / 2) ∉ A /\
  is_glb A ((-1 - √5) / 2) /\
  ((-1 - √5) / 2) ∉ A.
Proof. Abort.

Lemma lemma_8_1_vii :
  let A := (λ x : ℝ,
    x < 0 /\ x * x + x - 1 < 0) in
  is_lub A 0 /\ 0 ∉ A /\
  is_glb A ((-1 - √5) / 2) /\
  ((-1 - √5) / 2) ∉ A.
Proof. Abort.

Lemma lemma_8_1_viii :
  let A := (λ x : ℝ,
    ∃ n : ℕ,
      n ≠ 0%nat /\
      x = 1 / n + (-1 : ℝ) ^ n) in
  is_lub A (3 / 2) /\ (3 / 2) ∈ A /\
  is_glb A (-1) /\ (-1) ∉ A.
Proof. Abort.
