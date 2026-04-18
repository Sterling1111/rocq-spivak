From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_1_i :
  let A := (λ x, ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\ is_glb A 0 /\ 0 ∉ A.
Proof. 
  intros A. repeat split; unfold A.
  - 
  intros x [n [H1 H2]]. subst. apply Rmult_le_reg_l with (r := n); field_simplify.
  replace 0 with (INR 0) by (reflexivity). apply lt_INR. solve_R.
  replace 1 with (INR 1) by reflexivity. apply le_INR. solve_R.
  intros H2. apply H1. replace 0 with (INR 0)  in H2 by reflexivity. solve_R.
Abort.

Lemma lemma_8_1_ii :
  let A := (λ x, ∃ n : ℤ, n ≠ 0%Z /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\
  is_glb A (-1) /\ (-1) ∈ A.
Proof. Abort.

Lemma lemma_8_1_iii :
  let A := (λ x, x = 0 \/ ∃ n : ℕ, n ≠ 0%nat /\ x = 1 / n) in
  is_lub A 1 /\ 1 ∈ A /\
  is_glb A 0 /\ 0 ∈ A.
Proof. Abort.

Lemma lemma_8_1_iv :
  let A := (λ x, 0 ≤ x /\ x ≤ √2 /\ rational x) in
  is_lub A (√2) /\ (√2) ∉ A /\
  is_glb A 0 /\ 0 ∈ A.
Proof. Abort.

Lemma lemma_8_1_v :
  let A := (λ x, x*x + x + 1 ≥ 0) in
  (∀ r : R, ¬ is_lub A r) /\
  (∀ r : R, ¬ is_glb A r).
Proof. Abort.

Lemma lemma_8_1_vi :
  let A := (λ x, x*x + x - 1 < 0) in
  is_lub A ((-1 + √5) / 2) /\
  is_glb A ((-1 - √5) / 2).
Proof. Abort.

Lemma lemma_8_1_vii :
  let A := (λ x, x < 0 /\ x*x + x - 1 < 0) in
  is_lub A 0 /\ 0 ∉ A /\
  is_glb A ((-1 - √5) / 2).
Proof. Abort.

Lemma lemma_8_1_viii :
  let A := (λ x, ∃ n : ℕ, x = 1 / (n + 1) + (-1)^n) in
  is_lub A 1 /\
  is_glb A (-1).
Proof. Abort.
