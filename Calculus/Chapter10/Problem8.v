From Calculus.Chapter11 Require Import Prelude.

Section Section_10_8.

Definition Area (r : ℝ) := π*r^2.
Definition Circumference (r : ℝ) := 2*π*r.

Variable r1 r2 r1' r2' : ℝ -> ℝ.

Hypothesis H1 : ∀ t, r1 t > 0.
Hypothesis H2 : ∀ t, r2 t > 0.
Hypothesis H3 : ∀ t, r1 t < r2 t.
Hypothesis H4 : ⟦ der ⟧ r1 = r1'.
Hypothesis H5 : ⟦ der ⟧ r2 = r2'.

Definition A1 (t : ℝ) := Area (r1 t).
Definition A2 (t : ℝ) := Area (r2 t).
Definition A1' := (fun t => 2 * π * r1 t * r1' t).
Definition A2' := (fun t => 2 * π * r2 t * r2' t).

Lemma A1_derivative : ⟦ der ⟧ A1 = A1'.
Proof.
  unfold A1, Area, A1'. auto_diff.
Qed.

Lemma A2_derivative : ⟦ der ⟧ A2 = A2'.
Proof.
  unfold A2, Area, A2'. auto_diff.
Qed.

Hypothesis H6 : ∀ t, A2 t - A1 t = 9*π.
Hypothesis H7 : ∀ t, A2' t = 10*π.

Lemma rate_relation : ∀ t, 10*π - 2*π * r1 t * r1' t = 0.
Proof.
  intros t.
  
  assert (H8 : A2 = (fun t => A1 t + 9 * π)).
  { extensionality x. pose proof (H6 x). lra. }
  
  assert (H9 : ⟦ der ⟧ A2 = A1').
  { rewrite H8. unfold A1, A1', Area. auto_diff. }
  
  pose proof derivative_at_unique A2 A2' A1' t (A2_derivative t) (H9 t) as H10.

  rewrite H7 in H10.
  unfold A1' in H10.
  lra.
Qed.

Definition C1 (t : ℝ) := Circumference (r1 t).
Definition C1' := (fun t => 2 * π * r1' t).

Lemma C1_derivative : ⟦ der ⟧ C1 = C1'.
Proof.
  unfold C1, Circumference, C1'. auto_diff.
Qed.

Variable t : ℝ.

Hypothesis H8 : A1 t = 16 * π.

Lemma lemma_10_8 : C1' t = 5 * π / 2.
Proof.
  unfold C1', A1, Area in *.
  pose proof (rate_relation t) as H9.
  pose proof (H1 t) as H10.
  pose proof π_pos as H11.

  assert (H12 : r1 t = 4).
  {
    unfold A1, Area in H8.
    apply Rmult_eq_compat_r with (r := / (π)) in H8.
    field_simplify in H8; nra.
  }

  assert (H13 : r1' t = 5 / 4).
  { rewrite H12 in H9. nra. }

  rewrite H13. field.
Qed.

End Section_10_8.