From Calculus.Chapter11 Require Import Prelude.

Section Section_10_8.

Definition Area (r : ℝ) := π * r^2.
Definition Circumference (r : ℝ) := 2*π*r.

Variable r : ℝ -> ℝ.
Hypothesis H1 : forall t, r t > 0.

Definition A_S (t : ℝ) := Area (r t).
Definition C_S (t : ℝ) := Circumference (r t).

Definition A_L (t : ℝ) := A_S t + 9*π.

Variable r' : ℝ -> ℝ.
Hypothesis H2 : ⟦ der ⟧ r = r'.

Lemma A_S_derivative : ⟦ der ⟧ A_S = (fun t => 2 * π * r t * r' t).
Proof.
  unfold A_S, Area. auto_diff.
Qed.

Lemma A_L_derivative : ⟦ der ⟧ A_L = (fun t => 2 * π * r t * r' t).
Proof.
  unfold A_L, A_S, Area. auto_diff.
Qed.

Lemma C_S_derivative : ⟦ der ⟧ C_S = (fun t => 2 * π * r' t).
Proof.
  unfold C_S, Circumference. auto_diff.
Qed.

Variable t0 : ℝ.

Hypothesis H3 : 2 * π * r t0 * r' t0 = 10 * π.

Hypothesis H4 : A_S t0 = 16 * π.

Lemma lemma_10_8 : 2 * π * r' t0 = 5 * π / 2.
Proof.
  unfold A_S, Area in H4.
  pose proof (H1 t0) as H5.
  pose proof π_pos as H6.
  nra.
Qed.

End Section_10_8.