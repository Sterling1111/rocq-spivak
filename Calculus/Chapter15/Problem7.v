From Calculus.Chapter15 Require Import Prelude.

(* Problem 7 *)

(* (a) Double and triple angle formulas *)
Lemma lemma_15_7_a_sin2x : forall x,
  sin (2 * x) = 2 * sin x * cos x.
Abort.

Lemma lemma_15_7_a_cos2x : forall x,
  cos (2 * x) = (cos x)^2 - (sin x)^2.
Abort.

Lemma lemma_15_7_a_sin3x : forall x,
  sin (3 * x) = 3 * sin x - 4 * (sin x)^3.
Abort.

Lemma lemma_15_7_a_cos3x : forall x,
  cos (3 * x) = 4 * (cos x)^3 - 3 * cos x.
Abort.

(* (b) Values of trigonometric functions *)
Lemma lemma_15_7_b_sin_pi_4 : sin (π / 4) = √2 / 2.
Abort.

Lemma lemma_15_7_b_cos_pi_4 : cos (π / 4) = √2 / 2.
Abort.

Lemma lemma_15_7_b_tan_pi_4 : tan (π / 4) = 1.
Abort.

Lemma lemma_15_7_b_sin_pi_6 : sin (π / 6) = 1 / 2.
Abort.

Lemma lemma_15_7_b_cos_pi_6 : cos (π / 6) = √3 / 2.
Abort.
