From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_14_a_1 : forall x y,
  sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2).
Proof.
  intros x y.
  set (a := (x + y) / 2).
  set (b := (x - y) / 2).
  replace x with (a + b) by (unfold a, b; lra).
  replace y with (a - b) by (unfold a, b; lra).
  rewrite sin_plus, sin_minus. lra.
Qed.

Lemma lemma_15_14_a_2 : forall x y,
  sin x - sin y = 2 * sin ((x - y) / 2) * cos ((x + y) / 2).
Proof.
  intros x y.
  set (a := (x + y) / 2).
  set (b := (x - y) / 2).
  replace x with (a + b) by (unfold a, b; lra).
  replace y with (a - b) by (unfold a, b; lra).
  rewrite sin_plus, sin_minus. lra.
Qed.

Lemma lemma_15_14_b_1 : forall x y,
  cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2).
Proof.
  intros x y.
  set (a := (x + y) / 2).
  set (b := (x - y) / 2).
  replace x with (a + b) by (unfold a, b; lra).
  replace y with (a - b) by (unfold a, b; lra).
  rewrite cos_plus, cos_minus. lra.
Qed.

Lemma lemma_15_14_b_2 : forall x y,
  cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2).
Proof.
  intros x y.
  set (a := (x + y) / 2).
  set (b := (x - y) / 2).
  replace x with (a + b) by (unfold a, b; lra).
  replace y with (a - b) by (unfold a, b; lra).
  rewrite cos_plus, cos_minus. lra.
Qed.