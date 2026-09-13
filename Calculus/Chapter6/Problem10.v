From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_10_a : ∀ f a,
  continuous_at f a -> continuous_at (λ x, |f x|) a.
Proof.
  intros f a H1 ε H2. destruct (H1 ε H2) as [δ [H3 H4]].
  exists δ. split; [lra|]. intros x H5.
  apply Rle_lt_trans with (r2 := |f x - f a|); [solve_R | apply H4; lra].
Qed.

Lemma lemma_6_10_b : ∀ f,
  continuous f ->
  ∃ E O, continuous E /\ (∀ x, E (-x) = E x) /\
              continuous O /\ (∀ x, O (-x) = - O x) /\
              (∀ x, f x = E x + O x).
Proof.
  intros f H1. exists (λ x, (f x + f (-x)) / 2), (λ x, (f x - f (-x)) / 2).
  assert (H2 : continuous (λ x, f (-x))).
  { apply continuous_comp; [auto_cont | exact H1]. }
  repeat split.
  - auto_cont.
  - intros x. rewrite Ropp_involutive. lra.
  - auto_cont.
  - intros x. rewrite Ropp_involutive. lra.
  - intros x. lra.
Qed.

Lemma lemma_6_10_c : ∀ f g,
  continuous f -> continuous g ->
  continuous (λ x, Rmax (f x) (g x)) /\ continuous (λ x, Rmin (f x) (g x)).
Proof.
  intros f g H1 H2. split; intros a.
  - apply continuous_at_ext with (f := λ x, (f x + g x + |f x - g x|) / 2).
    + intros x. solve_R.
    + auto_cont.
  - apply continuous_at_ext with (f := λ x, (f x + g x - |f x - g x|) / 2).
    + intros x. solve_R.
    + auto_cont.
Qed.

Lemma lemma_6_10_d : ∀ f,
  continuous f ->
  ∃ g h, continuous g /\ (∀ x, h x >= 0) /\
              continuous h /\ (∀ x, g x >= 0) /\
              (∀ x, f x = g x - h x).
Proof.
  intros f H1. exists (λ x, Rmax (f x) 0), (λ x, - Rmin (f x) 0).
  destruct (lemma_6_10_c f (λ _, 0) H1 ltac:(auto_cont)) as [H2 H3].
  repeat split.
  - exact H2.
  - intros x. solve_R.
  - apply continuous_neg. exact H3.
  - intros x. solve_R.
  - intros x. solve_R.
Qed.
