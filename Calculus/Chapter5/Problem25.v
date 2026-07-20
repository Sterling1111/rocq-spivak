From Calculus.Chapter5 Require Import Prelude.

Definition def_5_25_i (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < ε → |f x - l| < δ.

Definition def_5_25_ii (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < ε → |f x - l| <= δ.

Definition def_5_25_iii (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < ε → |f x - l| <= 5 * δ.

Definition def_5_25_iv (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < ε / 10 → |f x - l| < δ.

Lemma lemma_5_25_i : ∀ f a l, ⟦ lim a ⟧ f = l <-> def_5_25_i f a l.
Proof.
  intros f a l. split;
  (intros H1 ε H2;
  specialize (H1 ε H2) as [δ [H1 H3]];
  exists δ; split; [ solve_R | intros x H4 ];
  apply H3; solve_R).
Qed.

Lemma lemma_5_25_ii : ∀ f a l, ⟦ lim a ⟧ f = l <-> def_5_25_ii f a l.
Proof.
  intros f a l. split.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ. split; [solve_R|].
    intros x H5.
    specialize (H4 x H5).
    lra.
  - intros H1 ε H2.
    specialize (H1 (ε / 2)) as [δ [H3 H4]].
    { solve_R. }
    exists δ. split; [solve_R|].
    intros x H5.
    specialize (H4 x H5).
    solve_R.
Qed.

Lemma lemma_5_25_iii : ∀ f a l, ⟦ lim a ⟧ f = l <-> def_5_25_iii f a l.
Proof.
  intros f a l. split.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ. split; [solve_R|].
    intros x H5.
    specialize (H4 x H5).
    solve_R.
  - intros H1 ε H2.
    specialize (H1 (ε / 10)) as [δ [H3 H4]].
    { solve_R. }
    exists δ. split; [solve_R|].
    intros x H5.
    specialize (H4 x H5).
    solve_R.
Qed.

Lemma lemma_5_25_iv : ∀ f a l, ⟦ lim a ⟧ f = l <-> def_5_25_iv f a l.
Proof.
  intros f a l. split.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists (10 * δ). split.
    + solve_R.
    + intros x H5.
      apply H4.
      solve_R.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists (δ / 10). split.
    + solve_R.
    + intros x H5.
      apply H4.
      solve_R.
Qed.