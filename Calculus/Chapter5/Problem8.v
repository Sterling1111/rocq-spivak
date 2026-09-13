From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_8_a : ∃ (f g : R -> R) (a L1 L2 : R),
  (∀ Lf, ¬ (⟦ lim a ⟧ f = Lf)) /\ (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) /\
  ⟦ lim a ⟧ (f + g) = L1 /\
  ⟦ lim a ⟧ (f ⋅ g) = L2.
Proof.
  exists (λ x, |x| / x), (λ x, - |x| / x), 0, 0, (-1).
  repeat split.
  - intros Lf H1. specialize (H1 (1/2) ltac:(lra)) as [δ [H2 H3]].
    specialize (H3 (δ/2) ltac:(solve_R)) as H4.
    specialize (H3 (-δ/2) ltac:(solve_R)) as H5.
    rewrite Rabs_pos_eq with (x := δ/2) in H4; try lra.
    rewrite Rabs_left with (r := -δ/2) in H5; try lra.
    field_simplify in H4; try lra.
    field_simplify in H5; solve_R.
  - intros Lg H1. specialize (H1 (1/2) ltac:(lra)) as [δ [H2 H3]].
    specialize (H3 (δ/2) ltac:(solve_R)) as H4.
    specialize (H3 (-δ/2) ltac:(solve_R)) as H5.
    rewrite Rabs_pos_eq with (x := δ/2) in H4; try lra.
    rewrite Rabs_left with (r := -δ/2) in H5; try lra.
    field_simplify in H4; try lra.
    field_simplify in H5; solve_R.
  - apply limit_eq with (f1 := λ _, 0); [ | auto_limit ].
    exists 1; split; solve_R.
  - apply limit_eq with (f1 := λ _, -1); [ | auto_limit ].
    exists 1; split; solve_R.
Qed.

Lemma lemma_5_8_a_2 : ∃ (f g : R -> R) (a L : R),
  (∀ Lf, ¬ (⟦ lim a ⟧ f = Lf)) /\ (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) /\
  ⟦ lim a ⟧ (λ x, f x * g x) = L.
Proof.
  destruct lemma_5_8_a as [f [g [a [L1 [L2 [H1 [H2 [H3 H4]]]]]]]].
  exists f, g, a, L2. auto.
Qed.

Lemma lemma_5_8_b : ∀ (f g : R -> R) (a L L_sum : R),
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (λ x, f x + g x) = L_sum ->
  ∃ Lg, ⟦ lim a ⟧ g = Lg.
Proof.
  intros f g a L L_sum H1 H2. exists (L_sum - L).
  apply limit_eq with (f1 := λ x, (f x + g x) - f x).
  - exists 1. split; [lra | intros x H3; lra].
  - apply limit_minus; auto.
Qed.

Lemma lemma_5_8_c : ∀ (f g : R -> R) (a L : R),
  ⟦ lim a ⟧ f = L -> (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) ->
  ∀ L_sum, ¬ (⟦ lim a ⟧ (λ x, f x + g x) = L_sum).
Proof.
  intros f g a L H1 H2 L_sum H3.
  destruct (lemma_5_8_b f g a L L_sum H1 H3) as [Lg H4].
  apply (H2 Lg H4).
Qed.

Lemma lemma_5_8_d : ∃ (f g : R -> R) (a L L_prod : R),
  ⟦ lim a ⟧ f = L /\ ⟦ lim a ⟧ (λ x, f x * g x) = L_prod /\
  (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)).
Proof.
  set (g := λ x : R, if excluded_middle_informative (rational x) then 0 else 1).
  exists (λ x, x), g, 0, 0, 0. repeat split.
  - apply limit_id.
  - intros ε H1. exists ε. split; auto. intros x H2.
    unfold g. destruct (excluded_middle_informative (rational x)); solve_R.
  - intros Lg H1. specialize (H1 (1/3) ltac:(lra)) as [δ [H2 H3]].
    destruct (exists_rational_between 0 δ ltac:(lra)) as [x [H4 H5]].
    destruct (exists_irrational_between 0 δ ltac:(lra)) as [y [H6 H7]].
    specialize (H3 x ltac:(solve_R)) as H8.
    specialize (H3 y ltac:(solve_R)) as H9.
    unfold g in H8, H9.
    destruct (excluded_middle_informative (rational x)); try contradiction.
    destruct (excluded_middle_informative (rational y)); try contradiction.
    solve_R.
Qed.
