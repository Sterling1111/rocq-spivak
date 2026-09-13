From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_18 : ∀ f g h k : R -> R,
  (∀ x y, f x * g y = h x * k y) <->
  (((∀ x, f x = 0) \/ (∀ y, g y = 0)) /\
   ((∀ x, h x = 0) \/ (∀ y, k y = 0))) \/
  (∃ c : R, c <> 0 /\ (∃ x, f x <> 0) /\ (∃ y, g y <> 0) /\
    (∀ x, h x = c * f x) /\ (∀ y, g y = c * k y)).
Proof.
  intros f g h k. split.
  - intro H1. destruct (classic (∀ x, f x = 0)) as [H2 | H2].
    + left. split; [auto |].
      destruct (classic (∀ x, h x = 0)) as [H3 | H3]; auto.
      right. apply not_all_ex_not in H3. destruct H3 as [x H3].
      intro y. pose proof (H1 x y). rewrite H2 in H. nra.
    + destruct (classic (∀ y, g y = 0)) as [H3 | H3].
      * left. split; [auto |].
        destruct (classic (∀ x, h x = 0)) as [H4 | H4]; auto.
        right. apply not_all_ex_not in H4. destruct H4 as [x H4].
        intro y. pose proof (H1 x y). rewrite H3 in H. nra.
      * right. apply not_all_ex_not in H2, H3.
        destruct H2 as [x H2], H3 as [y H3].
        pose proof (H1 x y) as H4.
        assert (H5 : h x <> 0 /\ k y <> 0) by (split; intro H5; rewrite H5 in H4; nra).
        destruct H5 as [H5 H6]. exists (h x / f x).
        split.
        -- unfold Rdiv. apply Rmult_integral_contrapositive_currified; auto.
           apply Rinv_neq_0_compat. exact H2.
        -- split; [exists x; exact H2 |]. split; [exists y; exact H3 |].
           assert (H7 : h x / f x * f x = h x) by (field; exact H2).
           split.
           ++ intro z. pose proof (H1 z y) as H8.
              assert (H9 : g y = h x / f x * k y) by nra. nra.
           ++ intro z. pose proof (H1 x z) as H8.
              apply Rmult_eq_reg_r with (r := f x); [|exact H2].
              replace (h x / f x * k z * f x) with ((h x / f x * f x) * k z) by ring.
              rewrite H7. nra.
  - intros [[[H1 | H1] [H2 | H2]] | [c [H1 [H2 [H3 [H4 H5]]]]]] x y;
    try rewrite H1; try rewrite H2; try rewrite H4; try rewrite H5; ring.
Qed.
