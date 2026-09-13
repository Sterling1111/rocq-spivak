From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_17 : ∀ l,
  let f := λ x, polynomial l x in
  ∃ y, ∀ x, | f y | <= | f x |.
Proof.
  intros l f.
  set (p := poly_mul l l).
  assert (H1 : ∀ x, polynomial p x = (f x)^2).
  { intros x. unfold p, f. rewrite eval_poly_mul. ring. }
  assert (H2 : ∀ x, polynomial p x >= 0).
  { intros x. rewrite H1. nra. }
  destruct (Nat.eq_dec (degree p) 0) as [H3 | H3].
  - assert (H4 : ∀ q, degree q = 0%nat -> ∀ x, polynomial q x = polynomial q 0).
    {
      intros q. induction q as [| c q IH]; intros H4 x.
      - rewrite !poly_nil. reflexivity.
      - simpl in H4. destruct (Req_EM_T c 0) as [H5 | H5].
        + subst c. rewrite !poly_cons_0_eval. apply IH; auto.
        + assert (H6 : q = []) by (apply length_zero_iff_nil; lia).
          subst q. rewrite !poly_const_eval. reflexivity.
    }
    exists 0. intros x. pose proof (H4 p H3 x) as H5.
    rewrite !H1 in H5. solve_R.
  - assert (H4 : ~ is_zero_poly p) by (apply not_zero_poly_degree_gt_0; lia).
    destruct (polynomial_even_limit p (polynomial_pos_imp_even p H2)
      ltac:(lia) (polynomial_pos_imp_lead_coeff_pos p H4 H2)) as [H5 H6].
    destruct (continuous_limit_pinf_minf_global_min (polynomial p)
      (continuous_polynomial p) H5 H6) as [y H7].
    exists y. intros x. specialize (H7 x). rewrite !H1 in H7. solve_R.
Qed.
