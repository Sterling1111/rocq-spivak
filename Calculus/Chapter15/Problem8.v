From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_8_a : ∀ A B,
  ∃ a b, ∀ x,
    A * sin (x + B) = a * sin x + b * cos x.
Proof.
  intros A B. exists (A * cos B), (A * sin B).
  intro x. rewrite sin_plus. ring.
Qed.

Lemma lemma_15_8_b : ∀ a b,
  ∃ A B, ∀ x,
    a * sin x + b * cos x = A * sin (x + B).
Proof.
  intros a b.
  destruct (Req_dec a 0) as [H1 | H1].
  - exists b, (π / 2). intro x.
    rewrite sin_plus, cos_π_over_2, sin_π_over_2. subst a. ring.
  - set (B := arctan (b / a)).
    assert (H2 : 0 < cos B) by (unfold B; apply cos_arctan_pos).
    assert (H3 : tan B = b / a) by (apply arctan_spec; apply Full_intro).
    exists (a / cos B), B. intro x. rewrite sin_plus.
    unfold tan in H3.
    assert (H4 : a * sin B = b * cos B).
    { apply Rmult_eq_compat_r with (r := a * cos B) in H3.
      field_simplify in H3; nra. }
    apply Rmult_eq_reg_r with (r := cos B); [| lra].
    field_simplify; [pose proof (Rmult_eq_compat_r (cos x) _ _ H4); nra | lra].
Qed.
