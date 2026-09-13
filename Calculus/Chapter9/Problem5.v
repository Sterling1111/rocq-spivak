From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_5 : ∀ f x,
  f = (λ x, ((Int_part x)%Z : ℝ)) ->
  ((~ (∃ k : Z, x = (k : ℝ))) -> ⟦ der x ⟧ f = (λ _, 0)) /\
  ((∃ k : Z, x = (k : ℝ)) -> ~ differentiable_at f x).
Proof.
  intros f x H1. subst f. split.
  - intros H1.
    pose proof (base_Int_part x) as H2.
    assert (H3 : (Int_part x)%Z < x).
    { destruct H2 as [H2 H3]. destruct (Req_dec x (((Int_part x)%Z : ℝ))); [exfalso; apply H1; eauto | lra]. }
    apply limit_eq with (f1 := λ _, 0); [| apply limit_const].
    exists (Rmin (x - (Int_part x)%Z) ((Int_part x)%Z + 1 - x)).
    split; [solve_R |]. intros h H4.
    assert (H5 : Int_part x = Int_part (x + h)).
    { apply Int_part_spec. solve_R. }
    rewrite <- H5. lra.
  - intros [k H1] H2. subst x.
    apply differentiable_at_imp_continuous_at in H2.
    assert (H3 : k = Int_part (k : ℝ)).
    { apply Int_part_spec. lra. }
    destruct (H2 (1 / 2) ltac:(lra)) as [δ [H4 H5]].
    set (h := Rmin (δ / 2) (1 / 2)).
    assert (H6 : 0 < h < δ /\ h < 1) by (unfold h; solve_R).
    assert (H7 : (k - 1)%Z = Int_part (k - h)).
    { apply Int_part_spec. rewrite minus_IZR. simpl. lra. }
    specialize (H5 (k - h) ltac:(solve_R)).
    rewrite <- H3, <- H7, minus_IZR in H5. simpl in H5. solve_R.
Qed.
