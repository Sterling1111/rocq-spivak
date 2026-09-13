From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_11 : ∃ f : R -> R,
  ⟦ der^2 ⟧ f = (λ x, 1 / √(1 + (sin x)^2)).
Proof.
  set (g := λ x, 1 / √(1 + (sin x)^2)).
  set (F := λ x, ∫ 0 x g).
  assert (H1 : continuous g) by (unfold g; auto_cont).
  assert (H2 : ⟦ der ⟧ F = g) by (unfold F; apply FTC1_global; auto).
  assert (H3 : continuous F).
  { apply differentiable_imp_continuous. apply derivative_imp_differentiable with (f' := g). auto. }
  exists (λ x, ∫ 0 x F).
  exists F. split; [| exact H2].
  exists (λ x, ∫ 0 x F). split; [reflexivity |].
  apply FTC1_global. auto.
Qed.
