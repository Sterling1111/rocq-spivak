From Calculus.Chapter14 Require Import Prelude.

Section section_14_9.

  Variable f : ℝ -> ℝ.
  Variable a b c : ℝ.

  Hypothesis H1 : a < b.
  Hypothesis H2 : c ∈ (a, b).
  Hypothesis H3 : integrable_on a b f.

  Definition F := λ x, ∫ a x f.

  Lemma lemma_14_9_a : differentiable_at f c -> differentiable_at F c.
  Proof.
    intros H4.
    pose proof differentiable_at_imp_continuous_at f c H4 as H5.
  Admitted.


End section_14_9.

Lemma lemma_14_19_a : forall f a b c,
  a < b ->
  c ∈ (a, b) ->
  integrable_on a b f ->
  differentiable_at f c ->
  differentiable_at (fun x => ∫ a x f) c.
Abort.

(* (b) If f is differentiable at c, then F' is continuous at c. *)
(* This is actually true *)
Lemma lemma_14_19_b : forall f a b c,
  a < b ->
  c ∈ (a, b) ->
  integrable_on a b f ->
  differentiable_at f c ->
  continuous_at (⟦ Der ⟧ (fun x => ∫ a x f)) c.
Abort.

(* (c) If f' is continuous at c, then F' is continuous at c. *)
Lemma lemma_14_19_c : forall f f' a b c,
  a < b ->
  c ∈ (a, b) ->
  integrable_on a b f ->
  ⟦ der ⟧ f = f' ->
  continuous_at f' c ->
  continuous_at (⟦ Der ⟧ (fun x => ∫ a x f)) c.
Abort.
