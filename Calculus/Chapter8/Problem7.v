From Calculus.Chapter8 Require Import Prelude Problem6.
From Calculus.Chapter3 Require Import Problem16.

Lemma lemma_8_7 : ∀ f,
  continuous f -> (∀ x y, f (x + y) = f x + f y) -> ∃ c, ∀ x, f x = c * x.
Proof.
  intros f H1 H2.
  pose proof (lemma_3_16_b f H2) as [c H3].
  exists c.
  assert (H4 : dense rational).
  {
    intros x y H4. specialize (exists_rational_between x y H4) as [z [H5 H6]].
    exists z. split; auto.
  }
  assert (H5 : continuous (λ x, c * x)) by auto_cont.
  pose proof (lemma_8_6_b f (fun x => c * x) rational H1 H5 H4 H3) as H6.
  intros x.
  specialize (H6 x).
  simpl in H6.
  apply H6.
Qed.