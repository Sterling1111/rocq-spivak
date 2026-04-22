From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_26_i : ⟦ der ^ 2 ⟧ (fun x => x^3) = (fun x => 6 * x).
Proof.
  auto_diff.
Qed.

Lemma lemma_9_26_ii : ⟦ der ^ 2 ⟧ (fun x => x^5) = (fun x => 20 * x ^3).
Proof.
  auto_diff.
Qed.

Lemma lemma_9_26_iii : forall f,
  ⟦ der ⟧ f = (fun x => x^4) -> ⟦ der ^ 2 ⟧ f = (fun x => 4 * x^3).
Proof.
  auto_diff.
Qed.

Lemma lemma_9_26_iv : forall f,
  (forall x, f (x + 3) = x^5) -> ⟦ der ^ 2 ⟧ f = (fun x => 20 * (x - 3)^3).
Proof.
  intros f H1.
  replace f with (fun x => (x - 3)^5).
  - auto_diff.
  - extensionality x. 
    replace x with ((x - 3) + 3) at 1 by lra.
    rewrite <- H1. replace (x - 3 + 3 - 3 + 3) with x by lra.
    reflexivity.
Qed.