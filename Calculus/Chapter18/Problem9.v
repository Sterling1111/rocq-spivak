From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_9_a : forall x,
  x >= 1 ->
  sinh (arccosh x) = sqrt (x ^ 2 - 1).
Proof.
  intros x H1.
Abort.

Lemma lemma_18_9_b : forall x,
  cosh (arcsinh x) = sqrt (1 + x ^ 2).
Abort.

Lemma lemma_18_9_c :
  ⟦ der ⟧ arcsinh = (fun x => 1 / sqrt (1 + x ^ 2)).
Proof.
Abort.

Lemma lemma_18_9_d :
  ⟦ der ⟧ arccosh (1, ∞) = (fun x => 1 / sqrt (x ^ 2 - 1)).
Abort.

Lemma lemma_18_9_e :
  ⟦ der ⟧ arctanh (-1, 1) = (fun x => 1 / (1 - x ^ 2)).
Abort.
