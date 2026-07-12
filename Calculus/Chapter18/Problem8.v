From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_8_a : forall x,
  (cosh x)^2 - (sinh x)^2 = 1.
Proof.
  admit.
Abort.

Lemma lemma_18_8_b : forall x,
  (tanh x)^2 + 1 / (cosh x)^2 = 1.
Proof.
  admit.
Abort.

Lemma lemma_18_8_c : forall x y,
  sinh (x + y) = sinh x * cosh y + cosh x * sinh y.
Proof.
  admit.
Abort.

Lemma lemma_18_8_d : forall x y,
  cosh (x + y) = cosh x * cosh y + sinh x * sinh y.
Proof.
  admit.
Abort.

Lemma lemma_18_8_e :
  ⟦ der ⟧ sinh = cosh.
Proof.
  auto_diff.
Qed.

Lemma lemma_18_8_f :
  ⟦ der ⟧ cosh = sinh.
Proof.
  auto_diff.
Qed.

Lemma lemma_18_8_g :
  ⟦ der ⟧ tanh = fun x => 1 / (cosh x)^2.
Proof.
  auto_diff.
Qed.