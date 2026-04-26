From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_21 : forall x y,
  exp (x + y) = exp x * exp y.
Proof.
  intros x y.
  Search (exp).
Abort.
