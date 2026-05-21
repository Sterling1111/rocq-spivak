From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_25_even : forall f k,
  even f -> 
  even (⟦ Der ^ (2 * k) ⟧ f) /\ odd (⟦ Der ^ (2 * k + 1) ⟧ f).
Proof.
  intros f k H1. (* I have crippling depression *)
Abort.

Lemma lemma_9_25_odd : forall f k,
  odd_f f -> 
  odd_f (⟦ Der ^ (2 * k) ⟧ f) /\ even_f (⟦ Der ^ (2 * k + 1) ⟧ f).
Proof.
Abort.
