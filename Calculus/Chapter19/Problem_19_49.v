From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_49 : forall f a b,
  exists Q,
    (exists A B C D, forall x, Q x = A * x^3 + B * x^2 + C * x + D) /\
    Q a = f a /\
    Q b = f b /\
    Q ((a + b) / 2) = f ((a + b) / 2) /\
    ⟦ der ⟧ Q ((a + b) / 2) = ⟦ der ⟧ f ((a + b) / 2).
Admitted.
