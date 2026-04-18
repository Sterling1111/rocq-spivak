From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_2_i : forall x,
  x^2 - 4*x - 9 = -12 + 2*(x - 3) + (x - 3)^2.
Abort.

Lemma lemma_20_2_ii : forall x,
  x^4 - 12*x^3 + 44*x^2 + 2*x + 1 = 160 + 50*(x - 3) - 10*(x - 3)^2 + (x - 3)^4.
Abort.

Lemma lemma_20_2_iii : forall x,
  x^5 = 243 + 405*(x - 3) + 270*(x - 3)^2 + 90*(x - 3)^3 + 15*(x - 3)^4 + (x - 3)^5.
Abort.

Lemma lemma_20_2_iv : forall a b c x,
  a*x^2 + b*x + c = (9*a + 3*b + c) + (6*a + b)*(x - 3) + a*(x - 3)^2.
Abort.
