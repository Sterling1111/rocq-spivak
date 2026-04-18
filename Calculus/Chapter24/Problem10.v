From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_10_a : forall a, a > 0 -> exists f,
  uniform_limit (fun N x => ∑ 0 N (fun n => 2^n * sin (1 / (3^n * x)))) f (fun x => x >= a).
Abort.

Lemma lemma_24_10_b : forall f,
  ~ uniform_limit (fun N x => ∑ 0 N (fun n => 2^n * sin (1 / (3^n * x)))) f (fun x => x > 0).
Abort.
