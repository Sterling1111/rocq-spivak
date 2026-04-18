From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_9 : exists f,
  uniform_limit (fun N x => ∑ 1 N (fun n => x / (INR n * (1 + INR n * x^2)))) f (Full_set R).
Abort.
