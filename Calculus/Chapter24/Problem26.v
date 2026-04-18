From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_26_a : forall fn f a b,
  (forall n, integrable_on a b (fn n)) ->
  uniform_limit fn f (fun x => a <= x <= b) ->
  integrable_on a b f.
Abort.

Lemma lemma_24_26_d : exists f,
  uniform_limit (fun N x => ∑ 1 N (fun n => (-1)^n / (x + INR n))) f (fun x => x >= 0).
Abort.
