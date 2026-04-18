From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_12_a : forall ε, 0 < ε -> ε < π -> exists f,
  uniform_limit (fun N x => ∑ 1 N (fun n => sin (INR n * x) / INR n)) f (fun x => ε <= x <= 2 * π - ε).
Abort.

Lemma lemma_24_12_b : forall f,
  ~ uniform_limit (fun N x => ∑ 1 N (fun n => sin (INR n * x) / INR n)) f (fun x => 0 <= x <= 2 * π).
Abort.
