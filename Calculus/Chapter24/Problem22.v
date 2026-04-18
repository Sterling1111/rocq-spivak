From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_22 : forall a, 0 < a < 1 ->
  uniform_limit (fun N x => ∑ 0 N (fun n => x^(2*n+1) / INR (2*n+1) - x^(n+1) / INR (2*n+2)))
                (fun x => 1 / 2 * ln (x + 1))
                (fun x => -a <= x <= a) /\ ∑ 0 ∞ (fun n => 1^n / INR (2*n+1) - 1^n / INR (2*n+2)) = (ln 2).
Abort.
