From Calculus.Chapter18 Require Import Prelude.

(* P starts at A. The Napierian logarithm is defined by elapsed time;
   nonnegative times cover distances 0 < x <= 10^7. *)
Lemma lemma_18_33 : ∀ P Naplog,
  P 0 = 0 -> ⟦ der ⟧ P = (λ t, 10^7 - P t) ->
  (∀ t, 0 <= t -> Naplog (10^7 - P t) = 10^7 * t) ->
  ∀ x, 0 < x <= 10^7 -> Naplog x = 10^7 * log (10^7 / x).
Abort.
