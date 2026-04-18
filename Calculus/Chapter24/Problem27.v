From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_27 : forall fn f,
  (forall n, continuous_on (fn n) (fun x => 0 <= x <= 1)) ->
  uniform_limit fn f (fun x => 0 <= x <= 1) ->
  ⟦ lim ⟧ (fun n => ∫ 0 (1 - 1 / INR n) (fn n)) = ∫ 0 1 f.
Abort.
