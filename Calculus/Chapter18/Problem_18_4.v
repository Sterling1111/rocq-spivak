From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_4 : forall f,
  f = (fun x => exp x) \/ f = (fun x => log x) ->
  exists c, f c = 0 \/ forall x, f x > 0.
Admitted.
