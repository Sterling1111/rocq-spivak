From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_26 : forall f g a,
  limit_at_point (fun x => f x / g x) a (⟦ Der a ⟧ f / ⟦ Der a ⟧ g).
Abort.
