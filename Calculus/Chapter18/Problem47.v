From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_47 : forall f g a,
  limit_at_point f a 1 ->
  limit_at_point g a ∞ ->
  limit_at_point (fun x => (f x)^(g x)) a (exp (limit_point (fun x => g x * log (f x)) a)).
Abort.
