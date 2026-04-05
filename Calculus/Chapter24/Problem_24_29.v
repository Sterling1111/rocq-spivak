From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_29_a : forall fn f a b,
  (forall n, continuous_on (fn n) (fun x => a <= x <= b)) ->
  uniform_limit fn f (fun x => a <= x <= b) ->
  forall (xn : nat -> R) x,
  (forall n, a <= xn n <= b) -> a <= x <= b ->
  ⟦ lim ⟧ xn = x -> ⟦ lim ⟧ (fun n => fn n (xn n)) = f x.
Admitted.

Lemma lemma_24_29_c : forall fn f a b,
  continuous_on f (fun x => a <= x <= b) ->
  (forall (xn : nat -> R) x,
    (forall n, a <= xn n <= b) -> a <= x <= b ->
    ⟦ lim ⟧ xn = x -> ⟦ lim ⟧ (fun n => fn n (xn n)) = f x) ->
  uniform_limit fn f (fun x => a <= x <= b).
Admitted.
