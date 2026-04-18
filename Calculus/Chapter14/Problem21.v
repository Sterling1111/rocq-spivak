From Calculus.Chapter14 Require Import Prelude.

(* Problem 21: Suppose f' is integrable on [0, 1] and f(0) = 0.
   Prove that for all x in [0, 1], |f(x)| ≤ √(∫ 0 1 |f'|^2). *)

Lemma lemma_14_21 : forall f f',
  ⟦ der ⟧ f [0, 1] = f' ->
  f 0 = 0 ->
  integrable_on 0 1 (fun x => (f' x)^2) ->
  forall x, x ∈ [0, 1] ->
  |f x| <= √(∫ 0 1 (fun x => |f' x|^2)).
Abort.
