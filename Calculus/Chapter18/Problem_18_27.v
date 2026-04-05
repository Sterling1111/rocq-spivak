From Calculus.Chapter18 Require Import Prelude.

(* Problem 27: Gronwall's inequality *)
Lemma problem_18_27_a : forall f g a C,
  (forall x, f x <= C + ∫ a x (fun t => f t * g t)) ->
  (forall x, f x <= C * exp (∫ a x g)). Admitted.

Lemma problem_18_27_b : forall f g,
  (forall x, 0 <= f x) -> (forall x, 0 <= g x) ->
  ⟦ der ⟧ f = (fun x => g x * f x) -> f 0 = 0 ->
  f = fun _ => 0. Admitted.
