From Calculus.Chapter18 Require Import Prelude.

(* Problem 42: Suppose that f satisfies f'' - f = 0 and f(0) = f'(0) = 0. Prove that f = 0. *)
Lemma problem_18_42 : forall f, ⟦ der ⟧ (⟦ der ⟧ f) = f -> f 0 = 0 -> ⟦ der ⟧ f 0 = 0 ->
  f = fun _ => 0. Abort.
