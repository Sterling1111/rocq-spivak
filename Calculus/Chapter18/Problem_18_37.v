From Calculus.Chapter18 Require Import Prelude.

(* Problem 37: Prove that if f is continuous and f(x+y) = f(x)f(y) for all x and y, then either f = 0 or f(x) = [f(1)]^x for all x. *)
Lemma problem_18_37 : forall f, continuous f -> (forall x y, f (x + y) = f x * f y) ->
  f = (fun _ => 0) \/ exists a, f = fun x => a^x. Admitted.
