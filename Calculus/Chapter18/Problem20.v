From Calculus.Chapter18 Require Import Prelude.

(* Problem 20: Suppose that on some interval the function f satisfies f' = cf for some number c. *)
Lemma problem_18_20 : forall f c, ⟦ der ⟧ f = (fun x => c * f x) -> exists A, forall x, f x = A * exp (c * x). Abort.
