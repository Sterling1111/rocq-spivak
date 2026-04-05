From Calculus.Chapter23 Require Import Prelude.

(* Problem 5 *)

(* (a) Prove that if \sum_{n=1}^{\infty} a_n converges absolutely, then so does \sum_{n=1}^{\infty} {a_n}^2. *)
Lemma problem_23_5_a : forall a,
  (exists S, ∑ 0 ∞ (fun n => |a n|) = S) ->
  exists S, ∑ 0 ∞ (fun n => |a n ^ 2|) = S.
Admitted.

(* (b) Show that this does not hold for conditional convergence. *)
Lemma problem_23_5_b :
  ~ (forall a, (exists S, ∑ 0 ∞ a = S) -> (exists S, ∑ 0 ∞ (fun n => a n ^ 2) = S)).
Admitted.
