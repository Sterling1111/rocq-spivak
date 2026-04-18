From Coq Require Import Arith.
From Calculus.Chapter23 Require Import Prelude.

(* Problem 2 *)

(* (a) Show that \sum_{n=1}^\infty e^n n! / n^n diverges. *)
Lemma problem_23_2_a :
  ~ (exists S, ∑ 0 ∞ (fun n => exp (INR n) * INR (fact n) / (INR n)^(n)) = S).
Abort.

(* (b) Decide when \sum_{n=1}^\infty n^n / (a^n n!) actually converges.
   (It converges for a > e and diverges for a <= e) *)
Lemma problem_23_2_b : forall a,
  a > exp 1 ->
  exists S, ∑ 0 ∞ (fun n => (INR n)^(n) / (a^(n) * INR (fact n))) = S.
Abort.
