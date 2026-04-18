Require Import Reals.Rpower.
From Calculus.Chapter23 Require Import Prelude.

(* Problem 9: Root Test *)

(* (a) Prove root test. *)
Lemma problem_23_9_a : forall a r,
  (forall n, a n >= 0) ->
  ⟦ lim ⟧ (fun n => Rpower (a n) (1 / INR n)) = r ->
  (r < 1 -> exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S) /\
  (r > 1 -> ~ exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S).
Abort.

(* (b) Prove that if ratio test works, root test will also. *)
Lemma problem_23_9_b : forall a r,
  (forall n, a n > 0) ->
  ⟦ lim ⟧ (fun n => a (S n) / a n) = r ->
  ⟦ lim ⟧ (fun n => Rpower (a n) (1 / INR n)) = r.
Abort.
