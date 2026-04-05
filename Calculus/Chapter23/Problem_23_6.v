From Calculus.Chapter23 Require Import Prelude.

(* Problem 6 *)

(* Let f be a continuous function on an interval around 0, and let a_n = f(1/n) *)

(* (a) Prove that if \sum_{n=1}^{\infty} a_n converges, then f(0)=0. *)
Lemma problem_23_6_a : forall f a,
  continuous_at f 0 ->
  (forall n, (n > 0)%nat -> a n = f (1 / INR n)) ->
  (exists S, ∑ 0 ∞ a = S) ->
  f 0 = 0.
Admitted.

(* (b) Prove that if f'(0) exists and \sum_{n=1}^{\infty} a_n converges, then f'(0)=0. *)
Lemma problem_23_6_b : forall f f' a,
  continuous_at f 0 ->
  ⟦ der 0 ⟧ f = f' ->
  (forall n, (n > 0)%nat -> a n = f (1 / INR n)) ->
  (exists S, ∑ 0 ∞ a = S) ->
  f' 0 = 0.
Admitted.

(* (c) Prove that if f''(0) exists and f(0)=f'(0)=0, then \sum_{n=1}^{\infty} a_n converges. *)
Lemma problem_23_6_c : forall f f' f'' a,
  continuous_at f 0 ->
  ⟦ der 0 ⟧ f = f' ->
  ⟦ der^2 0 ⟧ f = f'' ->
  f 0 = 0 ->
  f' 0 = 0 ->
  (forall n, (n > 0)%nat -> a n = f (1 / INR n)) ->
  exists S, ∑ 0 ∞ a = S.
Admitted.

(* (d) Suppose \sum_{n=1}^{\infty} a_n converges. Must f'(0) exist? (No) *)
Lemma problem_23_6_d :
  ~ (forall f a,
      continuous_at f 0 ->
      (forall n, (n > 0)%nat -> a n = f (1 / INR n)) ->
      (exists S, ∑ 0 ∞ a = S) ->
      exists f', ⟦ der 0 ⟧ f = f').
Admitted.

(* (e) Suppose f(0)=f'(0)=0. Must \sum_{n=1}^{\infty} a_n converge? (No) *)
Lemma problem_23_6_e :
  ~ (forall f f' a,
      continuous_at f 0 ->
      ⟦ der 0 ⟧ f = f' ->
      f 0 = 0 ->
      f' 0 = 0 ->
      (forall n, (n > 0)%nat -> a n = f (1 / INR n)) ->
      exists S, ∑ 0 ∞ a = S).
Admitted.
