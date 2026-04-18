From Calculus.Chapter14 Require Import Prelude.

(* Problem 12: Periodic functions and their integrals *)

Definition periodic (f : R -> R) (a : R) : Prop :=
  forall x, f (x + a) = f x.

(* (a) If f is periodic with period a and integrable on [0, a],
   show that ∫ 0 a f = ∫ b (b+a) f for all b. *)
Lemma lemma_14_12_a : forall f a b,
  a > 0 ->
  periodic f a ->
  integrable_on 0 a f ->
  ∫ 0 a f = ∫ b (b + a) f.
Abort.

(* (b) Find a function f such that f is not periodic, but f' is. *)
Lemma lemma_14_12_b : exists f : R -> R, exists a : R,
  a > 0 /\
  ~ (exists T, T > 0 /\ periodic f T) /\
  periodic (⟦ Der ⟧ f) a.
Abort.

(* (c) If f' is periodic with period a and f(a) = f(0), then f is periodic with period a. *)
Lemma lemma_14_12_c : forall f f' a,
  a > 0 ->
  ⟦ der ⟧ f = f' ->
  periodic f' a ->
  f a = f 0 ->
  periodic f a.
Abort.

(* (d) Converse: if f' is periodic with period a and f is periodic (with some period),
   then f(a) = f(0). *)
Lemma lemma_14_12_d : forall f f' a,
  a > 0 ->
  ⟦ der ⟧ f = f' ->
  periodic f' a ->
  (exists T, T > 0 /\ periodic f T) ->
  f a = f 0.
Abort.
