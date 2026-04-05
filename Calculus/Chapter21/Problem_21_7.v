From Calculus.Chapter21 Require Import Prelude.

(* Problem 7: Let f be a nondecreasing function on [0,1]. *)

Definition nondecreasing_on (f : R -> R) (D : Ensemble R) : Prop :=
  forall x y, x ∈ D -> y ∈ D -> x < y -> f x <= f y.

(* (a) For any ε > 0 prove that there are only finitely many numbers a in [0,1]
   with lim_{x->a+} f(x) - lim_{x->a-} f(x) > ε. *)
Lemma lemma_21_7_a : forall f ε,
  nondecreasing_on f (fun x => 0 <= x <= 1) ->
  ε > 0 ->
  Finite_set (fun a => 0 <= a <= 1 /\ 
    exists L R_val, ⟦ lim a⁻ ⟧ f = L /\ ⟦ lim a⁺ ⟧ f = R_val /\ R_val - L > ε).
Admitted.

(* (b) Prove that the set of points at which f is discontinuous is countable. *)
Lemma lemma_21_7_b : forall f,
  nondecreasing_on f (fun x => 0 <= x <= 1) ->
  countable (fun a => 0 <= a <= 1 /\ ~ continuous_at f a).
Admitted.
