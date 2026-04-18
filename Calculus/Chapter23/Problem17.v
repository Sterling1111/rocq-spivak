From Calculus.Chapter23 Require Import Prelude.

(* Problem 17: Continuous f >= 0, integral exists, limit at infinity does not exist. *)

Lemma problem_23_17 :
  exists f L,
    continuous f /\
    (forall x, f x >= 0) /\
    ⟦ lim ∞ ⟧ (fun N => ∫ 0 N f) = L /\
    ~ (exists M, ⟦ lim ∞ ⟧ f = M).
Abort.
