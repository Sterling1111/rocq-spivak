From Calculus.Chapter18 Require Import Prelude.

Definition admissible_threshold (a : option R) : Prop :=
  match a with None => True | Some A => 1 <= A end.
Definition delayed_log (a : option R) (x : R) : R :=
  match a with
  | None => 0
  | Some A => Rmax 0 (log ((1 + x^2) / A)) / 4
  end.

Lemma lemma_18_27 : ∀ f,
  (continuous f /\ ∀ x, (f x)^2 = ∫ 0 x (λ t, f t * t / (1 + t^2))) <->
  (∃ a b, admissible_threshold a /\ admissible_threshold b /\
  ∀ x, f x = if Rle_dec 0 x then delayed_log a x else delayed_log b x).
Abort.
