From Calculus.Chapter3 Require Export Prelude.

Local Definition f (a b c d x : R) := (a * x + b) / (c * x + d).

(* Literal "for which this equation makes sense": the first two alternatives
   include empty domains of f or of f composed with f. See REVIEW.md. *)
Lemma lemma_3_8 : ∀ a b c d,
  (∀ x, c * x + d <> 0 -> c * f a b c d x + d <> 0 ->
    f a b c d (f a b c d x) = x) <->
  (c = 0 /\ d = 0) \/
  (c * (a + d) = 0 /\ c * b + d^2 = 0) \/
  (c * (a + d) = 0 /\ a^2 = d^2 /\ b * (a + d) = 0).
Abort.
