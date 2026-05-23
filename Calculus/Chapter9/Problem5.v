From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_5 : ∀ f f' x,
  ~ (∃ k : Z, x = IZR k) ->
  f = (fun x => IZR (Int_part x)) -> ⟦ der x ⟧ f = f' -> f' x = 0.
Proof.

Abort.