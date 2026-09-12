From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_5 : ∀ f x,
  f = (fun x => IZR (Int_part x)) ->
  ((~ (∃ k : Z, x = IZR k)) -> ⟦ der x ⟧ f = (fun _ => 0)) /\
  ((∃ k : Z, x = IZR k) -> ~ differentiable_at f x).
Proof.

Abort.
