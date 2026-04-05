From Calculus.Chapter24 Require Import Prelude.

Definition curve_length (f df : R -> R) (a b : R) (L : R) : Prop :=
  (forall x, a <= x <= b -> ⟦ der x ⟧ f = df) /\
  integrable_on a b (fun t => sqrt (1 + df t * df t)) /\
  (∫ a b (fun t => sqrt (1 + df t * df t))) = L.

Lemma lemma_24_31 : exists fn dfn f df (L_fn : nat -> R) L_f,
  (forall n, curve_length (fn n) (dfn n) 0 1 (L_fn n)) /\
  curve_length f df 0 1 L_f /\
  uniform_limit fn f (fun x => 0 <= x <= 1) /\
  ~ (⟦ lim ⟧ L_fn = L_f).
Admitted.
