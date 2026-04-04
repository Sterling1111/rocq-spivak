Require Import List.
Lemma Injective_map_NoDup {A B : Type} (f : A -> B) (l : list A) :
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hf Hdup. induction Hdup; simpl; constructor; auto.
  intro Hin. apply in_map_iff in Hin. destruct Hin as [z [Heq Hin]].
  apply Hf in Heq. subst z. contradiction.
Qed.
