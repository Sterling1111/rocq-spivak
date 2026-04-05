From Calculus.Chapter23 Require Import Prelude.

(* Problem 3 *)

(* (a) Show that \int_{1}^{\infty} e^y/y^y dy exists. *)
Lemma problem_23_3_a :
  exists L, ⟦ lim ∞ ⟧ (fun x => ∫ 1 x (fun y => exp y / y^y)) = L.
Admitted.

(* (b) Show that \sum_{n=2}^{\infty} 1/(\log n)^{\log n} converges. *)
Lemma problem_23_3_b :
  exists S, ∑ 0 ∞ (fun n => if (n <? 2)%nat then 0 else 1 / (log (INR n))^(log (INR n))) = S.
Admitted.

(* (c) Show that \sum_{n=2}^{\infty} 1/(\log n)^{\log(\log n)} diverges. *)
Lemma problem_23_3_c :
  ~ (exists S, ∑ 0 ∞ (fun n => if (n <? 2)%nat then 0 else 1 / (log (INR n))^(log (log (INR n)))) = S).
Admitted.
