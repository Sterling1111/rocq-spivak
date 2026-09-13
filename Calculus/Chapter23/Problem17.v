From Calculus.Chapter23 Require Import Prelude.

Lemma problem_23_17 :
  ~ improper_integrable_pinf 0 (λ x, if Req_dec_T x 0 then 1 else |sin x / x|).
Abort.
