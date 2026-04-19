From Calculus.Chapter18 Require Import Prelude.

Local Notation exp := Rtrigo_def.exp.
Local Notation ln := Rpower.ln.

Definition f x := exp (x * ln (1 + 1/x)).

Definition p_f := ltac:(plot f (1/10) 20).

Plot p_f as "Calculus/Chapter18/Problem18/f.gp".