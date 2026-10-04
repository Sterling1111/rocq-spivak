# Logical assumptions and plugin review

The installed modules are every `.v` file under `Lib`, `Calculus`, `ATTAM`, and
`Backprop`, listed in both build manifests. The package installs their sources
and compiled libraries, as well as a complete source snapshot in
`share/rocq-spivak`. Inclusion does not mean every exercise is finished: many
proof attempts end in `Abort`, which creates no theorem. This audit samples
public results; it is not an exhaustive review of the textbook collection.

## Logical assumptions

The library uses Rocq's standard real numbers and imports classical logic,
choice, and extensionality through `Lib/Imports.v`. The public results
`FTC2`, `derive_correct`, `cont_correct`, and
`riemann_darboux_integral_equiv` report these assumptions with
Rocq 9.1.1 / Stdlib 9.1.0:

- `ClassicalDedekindReals.sig_not_dec`
- `ClassicalDedekindReals.sig_forall_dec`
- `propositional_extensionality`
- `functional_extensionality_dep`
- `constructive_indefinite_description`
- `classic`
- `Extensionality_Ensembles`

Run `rocq compile assumptions.v` on a copy of `packaging/assumptions.v` outside
the checkout after installation to reproduce the public-result audit. It also
checks `riemann_darboux_integral_equiv`. This audit samples key public results;
it does not assert that every declaration has exactly the same assumptions.

`packaging/compat_smoke.v` also audits `is_RInt_coquelicot_compat` and
`is_riemann_integral_coquelicot_compat`. The Coquelicot compatibility module
adds no axioms, parameters, admitted proofs, or aborted proofs. Its checked
bridges reuse the underlying libraries' real-number and classical assumptions.

`Lib/Series.v` declares `dist_to_nearest_integer : R -> R` as a parameter for
an aborted Weierstrass example. It has no axiomatized properties and does not
occur in the assumptions of the audited results. `Lib/Polynomial.v` contains
unfinished steps ending in `Abort`, which creates no theorem. The packaged
sources contain no proofs ending in `Admitted`.

## Candidate generation and OCaml review

SymPy supplies antiderivative candidates. `src/auto_int_main.ml` serializes an
expression, runs the Python worker, and decodes its answer into an expression
term. `src/g_auto_int.mlg` introduces that term using `Tactics.pose_tac`.
`Lib/Tactics.v` proves the derivative and the fundamental-theorem side
conditions; a candidate is not accepted as a proof. The worker is installed
as `calculus/auto_int.py` and discovered through findlib when outside a checkout.

The review scope is `src/auto_int_main.ml`, `src/g_auto_int.mlg`,
`src/auto_int.py`, and their use in `Lib/Tactics.v`. Check term construction,
kernel checking, worker process handling, timeout/interrupt behavior, and
installed worker discovery. The shared `META.calculus` also builds and
installs `src/simplex_main.ml` and `src/g_simplex.mlg`. The package includes
`Lib/Psatz.v` and builds its C++ candidate generator from `src/simplex.cpp`.
Include these in the review, along with installed-helper discovery. The solver
produces candidate coefficients; `Lib/Psatz.v` checks the resulting certificate
and proves the goal with its soundness theorem.

A Rocq developer's independent review is required before claiming that this
review is complete. The package submission should explicitly request that
review and record its outcome; local compilation is not a substitute.
