# 0.1.0 validation

The release was tested on Ubuntu 24.04 with opam 2.1.5 in a newly initialized
opam root and a separate `release-test` switch using `ocaml-system.4.14.1`.
No installed libraries were copied from the development switch. Opam resolved,
downloaded, built, and installed the dependencies and both local packages.

The main dependency versions were Rocq 9.1.1, Stdlib 9.1.0, Interval 4.11.4,
Coquelicot 3.4.4, Flocq 4.2.2, and Zarith 1.14. Opam selected MathComp 2.4.0
transitively. The SymPy conf check used Python 3 with SymPy 1.14.0; the system
package `python3-sympy` was already installed, so no OS package installation
was needed during this test.

After installation, `packaging/smoke.v` and `packaging/assumptions.v` were
copied to a separate temporary directory. Both compiled with `COQPATH`,
`ROCQPATH`, `OCAMLPATH`, `AUTO_INT_SCRIPT`, and `AUTO_INT_PYTHON` unset, using
the test switch's `rocq`. No `-R` or `-I` source paths were supplied.
The smoke test checks four definite integrals and rejects an incorrect result.
The assumptions output is described in `ASSUMPTIONS.md`.

Both local opam definitions pass `opam lint`. The SymPy repository definition
also passes `opam lint --check-upstream`.

The release commit includes packaging changes, plugin naming/discovery changes,
and completed proofs in `Derivative.v`, `Exponential.v`, `Integral.v`, and
`StdlibCompat.v`, which belong to the installed dependency set. Uncommitted
exercise changes and unrelated library edits from the development checkout are
not part of this release commit.

Other operating systems and dependency combinations have not been tested.
Independent review of the OCaml plugins by a Rocq developer remains pending.

## Coquelicot compatibility (2026-10-03)

The Coquelicot bridge is packaged with Rocq 9.1.1, Stdlib 9.1.0, Coquelicot
3.4.4, and Interval 4.11.4. The package has no direct MathComp dependency or
local adapter repository requirement. Coquelicot and Interval may still
select MathComp transitively through their own package metadata.

Reproduce the source and package-manifest checks with:

```sh
rocq makefile -f _CoqProject -o Makefile
make -j2 BUILD_PLOTS=no check-compat
rocq makefile -f _CoqProject.opam -o Makefile.opam
make -f Makefile.opam -j2 BUILD_PLOTS=no all
make -f Makefile.opam BUILD_PLOTS=no check-compat
rocqchk -silent -R Lib Lib -norec Lib.CoquelicotCompat
opam lint rocq-spivak.opam
```

The compatibility target checks transport in both directions, arbitrary
integral orientation, equal endpoints, sequences, series, both Coquelicot
import orders, and calculus tactics. It also checks that a required
integrability premise cannot be skipped. It is enabled for opam builds with
`--with-test`; the regression module is not installed.

The kernel check rechecks the Coquelicot bridge against its compiled
dependencies; it does not recursively re-audit external libraries.

After removing the MathComp compatibility modules, the package-manifest
build, source and package compatibility targets, kernel check, and opam
lint all passed. A fresh staged installation under `/tmp` also passed
`packaging/compat_smoke.v` and `packaging/smoke.v` from outside the checkout,
using only staged library/plugin paths and no source load paths or
candidate-generator overrides. This checks the installed package, rather
than a fresh dependency installation.
