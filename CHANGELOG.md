# Changelog

## 0.1.0 — 2026-09-30

- Initial opam package for `Lib.Tactics` and its library dependencies, providing
  `auto_limit`, `auto_cont`, `auto_diff`, and `auto_int`.
- Install the SymPy worker beside the OCaml plugins and locate it through
  findlib, so `auto_int` works outside the source checkout.
- Declare Python/SymPy runtime requirements through `conf-python3-sympy`.
- Use the `calculus.auto_int_plugin` and `calculus.simplex_plugin` findlib names.
- Complete previously admitted results in the packaged derivative,
  exponential, integral, and standard-library compatibility modules.
- Restrict the package build to `_CoqProject.opam`; exercise collections,
  plots, and the C++ simplex helper are outside the installed package.
- Document logical assumptions and the OCaml review scope in
  `packaging/ASSUMPTIONS.md`.
