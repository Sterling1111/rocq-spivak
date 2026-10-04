"""Check that both builds include every Rocq source in the project namespaces."""

from pathlib import Path

root = Path(__file__).resolve().parent.parent
namespaces = ("Lib", "Calculus", "ATTAM", "Backprop")
expected = {
    str(path.relative_to(root))
    for namespace in namespaces
    for path in (root / namespace).rglob("*.v")
}
for name in ("_CoqProject", "_CoqProject.opam"):
    entries = [line.strip() for line in (root / name).read_text().splitlines()]
    sources = [line for line in entries if line.endswith(".v") and not line.startswith("#")]
    actual = set(sources)
    assert len(sources) == len(actual), f"{name}: duplicate source entries"
    assert actual == expected, (
        f"{name}: missing {sorted(expected - actual)}, unexpected {sorted(actual - expected)}"
    )
print(f"Both manifests include all {len(expected)} Rocq source files.")
