#!/usr/bin/env python3
"""
Standalone #print axioms auditor for all 78 theorems across LeanInLean/*.lean.
Verifies zero `sorryAx`, zero custom axioms, and zero `Lean.ofReduceBool` native axioms.
"""
import os
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
MODULES = [
    ("LeanInLean.CoreKernel", ROOT / "LeanInLean" / "CoreKernel.lean"),
    ("LeanInLean.FrontendAndMeta", ROOT / "LeanInLean" / "FrontendAndMeta.lean"),
    ("LeanInLean.CompilerAndRC", ROOT / "LeanInLean" / "CompilerAndRC.lean"),
    ("LeanInLean.RuntimeAndOlean", ROOT / "LeanInLean" / "RuntimeAndOlean.lean"),
    ("LeanInLean.FullStack", ROOT / "LeanInLean" / "FullStack.lean"),
]
ALLOWED_STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    theorems = []
    for mod, path in MODULES:
        for line_no, line in enumerate(path.read_text().splitlines(), 1):
            m = re.match(r"^theorem\s+([^\s({:]+)", line)
            if m:
                theorems.append((mod, m.group(1), line_no))

    script = ["import LeanInLean\n"] + [f"#print axioms {mod}.{name}\n" for mod, name, _ in theorems]
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tmp:
        tmp.writelines(script)
        tmp_path = tmp.name

    try:
        lake_bin = os.path.expanduser("~/.elan/bin/lake")
        if not os.path.exists(lake_bin):
            lake_bin = "lake"
        res = subprocess.run([lake_bin, "env", "lean", tmp_path], cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(tmp_path)

    if res.returncode != 0:
        print(res.stdout, file=sys.stderr)
        print(res.stderr, file=sys.stderr)
        return res.returncode

    zero_axiom_count = 0
    out_text = res.stdout.replace("\n ", " ")
    lines = [ln.strip() for ln in out_text.splitlines() if ln.strip()]
    for ln in lines:
        if "does not depend on any axioms" in ln:
            zero_axiom_count += 1
        elif "depends on axioms:" in ln:
            ax_part = ln.split("[", 1)[1].rstrip("]")
            axioms = {a.strip() for a in ax_part.split(",") if a.strip()}
            forbidden = axioms - ALLOWED_STD_AXIOMS
            if forbidden:
                print(f"ERROR: Forbidden axiom(s) {forbidden} in: {ln}", file=sys.stderr)
                return 1
        else:
            print(f"Unexpected line: {ln}", file=sys.stderr)
            return 1

    print(f"Verified {len(lines)} theorems across {len(MODULES)} modules:")
    print(f"  - Purely 0-axiom CIC theorems : {zero_axiom_count}")
    print(f"  - Standard CIC axioms only    : {len(lines) - zero_axiom_count}")
    print("  - Forbidden / sorry / native  : 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
