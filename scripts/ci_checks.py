#!/usr/bin/env python3
"""CI audit checks for lean-vanillavm (INVARIANTS.md I1, I7).

Two checks, selected by flag:

  --check-correspondence   Every audited row in docs/CORRESPONDENCE.md whose
                           "Lean declaration" column names a concrete declaration
                           must actually elaborate. We generate a throwaway Lean
                           file of `#check @<name>` lines and compile it with
                           `lake env lean`; a renamed/removed declaration fails
                           the build (I1: "the named Lean declaration must
                           actually elaborate").

  --check-axioms           Every headline theorem depends only on the permitted
                           axiom set {propext, Classical.choice, Quot.sound}, and
                           on no `sorryAx` (I7). We generate `#print axioms` lines,
                           compile, and parse the output.

Rows that are planned / not-yet-written / prototype are skipped: sections whose
heading mentions PROTOTYPE or "Planned", and any row whose declaration cell is
italic-planned text, carries a brace-shorthand `{...}`, or mentions an Issue.

Later issues extend HEADLINE_THEOREMS as they add headline results.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CORRESPONDENCE = REPO / "docs" / "CORRESPONDENCE.md"

PERMITTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# Headline theorems whose axiom footprint CI pins. Append one line per issue.
HEADLINE_THEOREMS = [
    "VanillaZkVM.ZkVM.cte_iff_knowledgeSound",   # Issue 0 — keystone
    "VanillaZkVM.knowledgeSound_trivialAS",      # Issue 0 — non-vacuity floor
    "VanillaZkVM.chain_flatten",                 # Issue 0 — concatenation lemma
    "VanillaZkVM.TwoStep.System.cte",            # two-step toy CTE
]

# A Lean identifier: dotted, letters/digits/_/'  (no braces, no spaces).
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")
CODESPAN = re.compile(r"`([^`]+)`")


def skip_section(heading: str) -> bool:
    h = heading.upper()
    return "PROTOTYPE" in h or h.strip().startswith("## PLANNED")


def declaration_names() -> list[str]:
    """Pull elaboratable declaration names from the CORRESPONDENCE tables."""
    names: list[str] = []
    section = ""
    for raw in CORRESPONDENCE.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line.startswith("#"):
            section = line
            continue
        if skip_section(section):
            continue
        if not line.startswith("|"):
            continue
        cols = [c.strip() for c in line.strip("|").split("|")]
        # header / separator rows
        if len(cols) < 2 or set(cols[0]) <= {"-", ":"} or cols[0] == "Paper label":
            continue
        cell = cols[1]
        low = cell.lower()
        if "planned" in low or "issue" in low or "{" in cell or "_" == cell:
            continue
        # A cell may list several declarations, e.g. `A.B.foo` / `bar`, where a
        # later *bare* name is a sibling sharing the first name's namespace.
        prefix = ""
        for span in CODESPAN.findall(cell):
            span = span.strip()
            if not IDENT.match(span):
                continue
            if "." in span:
                prefix = span.rsplit(".", 1)[0]
                names.append(span)
            else:
                names.append(f"{prefix}.{span}" if prefix else span)
    # de-dup, preserve order
    seen: set[str] = set()
    out: list[str] = []
    for n in names:
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def run_lean(body: str) -> subprocess.CompletedProcess:
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", dir=REPO, delete=False, encoding="utf-8"
    ) as f:
        f.write(body)
        path = Path(f.name)
    try:
        return subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=REPO,
            capture_output=True,
            text=True,
        )
    finally:
        path.unlink(missing_ok=True)


def check_correspondence() -> int:
    names = declaration_names()
    if not names:
        print("ERROR: parsed zero declarations from CORRESPONDENCE.md", file=sys.stderr)
        return 1
    body = "import VanillaZkVM\nopen VanillaZkVM\n"
    body += "".join(f"#check @{n}\n" for n in names)
    print(f"Checking {len(names)} CORRESPONDENCE declarations elaborate:")
    for n in names:
        print(f"  #check @{n}")
    res = run_lean(body)
    if res.returncode != 0:
        print("FAIL: a CORRESPONDENCE declaration did not elaborate.", file=sys.stderr)
        print(res.stdout, file=sys.stderr)
        print(res.stderr, file=sys.stderr)
        return 1
    print("OK: all CORRESPONDENCE declarations elaborate.")
    return 0


def check_axioms() -> int:
    body = "import VanillaZkVM\n"
    body += "".join(f"#print axioms {t}\n" for t in HEADLINE_THEOREMS)
    res = run_lean(body)
    if res.returncode != 0:
        print("FAIL: could not compile the axiom-check file (renamed theorem?).",
              file=sys.stderr)
        print(res.stdout, file=sys.stderr)
        print(res.stderr, file=sys.stderr)
        return 1
    out = res.stdout
    print(out.strip())
    bad = False
    if "sorryAx" in out:
        print("FAIL: a headline theorem depends on sorryAx.", file=sys.stderr)
        bad = True
    for used in re.findall(r"depends on axioms: \[([^\]]*)\]", out):
        for ax in (a.strip() for a in used.split(",") if a.strip()):
            if ax not in PERMITTED_AXIOMS:
                print(f"FAIL: disallowed axiom '{ax}'.", file=sys.stderr)
                bad = True
    if bad:
        return 1
    print(f"OK: headline theorems use only {sorted(PERMITTED_AXIOMS)}.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check-correspondence", action="store_true")
    ap.add_argument("--check-axioms", action="store_true")
    args = ap.parse_args()
    rc = 0
    if args.check_correspondence:
        rc |= check_correspondence()
    if args.check_axioms:
        rc |= check_axioms()
    if not (args.check_correspondence or args.check_axioms):
        ap.error("pass --check-correspondence and/or --check-axioms")
    return rc


if __name__ == "__main__":
    sys.exit(main())
