#!/usr/bin/env python3
"""CI audit checks for lean-vanillavm (INVARIANTS.md I1, I7).

Two checks, selected by flag (both may be passed together — they then share a
single `lake env lean` invocation, so Mathlib is loaded once):

  --check-correspondence   Every *audited* row in docs/CORRESPONDENCE.md must name
                           a declaration that actually elaborates. "Audited" is
                           read from the table's own `Status` column (the
                           controlled vocabulary defined in the doc header): a row
                           counts iff its status is `proved…` or `stated…`. Rows
                           that are `planned` / `pending` / `to be removed` /
                           `prototype` / `n/a`, and tables with no `Status` column
                           (the Planned section), are skipped — and the skipped
                           rows are printed, so a silently-dropped row cannot pass
                           as a false OK. We generate `#check @<name>` lines and
                           compile them (I1: "the named declaration must elaborate").

  --check-axioms           Every headline theorem depends only on the permitted
                           axiom set {propext, Classical.choice, Quot.sound}, and on
                           no `sorryAx` (I7). We generate `#print axioms` lines and
                           parse the output.

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


def _fail(msg: str, res: subprocess.CompletedProcess) -> int:
    print(msg, file=sys.stderr)
    print(res.stdout, file=sys.stderr)
    print(res.stderr, file=sys.stderr)
    return 1


def _table_rows() -> list[tuple[str, str]]:
    """Every data row of a CORRESPONDENCE table that has a `Status` column,
    as `(declaration cell, status cell)`. Column positions are read per-table
    from each table's own header, so the different tables' layouts are handled
    uniformly. Tables without a `Status` column yield nothing."""
    rows: list[tuple[str, str]] = []
    decl_idx: int | None = None
    status_idx: int | None = None
    for raw in CORRESPONDENCE.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line.startswith("|"):
            decl_idx = status_idx = None  # left the current table
            continue
        cols = [c.strip() for c in line.strip("|").split("|")]
        low = [c.lower() for c in cols]
        if any(c.startswith("lean declaration") for c in low):  # header row
            decl_idx = next(i for i, c in enumerate(low) if c.startswith("lean declaration"))
            status_idx = next((i for i, c in enumerate(low) if c == "status"), None)
            continue
        if cols and set(cols[0]) <= {"-", ":"}:  # separator row
            continue
        if decl_idx is None or decl_idx >= len(cols):
            continue
        status = cols[status_idx] if (status_idx is not None and status_idx < len(cols)) else ""
        rows.append((cols[decl_idx], status))
    return rows


def _qualify(cell: str) -> list[str]:
    """Declaration names in a cell. A later *bare* name is a sibling sharing the
    first dotted name's namespace, e.g. `A.B.foo` / `bar` -> A.B.foo, A.B.bar."""
    out: list[str] = []
    prefix = ""
    for span in CODESPAN.findall(cell):
        span = span.strip()
        if not IDENT.match(span):
            continue
        if "." in span:
            prefix = span.rsplit(".", 1)[0]
            out.append(span)
        else:
            out.append(f"{prefix}.{span}" if prefix else span)
    return out


def selected_declarations() -> tuple[list[str], list[tuple[str, str]]]:
    """`(audited names to #check, skipped (declaration, status) rows)`."""
    included: list[str] = []
    skipped: list[tuple[str, str]] = []
    seen: set[str] = set()
    for decl, status in _table_rows():
        names = _qualify(decl)
        audited = status.lower().startswith(("proved", "stated"))
        if audited and names:
            for n in names:
                if n not in seen:
                    seen.add(n)
                    included.append(n)
        elif decl.strip():
            skipped.append((decl.strip(), status.strip() or "(no status column)"))
    return included, skipped


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
            encoding="utf-8",
            errors="replace",
        )
    finally:
        path.unlink(missing_ok=True)


def eval_axioms(out: str) -> int:
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
    # CORRESPONDENCE cells contain unicode (em-dashes, arrows); keep printing them
    # from crashing on a non-UTF-8 console (e.g. Windows cp1252).
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--check-correspondence", action="store_true")
    ap.add_argument("--check-axioms", action="store_true")
    args = ap.parse_args()
    if not (args.check_correspondence or args.check_axioms):
        ap.error("pass --check-correspondence and/or --check-axioms")

    body = "import VanillaZkVM\nopen VanillaZkVM\n"
    names: list[str] = []
    if args.check_correspondence:
        names, skipped = selected_declarations()
        if not names:
            print("ERROR: parsed zero audited declarations from CORRESPONDENCE.md",
                  file=sys.stderr)
            return 1
        print(f"Checking {len(names)} audited CORRESPONDENCE declarations elaborate:")
        for n in names:
            print(f"  #check @{n}")
        if skipped:
            print(f"Skipped {len(skipped)} non-audited row(s):")
            for decl, status in skipped:
                print(f"  - {decl}  [{status}]")
        body += "".join(f"#check @{n}\n" for n in names)
    if args.check_axioms:
        body += "".join(f"#print axioms {t}\n" for t in HEADLINE_THEOREMS)

    res = run_lean(body)
    # An elaboration error (a renamed/removed audited declaration or headline
    # theorem) is a non-zero exit; both checks share this single compile.
    if res.returncode != 0:
        return _fail("FAIL: a checked declaration/theorem did not elaborate.", res)

    rc = 0
    if args.check_correspondence:
        print("OK: all audited CORRESPONDENCE declarations elaborate.")
    if args.check_axioms:
        print(res.stdout.strip())
        rc |= eval_axioms(res.stdout)
    return rc


if __name__ == "__main__":
    sys.exit(main())
