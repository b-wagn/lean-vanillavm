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
                           parse the output. NOTE this pins only the *listed*
                           theorems' footprints — it is not the repo-wide promise;
                           that is `--check-hygiene`.

  --check-hygiene          The repo-wide I7 promise: **no** `sorry` and **no**
                           non-permitted axiom anywhere in the project's own
                           modules. Two independent layers, because `lake build`
                           enforces neither (`sorry` is only a *warning* and an
                           `axiom` declaration compiles fine, so a stray
                           `axiom bad : False` or a `sorry` in any theorem not
                           reachable from HEADLINE_THEOREMS passes both `lake build`
                           and `--check-axioms`):
                             1. A Lean metaprogram walks every constant declared in
                                the project's modules and fails if it *is* a
                                non-permitted axiom or if `collectAxioms` reports
                                `sorryAx`/a non-permitted axiom.
                             2. A source scan of `VanillaZkVM/**.lean` (comments
                                stripped) rejecting `sorry`/`admit`/`native_decide`
                                and any `axiom` declaration — this also catches an
                                *unused* axiom regardless of reachability.

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

# Project source scanned by the hygiene source layer.
LEAN_SRC_DIR = REPO / "VanillaZkVM"
# Tokens that must never appear in project source (I7). `axiom` is included
# because the permitted axioms come from core/Mathlib — we never declare our own.
FORBIDDEN_TOKENS = [
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*axiom\b"), "axiom declaration"),
]

# Walks every constant *declared in the project's own modules* and fails on a
# non-permitted axiom or a `sorryAx`. Scoped in a section so its `open`s cannot
# perturb the `#check`/`#print axioms` lines that share this compilation.
LEAN_HYGIENE = """
section CIHygieneCheck
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut problems : Array String := #[]
  let mut scanned := 0
  for i in [0 : env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    if mod == `VanillaZkVM || (`VanillaZkVM).isPrefixOf mod then
      let data := env.header.moduleData[i]!
      for n in data.constNames do
        scanned := scanned + 1
        match env.find? n with
        | some (.axiomInfo _) =>
            if !permitted.contains n then
              problems := problems.push s!"  {mod}: declares axiom {n}"
        | _ => pure ()
        for a in ← liftCoreM (Lean.collectAxioms n) do
          if !permitted.contains a then
            problems := problems.push s!"  {mod}: {n} depends on {a}"
  IO.println s!"Hygiene: scanned {scanned} declarations across project modules."
  if problems.isEmpty then
    IO.println "OK: no sorry and no non-permitted axiom in any project module."
  else
    IO.println s!"FAIL: {problems.size} hygiene violation(s):"
    for p in problems do IO.println p
    throwError "repo-wide axiom/sorry hygiene check failed (I7)"

end CIHygieneCheck
"""


def _strip_lean_comments(src: str) -> str:
    """Drop `--` line comments and (nestable) `/- … -/` blocks, so a `sorry`
    mentioned in prose or a docstring is not mistaken for a real one."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        two = src[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1; i += 2; continue
            if two == "-/":
                depth -= 1; i += 2; continue
            i += 1; continue
        if two == "/-":
            depth += 1; i += 2; continue
        if two == "--":
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(src[i]); i += 1
    return "".join(out)


def check_hygiene_source() -> int:
    """Source layer: reject forbidden tokens in project `.lean` files."""
    problems: list[str] = []
    files = sorted(LEAN_SRC_DIR.rglob("*.lean"))
    if not files:
        print(f"ERROR: no .lean files found under {LEAN_SRC_DIR}", file=sys.stderr)
        return 1
    for path in files:
        stripped = _strip_lean_comments(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(stripped.splitlines(), start=1):
            for pattern, label in FORBIDDEN_TOKENS:
                if pattern.search(line):
                    rel = path.relative_to(REPO).as_posix()
                    problems.append(f"  {rel}:{lineno}: {label} — {line.strip()[:70]}")
    if problems:
        print(f"FAIL: {len(problems)} forbidden token(s) in project source (I7):",
              file=sys.stderr)
        for p in problems:
            print(p, file=sys.stderr)
        return 1
    print(f"OK: no forbidden tokens in {len(files)} project source file(s).")
    return 0


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
    ap.add_argument("--check-hygiene", action="store_true")
    args = ap.parse_args()
    if not (args.check_correspondence or args.check_axioms or args.check_hygiene):
        ap.error("pass --check-correspondence, --check-axioms and/or --check-hygiene")

    rc_src = check_hygiene_source() if args.check_hygiene else 0

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
    if args.check_hygiene:
        body += LEAN_HYGIENE

    res = run_lean(body)
    # A non-zero exit means either an elaboration error (a renamed/removed audited
    # declaration or headline theorem) or the hygiene metaprogram's `throwError`.
    # All checks share this single compile, so distinguish by the marker it prints.
    if res.returncode != 0:
        combined = res.stdout + res.stderr
        why = ("FAIL: repo-wide axiom/sorry hygiene violation (I7)."
               if "hygiene violation" in combined
               else "FAIL: a checked declaration/theorem did not elaborate.")
        return _fail(why, res)

    rc = rc_src
    if args.check_correspondence:
        print("OK: all audited CORRESPONDENCE declarations elaborate.")
    if args.check_axioms:
        print(res.stdout.strip())
        rc |= eval_axioms(res.stdout)
    elif args.check_hygiene:
        print(res.stdout.strip())
    return rc


if __name__ == "__main__":
    sys.exit(main())
