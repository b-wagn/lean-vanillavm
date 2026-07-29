# CORRESPONDENCE — Lean ↔ paper matrix

One row per formalized paper item. This is the surface a reviewer reads **with the paper open next
to it** (Hicks: the finality-repo handover pattern). It is also the audit anchor: a reviewer's
sign-off is a per-row act ("this Lean declaration faithfully and completely formalizes this paper
statement"). Adapted from `finality/CORRESPONDENCE.md`.

**Status vocabulary:** `stated` (statement written, proof may be `sorry`) · `proved` (proof
complete, axiom-clean) · `pending(N)` (blocked on N other rows) · `n/a` (Lean-only scaffolding, no
paper counterpart) · `planned` (not yet in code; owned by an issue).

**Reviewer columns:** `Fidelity` = does the Lean statement mean the paper statement? ·
`Complete` = does it cover the *whole* paper statement, not a faithful fragment? (finality learned
"faithful but partial" is a distinct failure mode.) · `Reviewer` = collaborator who signed off +
date.

**Rule (I1, CI-checked):** every declaration formalizing a paper notion has a docstring citing the
paper label AND a row here; the named Lean declaration must actually elaborate (`#check`).

## Core

**Frozen kernel (I4)** — the stable heart. **Provisional** — the commitment layer, expected to
change (see notes below the table).

| Paper label | Lean declaration | Tier | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|---|
| Argument system Π=(Prove,Verify) | `VanillaZkVM.ArgumentSystem` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Knowledge soundness (`def:extractable`) | `VanillaZkVM.KnowledgeSound` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| — (consistency floor for KS) | `VanillaZkVM.knowledgeSound_trivialAS` | frozen | proved (n/a) | ✓ | n/a | Dmitry 2026-07-29 |
| VM state S=(pc,regs,mem) (ch01) | `VanillaZkVM.VMStateWith` / `VMState` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Committed state Ŝ (ch02) | `VanillaZkVM.CommittedVMState` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Correct-execution relation R* (ch03) | `VanillaZkVM.ZkVM.Rstar` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Correct-trace extractability (`def:cte`) | `VanillaZkVM.ZkVM.CTE` | frozen | proved | ✓ | ✗ (see †) | Dmitry 2026-07-29 |
| CTE ⇔ KS (`rem:cte-ks`) | `VanillaZkVM.ZkVM.cte_iff_knowledgeSound` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Merkle memory commitment `Com_mem` (ch02) | `VanillaZkVM.VectorCommitment` | provisional | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Position binding (`def:binding`) | `VanillaZkVM.PositionBinding` | provisional | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| ~~Punctured binding~~ **INSUFFICIENT — retire** | `VanillaZkVM.PuncturedBinding` | deprecated | to be removed | — | — | Issue 1 |
| Update binding (`def:binding`) — replaces punctured | _planned — Issue 1_ (`UpdateBinding`) | provisional | planned | — | — | — |
| Bus commitment `Com_bus` | `VanillaZkVM.HashCommitment` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Collision resistance (`Adv^cr`) | `VanillaZkVM.CollisionResistant` | provisional | proved | ✓ | ✓ | Dmitry 2026-07-29 |

> **† `CTE` completeness is deliberately left unsigned.** `ZkVM.CTE` is *faithful* to
> `def:cte` (fidelity ✓), but it is not signed off as covering the paper definition in full: the
> paper's `def:cte` is **too verbose** and should probably itself be **refactored**. Until that
> refactor happens, claiming completeness against the current paper text would be signing off on a
> statement we expect to restate. Re-open this row once `def:cte` is tightened.

> **Note (I4).** `PuncturedBinding` is known to be insufficient and is replaced by `UpdateBinding`
> in Issue 1. The whole `VectorCommitment` binding layer and `CollisionResistant` are *provisional*
> (may gain a keyed/algorithmic variant); do not depend on their exact current shape.

## Leaf / segment / bus (ch04) — ⚠ PROTOTYPE, NOT GROUND TRUTH

> `main-temp`'s `Bus.lean` is **Yavor's playground prototype**, not authoritative. These rows are
> **not** audited checkpoints; the layer is **redone properly in Issue 5** (over the frozen kernel
> and the Issue-3 ISA). Treat the current declarations as reference only.

| Paper label | Lean declaration (prototype) | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|
| `R_{0,step}` (inner-step) | `Bus.System.RInnerStep` | prototype | — | — | Issue 5 |
| `R_{0,keccak/poseidon/range}` (chips) | `Bus.System.RInner{Keccak,Poseidon,Range}` | prototype | — | — | Issue 5 |
| `R_1` (segment) | `Bus.System.RSegment` | prototype | — | — | Issue 5 |
| segment extraction (`lem:segment`) | `Bus.System.segment_extract` | prototype | — | — | Issue 5 |
| bus unification / extract-or-collision | _Issue 2 (shape) → Issue 5 (wired)_ | planned | — | — | — |

## Two-step toy (intermediate)

| Paper label | Lean declaration | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|
| segment/final toy relations | `TwoStep.System.RSeg` / `RFinal` | proved | — | — | _unreviewed_ |
| toy CTE | `VanillaZkVM.TwoStep.System.cte` | proved | — | — | _unreviewed_ |

## Planned (owned by issues — see PLAN.md)

| Paper label | Lean declaration (planned name) | Owner issue |
|---|---|---|
| memory-extractability (`prop:memory-extractability`) | `Memory.step_mem_extract` / `trace_mem_extract` | Issue 1 |
| Update binding replaces punctured binding | `UpdateBinding` | Issue 1 |
| ISA op set `{read, write, arith, hash, bin}` + `φ'_op` split (ch03, simplified) | `ISA.*` | Issue 3 |
| `R_2` convert (`lem:convert`) | `MultiStep.RConvert` | Issue 4 |
| `R_3` combine + tree unrolling (`lem:combine`) | `MultiStep.RCombine` / `combine_tree` | Issue 4 |
| `R_4` embed (`lem:embed`) | `MultiStep.REmbed` | Issue 4 |
| bus-deferred step `φ̂_step` (`eq:step-expanded`) + per-execution bus lift (`thm:main` 4–5) | `Bus.*` (redone) + `concatTrace` glue | Issue 5 |
| main theorem (`thm:main`) | `VanillaVM.cte_main` | Issue 7 |
| advantage / reduction vocabulary | `Reduction.*` | Issue 2/6 |
