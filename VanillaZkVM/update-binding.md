# Update binding: why `PuncturedBinding` was not enough

## TL;DR

The memory-extractability argument needs to conclude, on a write step, that a
**committed post-state root is an actual output of `commit`** — specifically
`Ŝ_{k+1}.mem = commit(mem_{k+1})` for the reconstructed vector
`mem_{k+1} = mem_k[addr ↦ v]`. The binding notions we had (`PositionBinding`,
`PuncturedBinding`) are **non-equivocation** properties: they bound what a root
can be *opened to*. They do **not** force a root to lie in the image of `commit`.
So the step "…hence `Ŝ_{k+1}.mem = commit(mem_{k+1})`" was not supported by the
stated hypotheses. We replace `PuncturedBinding` with a property that supplies
exactly what is needed: **`UpdateBinding`**.

This mirrors a fix applied to the whitepaper (`sampleVM/ch05-security.tex`),
keeping the Lean development and the paper in step.

## The gap in one paragraph

A verifier accepts an *opening* `(C, i, v, π)` when `verify C i v π` holds. Nothing
in `PositionBinding`/`PuncturedBinding` says a value `C : Com` that admits
accepting openings is equal to `commit m` for the `m` it is "consistent" with:

- `PositionBinding` — a single `C` cannot open at one position to two different
  values (no equivocation at a point).
- `PuncturedBinding` — a shared path at `addr` under `C` and `C'` forces `C` and
  `C'` to *agree* at every other position (no equivocation off the punctured
  point).

Both constrain *disagreement*. Neither says "`C` **is** `commit m`". A malformed
root can verify the write path at `addr` and be consistent off `addr`, yet not be
`commit` of any vector. That is precisely the situation flagged in the paper:
*"the committed memory values may verify against proofs, but may not be actual
outputs of `Commit()`."*

## Where it bites in this development

The per-step lemma `Memory.step_mem_extract` is sound: it takes `CommitInv` on
**both** endpoints as a hypothesis (`Ŝⱼ.mem = commit Sⱼ.mem`) and, given that,
lifts a committed step to a full-memory step. The paper's proposition is the same
— sound *conditional on the invariant*.

The problem is **discharging** `CommitInv` when the extractor *reconstructs* the
full memory along a trace (the whitepaper's Theorem Step 6 / `rem:mem-inheritance`;
here the deferred "full-memory trace fold", Stage 3.2/3.3). On a write the fold
sets `mem_{k+1} := mem_k[addr ↦ v]` and must prove
`Ŝ_{k+1}.mem = commit(mem_{k+1})`. This is the step that needs more than
non-equivocation.

> Status note. Before this change the Lean code never reached the gap: `cte`
> proves correct-trace extractability only at the **committed-state** level, and
> the full-memory reconstruction that would need the discharge was not yet
> formalized. The flaw was therefore *absent, not fixed*. This change adds the
> missing property and the reconstruction lemmas so the discharge is sound and
> consistent with the whitepaper.

## The property

```lean
def UpdateBinding (VC : VectorCommitment) : Prop :=
  ∀ (m m' : VC.Index → VC.Value) (addr : VC.Index) (x : VC.Value)
    (C' : VC.Com) (π : VC.OpenProof),
    m' addr = x → (∀ j, j ≠ addr → m' j = m j) →
    VC.verify (VC.commit m) addr (m addr) π → VC.verify C' addr x π →
    C' = VC.commit m'
```

Read it as: a single path `π` that opens the **honest** commitment `commit m` at
`addr` and also opens `C'` at `addr` to `x` forces `C'` to be the honest
commitment of the point-update `m[addr ↦ x]` (given pointwise as `m'`, to avoid a
`DecidableEq VC.Index` requirement). In particular `C'` is then a genuine
`commit` output.

**Not a stronger assumption in spirit.** For a Merkle tree this is the *same*
collision-resistance fact that justified punctured binding: the path fixes all
sibling hashes, so recomputing the root with the new leaf gives exactly
`commit(m[addr ↦ x])` and no other `C'` can pass. `UpdateBinding` just states the
version the proof actually uses, and it *subsumes* punctured binding's role here
(off-`addr` agreement follows from `commit`-injectivity, i.e. `mem_eq_of_commit_eq`).

## What changed

- **`Crypto.lean`** — `PuncturedBinding` **replaced** by `UpdateBinding`
  (position binding, completeness, collision-resistance, and
  `mem_eq_of_commit_eq` are unchanged).
- **`Memory.lean`** —
  - `step_mem_extract` now takes `hupd : UpdateBinding VC` instead of
    `hpunc : PuncturedBinding VC`. Its write case derives the off-`addr`
    agreement by: position binding pins the value at `addr`; `UpdateBinding`
    pins the whole post-root to `commit(mem_k[addr ↦ v])`; `mem_eq_of_commit_eq`
    (injectivity) then gives the pointwise agreement. It uses `classical` to name
    the point-updated memory (there is no `DecidableEq` on the abstract
    `VC.Index`). Read/other cases are unchanged.
  - **`commit_update`** — the memory-part obligation: from an honest pre-root and
    the shared write path, `UpdateBinding` yields `Ĉ₂ = commit(mem₂)` for the
    point-updated `mem₂`.
  - **`commitInv_write`** — the full reconstruction lemma: from `CommitInv` on the
    pre-state and a committed write, `CommitInv` holds on the reconstructed
    post-state. This is what a trace fold discharges at each write.

  Both reconstruction lemmas are constructive and depend on **no axioms**.

## Relation to `cte`

`TwoStep.System.cte` proves correct-trace extractability at the committed-state
level (`CTE toZkVM`). **`TwoStep.System.cte_full` now strengthens it to full
memory**, stated as a concrete instance of the same abstract definition:
`cte_full : sys.toZkVMFull.CTE`, where `toZkVMFull` is the two-step VM over
full-memory states (`step = ∃ w, stepF …`, statement carries full boundary
states, verifier commits them). So the full-memory guarantee reuses `CTE`
verbatim rather than a bespoke conclusion, and the per-state commitment invariant
lives inside the proof, not the statement.

The fold is packaged as `TwoStep.System.traceValid_full`, stated purely in ZkVM
terms — `sys.toZkVM.TraceValid ⟨…⟩ Ŝ → sys.toZkVMFull.TraceValid x (reconstruct…)`
— and living right after `toZkVMFull`. It seeds the invariant (which holds
definitionally, since the committed initial state *is* `commit` of the full one),
runs the generic `trace_mem_extract`, and matches the terminal by injectivity of
`commit`. `cte_full` is then a thin wrapper: run `cte`'s committed extractor,
feed its `TraceValid` to `traceValid_full`. The supporting chain is:

```
commit_update → commitInv_write → commitInv_step → trace_mem_extract → traceValid_full → cte_full
```

with `step_mem_extract` lifting each committed step to a full-memory step inside
`trace_mem_extract`. This is the theorem-level connection between `Memory.lean`
(generic per-step + fold) and `Twostep.lean` (the ZkVM-phrased `traceValid_full`
and `cte_full`).
