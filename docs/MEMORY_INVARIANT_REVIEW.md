# Memory Reconstruction Invariant Review

> **Document status on `yl-memory-reconstruction`: historical design review.**
> This analysis motivated the pre-invariant-only one-step theorem, explicit
> update-binding failure, and trace fold now implemented on this branch.
> `MEMORY_RECONSTRUCTION.md` is the current implementation contract.

## Scope and source snapshot

This review addresses the July 23 discussion about whether the main security
proof can maintain

```text
Ŝ_k.mem = Commit(mem_k)
```

while reconstructing a full-memory trace from an extracted committed trace.
It was checked against:

- whitepaper branch `origin/proof` at `a0f5e0b` (`fix attempt`);
- Lean branch `origin/memory-integration` at `bd48832`
  (`Replace punctured binding with update binding for memory reconstruction`);
- the current Bus-planning branch, without switching either active worktree.

The latest memory branch was built independently with the pinned Lean/Mathlib
toolchain.

## Verdict

Benedikt identified a genuine gap in the old proof. Position binding and the
old punctured-binding condition constrain what commitments can be opened to,
but they do not imply that every value accepted by `Verify` is in the image of
`Commit`. Consequently, the old one-step proposition could transfer a step
only after assuming the commitment invariant at both endpoints; it could not
establish the post-state invariant needed for induction.

Dmitry's new `UpdateBinding` property is the right kind of missing assumption.
It rules out the counterexample and proves the load-bearing write transition:
starting from an honest pre-state commitment, a shared valid write path forces
the post-state root to be the honest commitment of the point-updated memory.

The fix is important but not yet the complete trace theorem:

- `commit_update` proves the memory-root obligation for one write;
- `commitInv_write` proves the post-state invariant for a supplied
  reconstructed write state;
- `step_mem_extract` proves semantic transfer while still assuming
  `CommitInv` at both endpoints;
- no checked fold yet constructs all full states from the initial full state.

The next primary theorem should therefore construct the post-state and prove
both its invariant and its full-step semantics from the **pre-state invariant
only**. The trace fold should iterate that theorem.

## Why the old assumptions were insufficient

### The append-bit counterexample

Start with any secure commitment scheme `VC` and define:

```text
Com'       := Com × Bool
Commit'(m) := (Commit(m), false)
Verify'((C, b), i, v, π) := Verify(C, i, v, π)
```

The verifier ignores the added bit. Position binding is inherited from `VC`,
and any old property stated only through accepted openings or agreement away
from an address can also be inherited. Nevertheless,

```text
(Commit(m), true)
```

is not `Commit'(m')` for any `m'`, because every honest commitment ends in
`false`. It can still accept all the same opening proofs. Thus an extracted
committed state may pass the local step verifier without corresponding to any
full memory.

This separates two properties that the old argument conflated:

1. **non-equivocation:** a root cannot open inconsistently;
2. **realizability/image membership:** the root is the honest commitment of
   the reconstructed memory.

Position binding supplies the first at one index. It does not supply the
second.

### The partial-Merkle-tree illustration

The Merkle-tree example highlights the same missing proof obligation, but it
needs one qualification. In the CTE game the initial full memory is supplied
and the initial committed root is recomputed honestly, so an adversary cannot
start with an arbitrary right subtree while retaining that boundary root.
What had been missing was the inductive argument that every later root remains
honest.

For a standard deterministic Merkle commitment, update binding supplies that
argument: the honest old root and the shared authentication path fix the
siblings; replacing the leaf and recomputing the path fixes the unique new
root, except when the underlying hash collision-resistance game is broken.
This claim still needs a construction-specific reduction, not only intuition.

## What `UpdateBinding` establishes

The Lean branch defines the qualitative property:

```lean
def UpdateBinding (VC : VectorCommitment) : Prop :=
  ∀ m m' addr x C' π,
    m' addr = x →
    (∀ j, j ≠ addr → m' j = m j) →
    VC.verify (VC.commit m) addr (m addr) π →
    VC.verify C' addr x π →
    C' = VC.commit m'
```

It begins with an honest root `commit m`. If one path opens that root to the
actual old value and opens `C'` to the new value, then `C'` must be the honest
root of the point-updated memory.

This is exactly the property that defeats the append-bit construction: a
post-root ending in `true` could never satisfy the required conclusion.

Three surrounding details remain essential:

- **Completeness** supplies an honest opening of `commit m`.
- **Position binding** shows that the old value carried by the adversarial
  write witness equals `m addr`, allowing the same path to meet
  `UpdateBinding`'s honest-old-value premise.
- **Scheme compatibility** must be reviewed. The VanillaVM write relation
  reuses one opening path under the old and new roots. This is natural for a
  Merkle authentication path, but a different vector commitment may use an
  explicit proof-update algorithm instead. Such a scheme needs a generalized
  update relation and matching binding game, not an assumed reuse of `π`.

`UpdateBinding` should be described as a scheme-specific cryptographic
assumption until its computational reduction is proved for the selected memory
commitment. It is stronger in statement than ordinary point non-equivocation,
but no stronger than what this reconstruction argument actually needs.

## Audit of the latest Lean branch

The independent build of `origin/memory-integration` succeeded. The axiom
audit produced:

```text
mem_eq_of_commit_eq: [Quot.sound]
step_mem_extract:    [propext, Classical.choice, Quot.sound]
commit_update:       no axioms
commitInv_write:     no axioms
```

The standard axioms reported for `step_mem_extract` are not evidence of an
inconsistency, but its use of `classical` can be avoided in the primary
reconstruction theorem by requiring `DecidableEq VC.Index`. Concrete
VanillaVM addresses already have decidable equality.

### What is proved

`step_mem_extract` proves:

```text
CommitInv Ŝ₁ S₁
  + CommitInv Ŝ₂ S₂
  + stepC Ŝ₁ Ŝ₂ w
  + completeness/position binding/update binding
  -> stepF S₁ S₂ w
```

This is a valid endpoint-transfer lemma. It says that if both committed roots
already have the claimed full-memory preimages, then a valid committed step is
a valid full step.

`commitInv_write` proves:

```text
CommitInv Ŝ₁ S₁
  + writeC Ŝ₁ Ŝ₂ addr new old π
  + supplied S₂ whose memory is S₁.mem[addr ↦ new]
  -> CommitInv Ŝ₂ S₂
```

This closes the critical write-root obligation.

### What is not yet proved

Neither theorem alone is the extractor needed in the main induction:

- `step_mem_extract` assumes the post invariant;
- `commitInv_write` takes the intended post-state as an input;
- read and non-write reconstruction are not packaged with write
  reconstruction under one classified theorem;
- no segment/trace fold chooses `S_{k+1}` at every index;
- no integrated theorem proves the final reconstructed memory equals the
  claimed public final memory;
- no probabilistic valid-or-binding-break theorem or running-time bound exists.

The final sentence in `update-binding.md` calls the remaining fold
"mechanical." The induction itself should be straightforward once the trace
and descriptors are aligned, but it remains a security-critical theorem:
indexing, operation coverage, boundary equality, and bad-event accounting all
belong in its statement and proof.

## The correct Stage 3 theorem

The primary one-step theorem should have this shape:

```lean
theorem reconstructStep
    [DecidableEq VC.Index]
    (hComplete : Complete VC)
    (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC)
    (hInv : CommitInv Ŝ₁ S₁)
    (hstep : stepC memFreePred Ŝ₁ Ŝ₂ w) :
    ∃ S₂,
      CommitInv Ŝ₂ S₂ ∧
      stepF memFreePred S₁ S₂ w
```

It must not accept `CommitInv Ŝ₂ S₂` as a premise.

The construction is explicit:

- read: copy `S₁.mem`;
- write at `(addr, value)`: use `S₁.mem[addr ↦ value]`;
- other: copy `S₁.mem`;
- in every case, take `pc` and registers from `Ŝ₂`.

For writes, `commitInv_write` establishes the post invariant. For reads,
position binding establishes the read value and committed-root equality
preserves the invariant. For other operations, committed-root equality directly
preserves it.

A scratch implementation of this exact interface was compiled against
`bd48832`; `#print axioms` reported no axioms. This validates the interface but
has deliberately not been copied into the active branch, because the memory
branch and current Bus branch first need a controlled integration.

`step_mem_extract` can remain as a useful derived/general endpoint lemma, but
the main trace proof should call `reconstructStep`, not assume a future
endpoint and then try to justify it afterward.

## The trace theorem

The next result should fold `reconstructStep` over a committed trace:

```text
committed states Ŝ₀ ... Ŝ_T
per-step descriptors w₀ ... w_{T-1}
CommitInv Ŝ₀ S₀
∀ k < T, stepC Ŝ_k Ŝ_{k+1} w_k
--------------------------------------------------
∃ full states S₀ ... S_T,
  ∀ k ≤ T, CommitInv Ŝ_k S_k
  ∧ ∀ k < T, stepF S_k S_{k+1} w_k
```

The implementation should make these points explicit:

1. the descriptor vector has exactly one descriptor per transition;
2. the operation split is exhaustive;
3. the constructed post-state is reused as the next pre-state;
4. segment seams share the same committed state;
5. the initial state is exactly the public full initial state;
6. the final constructed memory commits to the public final root;
7. completeness plus position binding turns equality of the reconstructed and
   public final commitments into equality of the full final memories.

Only after this theorem exists should the committed-segment Bus result be
advertised as lifting to full-memory `Rstar`.

## Computational valid-or-break form

The qualitative `UpdateBinding` implication is not the final cryptographic
theorem. The computational version should expose two explicit bad records:

- a position-binding record containing two accepted openings of one
  root/index to distinct values;
- an update-binding record
  `(m, addr, x, C', π)` satisfying both verification equations while
  `C' ≠ Commit(m[addr ↦ x])`.

For each reconstructed transition, the reduction should return either:

- the constructed full post-state, its invariant, and its full-step proof; or
- one of those game-winning records.

Event accounting should follow the operation:

- read: position-binding failure or a valid reconstructed read;
- write: position-binding failure, update-binding failure, or a valid
  reconstructed write;
- other: a valid reconstruction with no memory-binding event.

The reconstruction and semantic-transfer arguments must share these events.
Applying one update-binding reduction to establish `CommitInv` and then
counting a second invocation when applying a generic endpoint-transfer
proposition would double count the same logical obligation. A combined
`reconstructStep` theorem makes the one-event-per-write structure explicit.

## Whitepaper assessment

The latest `origin/proof` revision fixes the core counterexample:

- Definition `def:binding` now states position binding and update binding.
- Step 6 constructs `mem_{k+1}` and uses update binding to maintain the
  invariant.
- The final bound uses `Adv_pos` and `Adv_upd`.

The following cleanup is still recommended before treating the proof as
settled:

1. Rename or restate the current "Memory extractability" proposition. It
   assumes `Ŝ_j.mem = Commit(mem_j)` for both endpoints, so it is more
   accurately a **step-transfer theorem under endpoint invariants**.
2. State a separate reconstruction lemma from the pre-state invariant only,
   or combine reconstruction and step transfer in one proposition.
3. Remove the remaining `\bwnote` by saying explicitly that the trace invariant
   is established by the reconstruction lemma; it is not a conclusion of the
   present two-endpoint proposition.
4. Define vector-commitment completeness explicitly rather than relying on an
   instruction note about honest openings.
5. Make clear that the Step 6 invariant proof and per-step semantic proof reuse
   the same position/update bad events, so the final bound counts each event
   once.
6. Supply, or clearly defer as an assumption, the reduction from Merkle
   update-binding failure to a collision in the concrete hash construction.
7. Audit the final-boundary position-binding event and state which named
   reduction covers it.

These are mostly statement and reduction-organization changes after the new
assumption; they do not revive the append-bit attack.

## Branch and integration recommendation

Do not switch the active `zkvm-whitepaper` worktree away from
`yl-w2-updated`. The latest relevant proof text is `origin/proof` at
`a0f5e0b`, while the fetched `origin/main` does not yet contain that fix. Read
it with `git show`/`git grep`, or create a separate worktree from
`origin/proof` if edits are requested.

Do not switch the dirty `lean-vanillavm` worktree either. The current Bus branch
contains uncommitted planning and code changes, and `origin/memory-integration`
diverged from an older base. The safe integration sequence is:

1. preserve/commit the current Bus work when it is ready;
2. create a dedicated integration branch or worktree;
3. merge the current `origin/main` safeguards;
4. port the `UpdateBinding`, `commit_update`, and `commitInv_write` changes;
5. add `reconstructStep`;
6. add and test the trace fold;
7. reconcile the memory classified step with the single concrete ISA step.

This avoids losing the W2 branch, the Bus draft, or silently accepting an
old-base merge.

## Short response for the group

> Benedikt's counterexample is valid: the old position/punctured-binding
> assumptions constrained openings but did not force an extracted post-root to
> be an honest `Commit` output. Dmitry's new update-binding property supplies
> exactly that missing write-transition guarantee, and the latest Lean branch
> proves the critical one-write invariant. What remains is to package it as a
> theorem that constructs the post full state from the pre-state invariant
> alone, then fold that theorem over the trace. The existing
> `step_mem_extract` is correct but assumes both endpoint invariants, so it
> cannot itself justify the induction.
