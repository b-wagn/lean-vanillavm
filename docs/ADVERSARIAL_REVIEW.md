# Adversarial Review: Lean VanillaVM Security Formalization

> **Document status on `yl-memory-reconstruction`: historical review.**
> This reviews an earlier Bus-oriented snapshot. Several findings motivated
> later changes on this branch; read it together with
> `ADVERSARIAL_REVIEW_RESPONSE.md` and the current
> `MEMORY_RECONSTRUCTION.md` proof contract.

**Reviewer stance:** This review assumes the role of an adversary who wants to
convince themselves that the Lean proof, even when fully completed according to
the current plan, would *not* adequately establish the security of the VanillaVM
system described in the whitepaper (ch03–ch05 of `sampleVM/`). Every gap,
modeling shortcut, and implicit assumption is treated as a potential attack
surface.

---

## Executive Summary

The current Lean development proves a **structurally correct but semantically
hollow** theorem. It establishes that *if* you already have knowledge-sound
SNARKs, a collision-resistant hash, a semantic refinement theorem, and five
other hypotheses, *then* a committed-state segment trace exists. This is
logically valid but says almost nothing about the actual VanillaVM until every
hypothesis is discharged against concrete ISA semantics and real cryptographic
constructions — work that is entirely absent and for which no concrete plan
exists beyond abstract "phases."

The plan documents are unusually self-aware about these limitations. However,
self-awareness in documentation does not constitute security. The risk is that
the project produces a large body of Lean code that *looks like* a security
proof to non-experts while proving only that certain propositions imply other
propositions — none of which have been connected to reality.

---

## 1. Fundamental Modeling Gaps

### 1.1 The Step Relation Is Completely Unconstrained

**Severity: CRITICAL**

In `Bus.lean`, `canonicalStep : CommittedVMState VC → CommittedVMState VC → Prop`
is an arbitrary field of `Bus.System`. The theorem `segment_extract` concludes
CTE for *whatever relation the system designer puts in this field*. An adversary
could set `canonicalStep := fun _ _ => True` and every theorem in the
development would still type-check and pass `lake build`.

The whitepaper's security theorem (Theorem 5.1) is about a *specific* step
relation: the disjunction over all ISA operation predicates
(φ_read ∨ φ_write ∨ φ_op1 ∨ … ∨ φ_op20 ∨ φ_keccak ∨ φ_poseidon). The Lean
code has **zero connection** to this concrete relation.

**What can go wrong:** A team could "complete" the formalization by choosing a
trivially satisfiable `canonicalStep`, producing a theorem that proves nothing
about VanillaVM execution correctness.

**Required fix:** A concrete ISA definition with exhaustive opcode semantics,
from which `canonicalStep` is *derived* rather than postulated.

### 1.2 `BusRefinesStep` Is the Entire Security Argument, Assumed as a Hypothesis

**Severity: CRITICAL**

The proposition:
```lean
def BusRefinesStep : Prop :=
  ∀ S₁ S₂ bus aux,
    sys.stepBus S₁ S₂ bus aux →
    sys.keccak bus → sys.poseidon bus → sys.range bus →
    sys.canonicalStep S₁ S₂
```

is taken as a *hypothesis* of every security theorem. This is not a minor
"semantic obligation" — it is the core correctness claim that the bus-delegated
execution model faithfully implements the intended ISA. In the whitepaper, this
corresponds to the entire argument of Proposition 4.1 (Memory Extractability)
plus the case analysis showing that `φ̂_step` implies `φ_step`.

The plan (Stage B4) says "prove `BusRefinesStep` rather than assuming it," but
provides no concrete path for how this would work. Proving it requires:
- A concrete ISA with all 20+ operation predicates
- A bus structure with typed entries
- A proof that every bus entry satisfying the chip predicates corresponds to a
  valid ISA operation
- Memory opening verification for read/write operations

None of this exists, and it is arguably harder than everything else in the
project combined.

### 1.3 No Full-Memory Reconstruction

**Severity: CRITICAL**

The whitepaper's CTE definition (Definition 5.4) requires the extractor to
output **full-memory states** `S₀, S₁, …, S_T` with `mem₀' = mem₀` and
`mem_T' = mem_T`. The Lean code only produces **committed-memory states**
(`CommittedVMState VC = VMStateWith VC.Com`), where memory is an opaque
commitment.

The gap between committed-state and full-memory security is precisely where
position-binding and punctured-binding of the vector commitment do their work
(Proposition 4.1 in the paper). The Lean code defines `PositionBinding` and
`PuncturedBinding` in `Crypto.lean` but **never uses them in any theorem**.

**What can go wrong:** A malicious prover could commit to memory `mem₁` at step
k, then open it to a *different* value at step k+1, and the current Lean
theorems would not detect this. The entire memory consistency argument is
missing.

### 1.4 No Recursion (Convert/Combine/Embed)

**Severity: HIGH**

The whitepaper's proof descends a 5-layer recursion tree:
```
embed → combine → convert → segment → inner circuits
```

The Lean code has:
- `Twostep.lean`: a flat two-layer toy (segment + final merger)
- `Bus.lean`: the inner-circuit/segment layer only

The combine tree unrolling (Lemma 5.3 in the paper) requires well-founded
induction on step counts, handling the disjunction
`V₂(·,π) = 1 ∨ V₃(·,π) = 1` at each node, and accumulating `(m-1)` failure
terms. None of this is formalized.

**What can go wrong:** The recursion topology itself could be unsound — e.g.,
if the combine circuit does not properly enforce `N_L + N_R = N` or if the
well-foundedness argument has a gap at the base case. The paper's Remark 5.2
shows the base case `N = N_seg` leads to a contradiction, but this depends on
the exact relation definition, which is not in Lean.

### 1.5 No Program Model

**Severity: HIGH**

The whitepaper defines CTE with respect to a *program* — the adversary selects
initial state, program code, final state, and step count. The Lean code has no
notion of:
- A program or instruction memory
- Opcode decoding (fetching the instruction at `pc`)
- Program counter advancement semantics
- Halting or termination conditions

Without these, `canonicalStep` cannot be connected to "executing the
instruction at the current program counter," which is the fundamental semantic
claim.

---

## 2. Cryptographic Modeling Concerns

### 2.1 Perfect Security Is Not Just an "Idealization" — It Changes the Theorem

**Severity: HIGH**

The code models:
- Collision resistance as **injectivity**: `∀ b b', hash b = hash b' → b = b'`
- Knowledge soundness as **perfect extraction**: `verify x p → R.rel x (E.extract x p)`
- Position binding as **absolute uniqueness**: no probability, no adversary

The paper models all of these with:
- PPT adversaries
- Security parameter λ
- Negligible failure probabilities
- Running-time bounds on extractors

These are not "the same theorem minus the bookkeeping." Perfect collision
resistance (injectivity) is **false** for any real hash function with finite
output (pigeonhole principle). The Lean theorem therefore proves something about
a mathematical fiction.

The plan acknowledges this (Phase 7: "computational security layer") but
treats it as a future addition. The adversarial concern is: **the proof
structure may not survive contact with probabilities.** For example:
- The bus-unification reduction currently returns `Sum trace collision`. With
  probabilities, it must return a *distribution* over outcomes, and the
  "collision branch" has nonzero probability that must be bounded.
- The extractor composition currently chains perfect implications. With
  probabilities, each composition step introduces a union bound, and the
  final bound (equation 5.1 in the paper) has `O(m + T)` terms.
- The `concatTrace` lemma is purely structural and survives, but the
  *semantic* step at each index now holds only with high probability,
  requiring a union bound over all `T` steps.

### 2.2 The Extractor Is Not Efficient

**Severity: MEDIUM**

The paper requires PPT extractors. The Lean `Extractor` is an arbitrary
function `R.Stmt → AS.Proof → R.Wit` with no complexity bound. The
`segmentReduction` calls five extractors sequentially, but there is no proof
(or even statement) that this runs in polynomial time.

The plan mentions "cost annotations" (Stage B3) but correctly notes these are
"manual-audit layer" only. Without a machine model, there is no way to verify
efficiency in Lean.

### 2.3 Vector Commitment Is Defined but Never Consumed

**Severity: HIGH**

`VectorCommitment` in `Crypto.lean` defines `commit`, `openProof`, and
`verify`, along with `PositionBinding` and `PuncturedBinding`. However:

- `CommittedVMState VC` uses only `VC.Com` (the commitment type)
- No theorem in the codebase invokes `VC.verify`, `PositionBinding`, or
  `PuncturedBinding`
- The `InnerStepWitness` has abstract `StepAux` but no explicit memory
  opening proofs (the paper's `π^mem_i`)

This means the entire memory security argument — the most technically
subtle part of the whitepaper's proof — has no Lean counterpart whatsoever.

### 2.4 The Bus Structure Is Opaque

**Severity: MEDIUM**

In the paper, the bus `B` is a structured collection:
```
B = {(op, S₁, S₂)}_{i=1}^b ∪ {(range, S)}_{j=1}^r
```

The chip predicates filter by operation type and check each entry. In Lean,
`H.Domain` is an arbitrary type, and `keccak`, `poseidon`, `range` are
arbitrary predicates on it. There is no:
- Bus entry type with operation tags
- Filtering mechanism
- Guarantee that the predicates check *all* entries of their type
- Connection between bus entries and the states that reference them

A malicious "bus" could satisfy all three predicates vacuously (e.g., if the
predicates are `fun _ => True`) while containing no valid entries.

---

## 3. Logical and Structural Issues in Existing Proofs

### 3.1 The CTE ↔ KnowledgeSound Equivalence Is Tautological

**Severity: LOW (but misleading)**

`cte_iff_knowledgeSound` is presented as a "keystone theorem," but it is a
trivial repackaging: both sides say "∃ extractor, ∀ accepting proof, valid
trace." The proof is `constructor; rintro; refine; intro; exact`. This is not
wrong, but calling it a "keystone" risks giving reviewers false confidence that
something deep has been established.

### 3.2 `Nseg = 0` Makes Theorems Vacuously True

**Severity: MEDIUM**

In `Bus.lean`, `Nseg : ℕ` is unconstrained. If `Nseg = 0`:
- `RInnerStep` requires `states 0 = Sin ∧ states 0 = Sout`, so `Sin = Sout`
- The step condition `∀ j, j < 0 → ...` is vacuously true
- `toCommittedZkVM` has `T = 0`, so `TraceValid` requires `tr 0 = initial ∧
  tr 0 = terminal` — again vacuously true if boundaries match

The `TwoStep.cte` theorem has `hNseg : 0 < sys.Nseg`, but `Bus.segment_extract`
does **not** require `Nseg > 0`. A vacuous theorem is not a security guarantee.

### 3.3 Trace Indexing Uses ℕ Instead of Fin

**Severity: LOW**

Traces are `ℕ → State` with `< T` side conditions. This means:
- `tr 37` is well-typed even when `T = 10`
- Boundary conditions check `tr 0` and `tr T` but say nothing about `tr (T+1)`
- The `concatTrace` function is defined for all `ℕ` inputs, with arbitrary
  behavior outside the valid range

This is not unsound (the theorems correctly use `< T` guards), but it makes the
model less precise than it could be and introduces the possibility of subtle
off-by-one errors in future extensions.

### 3.4 `traceOfReductionOutput` Has an Arbitrary Fallback

**Severity: LOW**

```lean
def traceOfReductionOutput (x : SegmentStmt sys.VC) :
    sys.SegmentReductionOutput → (ℕ → CommittedVMState sys.VC)
  | .inl tr => tr
  | .inr _ => fun _ => x.Sin
```

The collision branch returns a constant trace `fun _ => x.Sin`. This is
"correct" only because `segment_extract` proves the branch is unreachable under
collision resistance. But if collision resistance is later weakened to
computational (probabilistic), this fallback becomes a real execution path, and
the constant trace would be invalid.

### 3.5 `unifyBuses_correct` Hypotheses Include Hash Equalities That Come From Extraction

**Severity: LOW**

The theorem `unifyBuses_correct` takes as hypotheses:
```lean
(hkeccakHash : sys.H.hash bstep = sys.H.hash bkeccak)
(hposeidonHash : sys.H.hash bstep = sys.H.hash bposeidon)
(hrangeHash : sys.H.hash bstep = sys.H.hash brange)
```

These are derived in `segment_valid_or_collision` from the extracted witnesses'
commitment equalities. The derivation uses `hsCom.symm.trans hkeccakCom` etc.
This is correct, but the asymmetry (comparing everything to `bstep` rather than
to the public `busCom`) means the collision candidates are `(bstep, bkeccak)`
rather than `(bstep, busCom)`. This is fine logically but could confuse a
reviewer expecting the collision to be against the public commitment.

---

## 4. Gaps Between the Plan and Adequate Security

### 4.1 The Roadmap Has No Concrete Timeline or Dependency Graph

**Severity: MEDIUM (process risk)**

`VANILLAVM_ROADMAP.md` lists 8 phases but:
- No phase has a concrete completion criterion beyond "prove X"
- Phase 1 (canonical operation semantics) is a prerequisite for Phases 2–6,
  but no one has started it
- Phase 7 (computational security) fundamentally changes the theorem
  statements, potentially invalidating proof structures developed in Phases 1–6
- Phase 8 (LaTeX/Lean consistency) is listed last but should be ongoing

The risk is that the project produces a polished abstract framework (Phases 0–3)
that is never connected to concrete semantics (Phase 1), resulting in a
technically impressive but security-irrelevant artifact.

### 4.2 No Satisfiability Models

**Severity: MEDIUM**

`SECURITY_ARCHITECTURE.md` correctly identifies the need for "small concrete
models showing that generic assumptions such as `KnowledgeSound` are
satisfiable." None exist in the code. Without them, the assumptions could be
jointly inconsistent (making all theorems vacuously true).

A trivial satisfiability model would be:
- `Proof := Witness` (the proof IS the witness)
- `verify x w := R.rel x w`
- `extract x p := p`

This is mentioned in the plan but not implemented.

### 4.3 No Negative Tests

**Severity: MEDIUM**

`BUS_SECURITY_PLAN.md` lists 8 "required negative tests" (e.g., "remove one
knowledge-soundness assumption," "make a verifier always accept"). None are
implemented. Without them, there is no evidence that the theorem actually
*depends* on its assumptions rather than being provable from a subset.

### 4.4 The Plan Does Not Address the Paper's Footnote 1

**Severity: MEDIUM**

The whitepaper (ch03, equation for `φ_step,bus`) contains a critical footnote:
> "Formally the new predicate is even stronger as it also asserts the
> correctness of the operations in B not listed in the segment. We omit
> checking for such operations for efficiency."

This means the bus-delegated predicate is **not equivalent** to the original
step predicate — it is weaker (it misses operations in the bus not referenced
by the segment). The Lean formalization does not capture this subtlety. If the
chip predicates check *all* bus entries but the step predicate only references
*some* of them, there could be bus entries that are checked but never used, or
worse, operations that should be in the bus but are not.

---

## 5. Specific Attack Scenarios Not Ruled Out

### 5.1 The "Trivial Bus" Attack

An adversary provides a bus `b` that satisfies `keccak b ∧ poseidon b ∧
range b` vacuously (e.g., the predicates are `True` for the empty bus). The
step predicate `stepBus S₁ S₂ b aux` then only checks inline operations. If
the ISA has precompile operations that *should* be delegated to the bus but the
adversary simply omits them, the current formalization cannot detect this
because `stepBus` is unconstrained.

### 5.2 The "Commitment Swap" Attack

At step k, the committed state has `mem̂_k = C`. At step k+1, it has
`mem̂_{k+1} = C'`. The adversary uses a different memory `mem'` with
`Commit(mem') = C'` but `mem'[addr] ≠ expected_value`. Without
position-binding being *invoked* in the proof, this attack succeeds. The
current Lean code has no mechanism to prevent it.

### 5.3 The "Phantom Segment" Attack

In the recursion tree, a combine proof claims `N_L + N_R = N`. If the
formalization does not enforce that `N_seg | N_L` and `N_seg | N_R` (as the
paper does), an adversary could create a segment of size 0 or a non-integer
number of segments. The current `TwoStep` model uses `m : ℕ` segments of size
`Nseg`, but there is no divisibility constraint connecting `T` to `m * Nseg`
beyond the definitional equality `T := m * Nseg`.

### 5.4 The "Wrong Program" Attack

The CTE guarantee should say the extracted trace executes *the program claimed
by the adversary*. But since there is no program model in the Lean code, the
extracted trace could execute any sequence of operations satisfying
`canonicalStep` — including operations from a completely different program.
The step relation does not reference an instruction memory or program counter
fetch logic.

### 5.5 The "Inconsistent Boundary" Attack

At segment boundaries, the paper requires `Ŝ^{(i,N_seg)} = Ŝ^{(i+1,0)}`. In
the Lean `TwoStep` model, this is enforced by the `RFinal` witness structure
(`boundary i` is shared). But in a full recursion model with combine proofs,
the boundary state is a *witness field* that the prover provides. If the
combine relation does not check that the left child's terminal state equals the
right child's initial state *and* the witness `Ŝ_mid`, an adversary could
introduce an inconsistent boundary.

---

## 6. Engineering and Process Concerns

### 6.1 Entirely AI-Generated, No Human Audit Trail

**Severity: HIGH (process)**

The README states: "This is *purely AI made* so far. Take everything not too
seriously." For a security proof, this is alarming. The concern is not that AI
cannot write correct Lean — the type checker verifies that. The concern is that
**modeling decisions** (what to abstract, what to assume, what to omit) require
cryptographic expertise that cannot be type-checked.

Specific modeling decisions that need human expert review:
- Is `BusRefinesStep` the correct semantic obligation?
- Does the bus-unification reduction match the paper's argument?
- Is the committed-state → full-memory gap correctly characterized?
- Are the knowledge-soundness assumptions stated for the correct relations?

### 6.2 No `#print axioms` Audit

**Severity: MEDIUM**

The code imports Mathlib, which transitively imports classical axioms
(`Classical.choice`, `propext`, `Quot.sound`). While these are standard and
consistent, the security community typically wants to know exactly which axioms
a proof depends on. No `#print axioms` output is recorded for the main
theorems.

Of particular concern: `Classical.choice` makes all types inhabited, which
could mask issues where a witness type should be empty (indicating an
unsatisfiable relation).

### 6.3 No CI or Build Verification

**Severity: LOW**

There is no evidence of continuous integration or automated build testing. The
`lake-manifest.json` pins dependencies, which is good, but without CI, a
passing `lake build` is not guaranteed for reviewers.

### 6.4 Release Candidate Toolchain

**Severity: LOW**

The project uses `lean4:v4.32.0-rc1` — a release candidate, not a stable
release. RC versions can contain bugs that are fixed in the final release,
potentially invalidating compiled proofs.

---

## 7. What the Completed Plan Would Still Not Prove

Even if every phase of `VANILLAVM_ROADMAP.md` is completed perfectly:

1. **It would not prove that real SNARKs are knowledge-sound.** The
   assumptions `KnowledgeSound ASInnerStep` etc. would still be *assumed*, not
   derived from concrete cryptographic constructions. The formalization
   verifies the *reduction structure* only.

2. **It would not prove collision resistance of any real hash function.**
   Even the computational version (Phase 7) would state collision resistance as
   an assumption, not derive it from properties of Keccak/Poseidon.

3. **It would not prove that the VanillaVM ISA is correctly specified.** The
   step relation could be formally proven correct while still containing
   logical bugs (e.g., an arithmetic operation that overflows incorrectly).
   Formal verification of the step relation against a reference semantics is a
   separate (much larger) undertaking.

4. **It would not prove absence of implementation bugs in the actual
   verifier.** The Lean model proves properties of an *abstract* verifier
   (`verify : Stmt → Proof → Prop`). The real verifier is a program with
   potential bugs, side channels, and undefined behavior.

5. **It would not address recursion impossibility results.** The paper's
   Remark 5.1 acknowledges that straight-line extractors "provably do not
   exist for standard SNARKs in the plain model." The formalization assumes
   they exist. Even with ROM/AGM, the recursive composition of extractors
   has subtleties (e.g., the Di Giorgio–Micali impossibility for certain
   recursion depths) that the plan does not address.

---

## 8. Recommendations

### Immediate (before any further code)

1. **Define a minimal concrete ISA** with 3–4 operations (read, write, add,
   noop) and prove `BusRefinesStep` for it. This validates the architecture
   before scaling.

2. **Implement the trivial satisfiability model** (witness-as-proof) to
   demonstrate non-vacuity of the assumptions.

3. **Add `#print axioms` output** for `segment_extract` and `TwoStep.cte` to
   the documentation.

4. **Add `hNseg : 0 < sys.Nseg`** to `Bus.segment_extract` (matching
   `TwoStep.cte`).

### Short-term (next 2–4 weeks)

5. **Formalize memory reconstruction** for a single step: given
   `PositionBinding VC` and a valid write opening, prove that the updated
   memory is consistent with the new commitment.

6. **Implement at least 3 negative tests** from the checklist: remove a
   knowledge-soundness assumption, make a predicate `True`, and verify the
   theorem fails.

7. **Define the bus as a structured type** (list of tagged entries) rather
   than an opaque `H.Domain`, and define chip predicates as universal
   quantification over filtered entries.

### Medium-term (before claiming any security result)

8. **Formalize the convert/combine/embed recursion** with well-founded
   induction, even for the two-step toy.

9. **State the full-memory CTE theorem** as the final target, with explicit
   boundary predicate relating committed and full states.

10. **Engage a human cryptographer** to review the modeling decisions,
    particularly the `BusRefinesStep` obligation and the memory reconstruction
    invariant.

---

## 9. Verdict

**Does the current plan, if fully executed, adequately show the security of
VanillaVM?**

**No.** It would show that the *reduction structure* of the VanillaVM security
proof is internally consistent — i.e., that the composition of extractors
produces a trace *if* all component assumptions hold. This is valuable as a
specification-level artifact (it forces precise statement of what is assumed
and what is derived). But it falls short of a security proof in three
fundamental ways:

1. **Semantic adequacy is not established.** The connection between the Lean
   step relation and the actual VanillaVM ISA is entirely deferred to an
   unproven hypothesis (`BusRefinesStep`).

2. **Memory security is absent.** The hardest part of the paper's proof
   (committed → full-memory lifting via binding) has no Lean counterpart.

3. **Cryptographic assumptions are not grounded.** Perfect security
   assumptions are mathematically false for real constructions. The
   computational layer is deferred to a future phase with no concrete design.

The project is best understood as a **formal specification of the proof
structure**, not a proof of security. This is a legitimate and useful goal, but
it must be communicated as such. Claiming "we formally verified the security of
VanillaVM" based on this development would be misleading.

---

## Appendix: Assumption Inventory

| Assumption | Where used | Status | Risk |
|---|---|---|---|
| `KnowledgeSound ASSegment` | `segment_extract` | Assumed | Standard for SNARKs |
| `KnowledgeSound ASInnerStep` | `segment_extract` | Assumed | Standard |
| `KnowledgeSound ASInnerKeccak` | `segment_extract` | Assumed | Standard |
| `KnowledgeSound ASInnerPoseidon` | `segment_extract` | Assumed | Standard |
| `KnowledgeSound ASInnerRange` | `segment_extract` | Assumed | Standard |
| `CollisionResistant H` | `segment_extract` | Assumed, perfect | **False for real hashes** |
| `BusRefinesStep` | `segment_extract` | Assumed | **Core semantic gap** |
| `busEq : DecidableEq H.Domain` | `unifyBuses` | Structural | Benign |
| `Nseg : ℕ` (unconstrained) | `Bus.System` | Structural | **Can be 0** |
| `PositionBinding VC` | Defined, unused | Not consumed | **Memory gap** |
| `PuncturedBinding VC` | Defined, unused | Not consumed | **Memory gap** |
| Concrete ISA semantics | Not present | Missing | **Critical** |
| Program/instruction model | Not present | Missing | **Critical** |
| Recursion tree (R2/R3/R4) | Not present | Missing | **High** |
| Full-memory reconstruction | Not present | Missing | **Critical** |
| Computational probabilities | Not present | Missing | **High** |
