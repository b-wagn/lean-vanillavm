
## 1. How the Lean code works

> **Note.** This overview has been updated for the current architecture (integration branch `memory-integration`, after b-wagn's `Restructure: abstract zkVM and CTE`, RovayL's `Bus.lean`, and the memory-extractability integration). The project is now five files (~1000 lines), no longer three: `Model.lean` was deleted and its contents folded into `Zkvm.lean`.

**VanillaZkVM/Crypto.lean** — the generic crypto vocabulary from Chapter 5, with one big design decision:
- `Relation`, `ArgumentSystem` (proof type + `verify : Stmt → Proof → Prop` — the prover is deliberately omitted, since it plays no role in soundness), `Extractor`.
- `KnowledgeSound AS := ∃ E, ∀ x p, verify x p → rel x (E.extract x p)` — **perfect straight-line extraction**. The whole probabilistic layer (PPT adversaries, negligible advantage, security parameter $\lambda$) is deliberately erased: "the bad event never happens" instead of "happens with negligible probability".
- `VectorCommitment` with `PositionBinding` (no commitment opens to two different values at one position) and `PuncturedBinding` (a shared opening at `addr` under $C, C'$ forces agreement everywhere else) — verbatim transcriptions of Definition 5's two binding notions, minus probabilities.
- `HashCommitment` with `CollisionResistant := hash injective`, for the bus commitment.

The file header honestly argues why this is sound methodology: every reduction in the paper's security proof is *pointwise*, and the one nontrivial base case fails by arithmetic contradiction ($N_L + N_R \ge 2N_{seg} > N_{seg}$), so negligibility machinery would do no discriminating work here. The cost: you lose the quantitative bound $\varepsilon \le \mathsf{Adv}_4 + (m{-}1)\mathsf{Adv}_3 + \dots$, and "perfectly sound argument system" is an assumption no real scheme satisfies — it stays an undischarged hypothesis, matching the paper's own idealization caveat (Remark on relativized SNARKs / ePrint 2024/728).

**VanillaZkVM/Zkvm.lean** — Chapter 1's execution model (absorbed from the old `Model.lean`) plus the abstract heart of the security argument:
- `Word`, `Addr`, `Byte` are all just `ℕ` (no 32-bit range enforcement yet). `VMStateWith Mem` is the key trick: a single structure $(pc, regs, mem)$ parameterized by the *memory representation*, with registers a total function `ℕ → Word`. `VMState := VMStateWith (Addr → Byte)` is the full state $S$; `CommittedVMState VC := VMStateWith VC.Com` is the committed state $\hat S$ — same `pc`/`regs`, memory replaced by a commitment value. This mirrors the paper's $S \mapsto \hat S$ substitution exactly.
- An **abstract `ZkVM`**: a `State` with a `step` predicate, a fixed step count `T`, boundary statements (`initial`/`terminal`), and a final `Proof`/`verify`. From it: `TraceValid`, the correct-execution relation `Rstar` (statements are boundary claims, witnesses are traces), the final argument system `ASstar`, and **`CTE`** (correct-trace extractability) in VM-native form.
- The keystone `cte_iff_knowledgeSound : CTE V ↔ KnowledgeSound V.ASstar` — both sides are "∃ extractor, ∀ accepting $(x,p)$, the output is a valid trace"; concrete systems prove `CTE` by proving knowledge-soundness and invoking this.
- `concatTrace` + **`chain_flatten`** (fully proved): glue $m$ length-$N_{seg}$ sub-chains into one length-$m\cdot N_{seg}$ trace — the flattening step, once a TODO, is now done.

**VanillaZkVM/Twostep.lean** — a deliberately flattened, two-layer system that *instantiates* the abstract `ZkVM`:
- `System` bundles: a vector commitment `VC`, parameters `Nseg`, `m`, a `regPart : RegPart` (the memory-free part of the classified step), and two opaque proof systems (`segVerify`, `finalVerify`).
- `RSeg`: witness = `Nseg + 1` committed states **and `Nseg` `MemStep` descriptors** (`SegWitness.steps`); relation = endpoints match and the classified `stepC sys.regPart (states j) (states (j+1)) (steps j)` holds for each `j < Nseg` (ℕ-indexed).
- `RFinal`: witness = `m + 1` boundary states + `m` segment proofs; relation = endpoints match and **`segVerify` accepts each segment proof** — the final relation talks about *proofs verifying*, which is exactly what makes recursive composition of extractors necessary.
- `toZkVM` instantiates the abstract `ZkVM` with `State := CommittedVMState`, `T := m * Nseg`, and `step := stepRel`, where `stepRel Ŝ₁ Ŝ₂ := ∃ w, stepC sys.regPart Ŝ₁ Ŝ₂ w` is the existential projection of the classified step (the abstract trace is descriptor-free; the concrete descriptors stay in the segment witnesses).
- `cte`: the main theorem. Given `KnowledgeSound` for both layers and `0 < Nseg`, the instantiated system is correct-trace extractable, via `cte_iff_knowledgeSound` + two-layer straight-line extraction (`RFinal` witness, then an `RSeg` witness per segment) + `chain_flatten`.

**VanillaZkVM/Memory.lean** — the memory-extractability slice (Chapter 5, Step 6):
- `FullVMState VC := VMStateWith (VC.Index → VC.Value)`, `Complete VC` (honest openings verify), `CommitInv Ŝ S` (`Ŝ.mem = VC.commit S.mem`), and `mem_eq_of_commit_eq` (completeness + position-binding ⟹ commitment injective on memories).
- The `MemStep` descriptor (`read`/`write`/`other`, carrying typed `addr`/`v`/`vOld`/`π`), the committed (`readC`/`writeC`) and full-memory (`readF`/`writeF`) op predicates, and the classified steps `stepC`/`stepF`.
- `step_mem_extract`: **position-binding + punctured-binding + completeness lift a committed step to a full-memory step**. This is the first place `PositionBinding`/`PuncturedBinding` are actually *consumed* (`#print axioms` reports only `Quot.sound` — no `sorry`).

**VanillaZkVM/Bus.lean** — the leaf layer of the proof architecture (bus delegation):
- Four inner circuits (`RInnerStep`, `RInnerKeccak`, `RInnerPoseidon`, `RInnerRange`) sharing one bus commitment, and `RSegment` verifying the four inner proofs.
- `segment_extract`: knowledge-soundness of the four inner + segment systems, together with **`CollisionResistant`** of the bus commitment, makes the segment verifier knowledge-sound for a unified bus-delegated trace. This is where `HashCommitment`/`CollisionResistant` earn their keep.

## 2. The real system it's modeling (sampleVM whitepaper)

The whitepaper describes a full vanilla zkVM:

1. **Execution model (ch. 1):** RV+ (RV32IM + Keccak/Poseidon precompiles), state $S = (pc, regs[0..k{-}1], mem)$, per-opcode black-box predicates $\varphi_{op}$, with memory ops decomposed into a register-only part plus an explicit memory-access equation.
2. **Segmentation (ch. 2):** trace split into $m$ segments of exactly $N_{seg}$ steps (no-op padded), chained by cross-segment boundary states.
3. **Correct execution (ch. 3):** $\varphi_{step} = \bigvee_{op} \varphi_{op}$; expensive ops (range checks, precompiles) deferred to a shared **bus** $\mathcal B$, giving $\varphi_{step,bus}$; memory replaced by a **Merkle commitment**, with committed predicates $\hat\varphi_{read}/\hat\varphi_{write}$ taking *explicit* opening proofs $\pi^{\mathsf{mem}}$ as witness fields (crucial so the extractor can retrieve them).
4. **Proof architecture (ch. 4):** four **inner circuits** (`inner-step`, `inner-keccak`, `inner-poseidon`, `inner-range`) sharing the bus via $C_{\hat{\mathcal B}} = \Com_{\mathsf{bus}}(\hat{\mathcal B})$; a `segment` circuit ($\Pi_1$) verifying all four; then a recursion tower `convert` ($\Pi_2$, 1-to-1) → `combine` ($\Pi_3$, binary-tree 2-to-1) → `embed` ($\Pi_4$, final).
5. **Security (ch. 5):** correct-trace extractability via layer-by-layer straight-line extraction, resting on knowledge-soundness of $\Pi_0..\Pi_4$, position- + punctured-binding of $\Com_{\mathsf{mem}}$ (memory extractability proposition lifts committed traces to full-memory traces), and collision-resistance of $\Com_{\mathsf{bus}}$ (unifies the four circuits' buses).

**What the Lean development now keeps:** committed states, the two features that make the argument non-trivial (extraction *composed across* SNARK layers; relations whose witnesses contain lower-layer proofs), the exact binding definitions, segment chaining, an **abstract `ZkVM` + `CTE`** with the keystone equivalence, the **flattening** lemma (`chain_flatten`), the **memory-extractability** single-step lemma (`step_mem_extract`, consuming both binding notions), the **bus unification** step (`Bus.lean`/`segment_extract`, consuming collision-resistance), and the classified step with **explicit `MemStep` opening witnesses** threaded into the segment witnesses.

**What it still drops / simplifies:** the recursion *tree* (`RFinal` is one flat $m$-way merge, not `convert`/`combine`/`embed`); full-memory *trace* reconstruction (the single-step `step_mem_extract` exists, but the fold that reconstructs $mem_0 … mem_T$ and strengthens `cte` is the next increment — see `mem-plan.md` Stage 3.2/3.3); concrete instruction semantics; folding the descriptors through the flattened trace (the abstract trace's step is the existential `stepRel`); and all quantitative bounds.

## 3. Scalability / extension issues

**Structural (will force rework):**
- **The recursion tree is still flat.** `Nseg` and `m` are fixed fields of `System`, and `RFinal` is a single $m$-way merge. The real `combine` circuit is 2-to-1 over subtrees of *varying* step counts; $\mathcal R_3$ must be indexed by $N$ with the side condition $N = N_L + N_R$. The current flat witness can't express a binary tree — you'll need an inductive proof-tree type and structural induction, replacing the two-layer composition in `cte`. **This is now the biggest architectural gap** (memory extractability and the bus, previously listed here, are addressed — see §4).
- **Full-memory reconstruction is half-done.** `step_mem_extract` lifts one committed step to a full-memory step, and `SegWitness` now carries the `MemStep` openings, but nothing yet folds these into a reconstructed $mem_0 … mem_T$ or strengthens `cte`'s conclusion from committed states to real memory. The remaining work (a commitment-realizability predicate + inductive fold) is specified in `mem-plan.md` Stage 3.
- **`stepRel` hides descriptors in the flattened trace.** The abstract `ZkVM.step` is descriptor-free, so `toZkVM` projects `stepC` to `∃ w, stepC … w`. The concrete openings survive only in the per-segment witnesses. If a later increment needs descriptors *in* the flattened trace (e.g. for a single global memory fold), `ZkVM.step` must be generalized to carry a descriptor slot — a change to `Zkvm.lean` worth coordinating with its authors.

**Modeling-fidelity:**
- **Everything is `ℕ`**: no 32-bit wraparound, so ADD semantics would be wrong; range checks (a whole inner circuit!) are still abstract — `regs 5 = 2^100` is a legal state. `Bus.lean`'s `range` predicate is a black box over bus entries, not an actual bound.
- **`regs : ℕ → Word`** is total/infinite: equalities need `funext`; no notion of the $k$ registers. Full memory is `VC.Index → VC.Value` (an infinite vector unless `VC.Index` is finite) — a concrete `VectorCommitment` instance will force a finite index type; `Memory.lean`'s point-wise `writeF` already avoids a `DecidableEq VC.Index` requirement in anticipation.
- **Only soundness, no completeness**: `ArgumentSystem` carries no prover, and there is no theorem "an honest execution yields an accepting proof", so a vacuous system (`verify := False`) satisfies everything.
- **Perfect soundness**: upgrading to quantitative security means rewriting all security predicates with randomized adversaries (`PMF`), advantages in $[0,1]$, and a negligibility predicate — the headers correctly note structures survive but every proof gets a hybrid-argument overhaul.

**Practical:** builds depend on the full Mathlib (compiling it dominates a clean build at ~500s); the project's own five files are ~25–60s each incrementally.

## 4. Roadmap to the real vanillaVM

Roughly in dependency order. The first items are now **done**; the remainder are open.

1. **✅ Memory extractability** (single-step): `Memory.lean` defines $\hat\varphi_{read}/\hat\varphi_{write}$ with explicit opening witnesses and proves `PositionBinding` + `PuncturedBinding` (+ `Complete`) ⟹ a committed step lifts to a full-memory step. `SegWitness` now carries the `MemStep` descriptors (Twostep.lean). **Open sub-item:** the trace-level fold that reconstructs full memory and strengthens `cte` (mem-plan.md Stage 3.2/3.3).
3. **✅ Bus + inner circuits**: `Bus.lean` models the four inner relations sharing a bus commitment and proves `segment_extract`, using `CollisionResistant` to unify the buses. **Open sub-item:** connecting the bus-delegated `RSegmentTrace` to `Twostep`'s `RSeg`/`stepC` (currently they are parallel developments; `stepBus`/`StepAux` in `Bus.lean` vs `regPart`/`MemStep` in `Memory.lean`).
5. **✅ Flattening lemma**: `chain_flatten` in `Zkvm.lean` glues $m$ chains of $N_{seg}$ steps into one $m\cdot N_{seg}$ trace, and `cte` uses it. (Still committed-state only; the full-memory flatten reuses the same lemma.)

Remaining, roughly in dependency order:

2. **Concrete step predicate**: an inductive `Op` (a couple of ALU ops, `read`, `write`, `keccak` as black box), `code : Word → Op`, per-op `φ_op` matching eq. (phiop), `φ_step := ⋁ φ_op`. Even 3–4 opcodes make `regPart`/`stepC` a definition instead of an abstract field.
4. **Real recursion**: replace `RFinal` with `convert`/`combine`/`embed` relations indexed by step count $N$, an inductive tree of proofs, and CTE by induction on the tree — including the $N_L + N_R \ge 2N_{seg}$ base-case arithmetic the Crypto header already anticipates. **Biggest remaining architectural gap.**
6. **Bit-width realism**: `Word := UInt32` (or `Fin (2^32)`), `regs : Fin k → Word`; then `inner-range` becomes meaningful. Alternatively keep `ℕ` but add explicit `InRange` predicates, matching the paper's "arithmetic with range checks" group.
7. **Completeness**: reintroduce a prover and assume `∀ x w, R.rel x w → AS.verify x (AS.prove x w)`, plus a theorem that an honest trace yields an accepting final proof — rules out degenerate models.
8. **Concrete Merkle instance**: instantiate `VectorCommitment` over `Fin 2^n → Byte` and derive both binding notions from hash collision-resistance — the paper explicitly leaves punctured binding's proof "for now", so this would go beyond the whitepaper.
9. **Quantitative security** (optional, biggest lift): `PMF`-based adversaries, real-valued advantages, negligibility — only the security *predicates* change, as designed.

The code is a faithful, well-documented skeleton of the paper's security-argument core. With memory extractability (single-step), bus unification, flattening, and the abstract CTE keystone all in place, the two highest-value open items are (i) the full-memory *trace* fold that makes `cte`'s conclusion about real execution rather than committed states, and (ii) the recursion *tree* that replaces the flat $m$-way merge.
