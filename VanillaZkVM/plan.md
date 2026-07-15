
## 1. How the Lean code works

The project is three small files layered on top of each other (~350 lines total):

**VanillaZkVM/Model.lean** — Chapter 1's execution model, maximally abstracted:
- `Word`, `Addr`, `Byte` are all just `ℕ` (no 32-bit range enforcement yet).
- `VMStateWith Mem` is the key trick: a single structure `(pc, regs, mem)` parameterized by the *memory representation*. Registers are a total function `ℕ → Word`.
- `VMState := VMStateWith (Addr → Byte)` is the full state $S$; later, `CommittedVMState VC := VMStateWith VC.Com` is the committed state $\hat S$ — same `pc`/`regs`, memory replaced by a commitment value. This mirrors the paper's $S \mapsto \hat S$ substitution exactly.

**[VanillaZkVM/Crypto.lean](../lean-vanillavm/VanillaZkVM/Crypto.lean)** — the generic crypto vocabulary from Chapter 5, with one big design decision:
- `Relation`, `ArgumentSystem` (proof type + `prove` + `verify : Stmt → Proof → Prop`), `Extractor`.
- `KnowledgeSound AS := ∃ E, ∀ x p, verify x p → rel x (E.extract x p)` — **perfect straight-line extraction**. The whole probabilistic layer (PPT adversaries, negligible advantage, security parameter $\lambda$) is deliberately erased: "the bad event never happens" instead of "happens with negligible probability".
- `VectorCommitment` with `PositionBinding` (no commitment opens to two different values at one position) and `PuncturedBinding` (a shared opening at `addr` under $C, C'$ forces agreement everywhere else) — verbatim transcriptions of Definition 5's two binding notions, minus probabilities.
- `HashCommitment` with `CollisionResistant := hash injective`, for the bus commitment.

The file header honestly argues why this is sound methodology: every reduction in the paper's security proof is *pointwise*, and the one nontrivial base case fails by arithmetic contradiction ($N_L + N_R \ge 2N_{seg} > N_{seg}$), so negligibility machinery would do no discriminating work here. The cost: you lose the quantitative bound $\varepsilon \le \mathsf{Adv}_4 + (m{-}1)\mathsf{Adv}_3 + \dots$, and "perfectly sound argument system" is an assumption no real scheme satisfies — it stays an undischarged hypothesis, matching the paper's own idealization caveat (Remark on relativized SNARKs / ePrint 2024/728).

**VanillaZkVM/Twostep.lean** — a deliberately flattened, two-layer version of the proof architecture:
- `System` bundles: a vector commitment `VC`, parameters `Nseg`, `m`, an **assumed abstract** committed step predicate `stepC : Ŝ → Ŝ → Prop` (the paper's $\hat\varphi_{step}$, taken as a black box), and two opaque proof systems (`segProve/segVerify`, `finalProve/finalVerify`).
- `RSeg`: witness = `Nseg + 1` committed states; relation = endpoints match the statement, and `stepC` holds on each adjacent pair (`Fin.castSucc`/`Fin.succ` chaining).
- `RFinal`: witness = `m + 1` boundary states + `m` segment proofs; relation = endpoints match and **`segVerify` accepts each segment proof** — i.e., the final relation talks about *proofs verifying*, which is exactly what makes recursive composition of extractors necessary.
- `toy_cte`: the main theorem. Given `KnowledgeSound` for both layers and an accepting final proof, extract the `RFinal` witness (layer 1), then for each of the `m` segments extract an `RSeg` witness from its accepted proof (layer 2). The proof is ~10 lines because perfect extraction makes composition trivial — no union bounds, no hybrid arguments.

## 2. The real system it's modeling (sampleVM whitepaper)

The whitepaper describes a full vanilla zkVM:

1. **Execution model (ch. 1):** RV+ (RV32IM + Keccak/Poseidon precompiles), state $S = (pc, regs[0..k{-}1], mem)$, per-opcode black-box predicates $\varphi_{op}$, with memory ops decomposed into a register-only part plus an explicit memory-access equation.
2. **Segmentation (ch. 2):** trace split into $m$ segments of exactly $N_{seg}$ steps (no-op padded), chained by cross-segment boundary states.
3. **Correct execution (ch. 3):** $\varphi_{step} = \bigvee_{op} \varphi_{op}$; expensive ops (range checks, precompiles) deferred to a shared **bus** $\mathcal B$, giving $\varphi_{step,bus}$; memory replaced by a **Merkle commitment**, with committed predicates $\hat\varphi_{read}/\hat\varphi_{write}$ taking *explicit* opening proofs $\pi^{\mathsf{mem}}$ as witness fields (crucial so the extractor can retrieve them).
4. **Proof architecture (ch. 4):** four **inner circuits** (`inner-step`, `inner-keccak`, `inner-poseidon`, `inner-range`) sharing the bus via $C_{\hat{\mathcal B}} = \Com_{\mathsf{bus}}(\hat{\mathcal B})$; a `segment` circuit ($\Pi_1$) verifying all four; then a recursion tower `convert` ($\Pi_2$, 1-to-1) → `combine` ($\Pi_3$, binary-tree 2-to-1) → `embed` ($\Pi_4$, final).
5. **Security (ch. 5):** correct-trace extractability via layer-by-layer straight-line extraction, resting on knowledge-soundness of $\Pi_0..\Pi_4$, position- + punctured-binding of $\Com_{\mathsf{mem}}$ (memory extractability proposition lifts committed traces to full-memory traces), and collision-resistance of $\Com_{\mathsf{bus}}$ (unifies the four circuits' buses).

**What the Lean toy keeps:** committed states, the two features that make the argument non-trivial (extraction *composed across* SNARK layers; relations whose witnesses contain lower-layer proofs), the exact binding definitions, and segment chaining.

**What it drops** (per its own README and headers): the bus and all four inner circuits, the chips, the entire convert/combine/embed tree (collapsed to one flat $m$-way merge), memory reconstruction (binding properties are declared but never *used*), concrete instruction semantics, flattening to a single $T$-step trace, and all quantitative bounds.

## 3. Scalability / extension issues

**Structural (will force rework):**
- **`Nseg` and `m` are fixed fields of `System`.** The real `combine` circuit is 2-to-1 over subtrees of *varying* step counts; $\mathcal R_3$ must be indexed by $N$ with the side condition $N = N_L + N_R$. The current flat `Fin m` witness can't express a binary tree — you'll need an inductive proof-tree type and structural induction, replacing the two-line composition in `toy_cte`. This is the biggest architectural gap.
- **`stepC` is a pure abstraction.** Nothing relates committed steps to real steps, so `toy_cte`'s conclusion is about states whose memories are opaque commitment values — semantically vacuous until memory extractability is proved. `PositionBinding`/`PuncturedBinding` sit unused; consuming them requires adding memory-opening proofs ($\pi^{\mathsf{mem}}$) as explicit witness fields in `SegWitness`, changing the relation's shape (the paper stresses openings must be concrete witness fields, not existentials — the current design would let you accidentally use `∃ π`, which breaks the extraction argument).
- **Adding the bus changes every relation.** $R_{0,step}$ carries $C_{\hat{\mathcal B}}$ in its *statement*; the segment layer must use `CollisionResistant` to argue the four inner circuits saw the same bus. `SegStmt`/`SegWitness` and `RSeg` all get rewritten, though `Crypto.lean` survives untouched (as its header predicts).

**Modeling-fidelity:**
- **Everything is `ℕ`**: no 32-bit wraparound, so ADD semantics would be wrong; range checks (a whole inner circuit!) are unformulable — `regs 5 = 2^100` is a legal state.
- **`regs : ℕ → Word`** is total/infinite: equalities need `funext`; no notion of the $k$ registers; likewise memory `Addr → Byte` is an infinite vector, which no Merkle tree can commit to — a concrete `VectorCommitment` instance will force a finite index type.
- **Only soundness, no completeness**: `prove`/`segProve`/`finalProve` are dead fields. There is no theorem "an honest execution yields an accepting proof", so a vacuous system (`verify := False`) satisfies everything.
- **Perfect soundness**: upgrading to quantitative security means rewriting all four security predicates with randomized adversaries (`PMF`), advantages in $[0,1]$, and a negligibility predicate — the header correctly notes structures survive but every proof gets a hybrid-argument overhaul.

**Practical:** `import Mathlib` (the whole library) in Model.lean makes builds slow; `import Mathlib.Logic.Function.Basic` + `Mathlib.Order.Fin.Basic`-level imports suffice for what's used.

## 4. Roadmap to the real vanillaVM

Roughly in dependency order (first three are the README's own TODOs):

1. **Memory extractability** (highest value, uses what's already there): add `memProofs` fields to `SegWitness`, define $\hat\varphi_{read}/\hat\varphi_{write}$ from eq. (op-mem-comm-read/write) — `VC.verify Ŝ₁.mem (regs 0) v π` conjuncts — and prove the paper's Proposition: `PositionBinding` + `PuncturedBinding` ⟹ a committed trace lifts to a full-memory trace w.r.t. the real `φ_step`. This finally connects `CommittedVMState` back to `VMState` and discharges the "declared but unused" debt.
2. **Concrete step predicate**: an inductive `Op` (a couple of ALU ops, `read`, `write`, `keccak` as black box), `code : Word → Op`, per-op `φ_op` matching eq. (phiop), `φ_step := ⋁ φ_op`. Even 3–4 opcodes make `stepC` a definition instead of an axiom-like field.
3. **Bus + inner circuits**: `Bus := List BusEntry` (entries `(op, Ŝ₁, Ŝ₂)` / `(range, Ŝ)`), `Com_bus : HashCommitment` with `Domain := Bus`; four relations $R_{0,j}$ sharing $C_{\hat{\mathcal B}}$; a segment relation $R_1$ verifying four inner proofs; use `CollisionResistant` to glue the buses. This is the first place your `HashCommitment` earns its keep.
4. **Real recursion**: replace `RFinal` with `convert`/`combine`/`embed` relations indexed by step count $N$, an inductive tree of proofs, and CTE by induction on the tree — including the $N_L + N_R \ge 2N_{seg}$ base-case arithmetic the Crypto header already anticipates.
5. **Flattening lemma**: purely combinatorial gluing of $m$ chains of $N_{seg}$ steps into one `Fin (m * Nseg + 1)` trace (re-indexing via `i / Nseg`, `i % Nseg`).
6. **Bit-width realism**: `Word := UInt32` (or `Fin (2^32)`), `regs : Fin k → Word`; then `inner-range` becomes meaningful. Alternatively keep `ℕ` but add explicit `InRange` predicates, matching the paper's "arithmetic with range checks" group.
7. **Completeness**: `∀ x w, R.rel x w → AS.verify x (AS.prove x w)` as an assumption, plus a theorem that an honest trace yields an accepting final proof — rules out degenerate models.
8. **Concrete Merkle instance** (there's a starting point in lean-learn/LeanLearn/LeanLearn/merkle.lean): instantiate `VectorCommitment` over `Fin 2^n → Byte` and derive both binding notions from hash collision resistance — the paper explicitly leaves punctured binding's proof "for now", so this would go beyond the whitepaper.
9. **Quantitative security** (optional, biggest lift): `PMF`-based adversaries, real-valued advantages, negligibility — only the four security *predicates* change, as designed.

The code is a faithful, well-documented skeleton of the paper's security argument core; its main current weakness is that the theorem's conclusion lives entirely in committed-state space, so step 1 is what turns it from a composition exercise into a statement about actual VM execution.