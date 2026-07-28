# Vanilla zkVM whitepaper — structural digest for Lean formalization

Source: `zkvm-whitepaper/sampleVM/{ch00..ch05}.tex`, `macros.tex`. Notation
follows the paper's macros: `pc, regs, mem` (state components), `code`
(program), `φ_op` (operation predicates), `B` (bus), `Ŝ` (committed state),
`Com` (commitment), `R*`, `R_{0,*}`, `R_1..R_4` (relations), `Π_i` (SNARKs).

---

## 1. Execution model (ch01)

**Program.** `P` is a fixed RV+ binary (RV32IM + precompiles), compiled from
an Ethereum state-transition function. Inputs `I` from Ethereum state `E`
(initial) + execution witness `W`; outputs `O` = final Ethereum state `E'`.

**VM state** `S := (pc, regs, mem)`: `pc` (32-bit program counter),
`regs[0..k-1]` (`k` 32-bit registers), `mem[]` (byte-addressed, writable
memory). `code` is immutable, read-only, and explicitly **not** part of the
state.

**Step relation.** `S:=(pc1,regs1,mem1) --op:=code[pc1]--> S':=(pc2,regs2,mem2)`
— the opcode is fetched from `code` at the current `pc`. Example (ADD):
`pc2=pc1+1`, `regs2=regs1[2:=regs1[0]+regs1[1]]`, `mem2=mem1`.

**Trace.** `T : S_0 -> S_1 -> ... -> S_T`. A zkVM proof for `(P,E,E')` proves
existence of such a chain with `S_0=(pc_0:=0,regs,mem)` derived from `E` and
`S_T` derived into `E'`.

**Operation predicates.** All ops are RV32IM or precompiles (Keccak,
Poseidon), treated as black boxes via:
```
φ_op(pc1,regs1,mem1,pc2,regs2,mem2) = TRUE  <=>
   (pc1,regs1,mem1) --op--> (pc2,regs2,mem2)  ∧  code[pc1] = op
```
(the `code[pc1]=op` "fetch conjunct" binds every step to the fixed program).
Memory ops (only ones touching `mem`):
```
read:  (regs1:=(addr,*,...),mem) -> (regs2:=(addr,x,...),mem),  mem[addr]=x
write: (regs1:=(addr,x,...),mem) -> (regs2:=(addr,x,...),mem'),
       mem'[i] = x if i=addr else mem[i]
```
decomposed into a memory-free pc/reg part `φ'_op` + explicit memory equation:
```
φ_read(S1,S2)  := φ'_read(pc1,regs1,pc2,regs2) ∧ mem1[regs1[0]] = regs2[1]
φ_write(S1,S2) := φ'_write(pc1,regs1,pc2,regs2) ∧ mem2 = mem1[regs1[0] ↦ regs1[1]]
```
All *other* ops get `φ'_op ∧ mem2=mem1` — non-memory steps provably can't
mutate memory.

**Op taxonomy (ch03):** memory (`read,write`); precompiles (`keccak,
poseidon`); arithmetic w/o range checks (`op_1..op_10`); arithmetic w/ range
checks (`op_11..op_20`, each `φ_op_i := φ'_op_i(S1,S2) ∧ φ_range(S1)`, range
constants in the last two registers). Step predicate:
`φ_step(S1,S2) := ⋁_{op} φ_op(S1,S2)`. No hash/arithmetic internals (e.g.
Keccak's permutation) are ever specified — they stay opaque predicates
`φ_keccak, φ_poseidon, φ_range`, as Lean already treats them.

---

## 2. Segmentation (ch02) and committed memory / bus (ch03)

**Segments.** Trace `T` cut into `m` segments `G_1..G_m` of exactly `N_seg`
instructions each (fixed, hardcoded, verifier-known; no-op padded).
`G_i: S_start_i -> S_end_i`. Global consistency:
`S_end_i = S_start_(i+1)` for `i∈[m-1]`, `S_start_1=S_0`, `S_end_m=S_T`.

**Segment layout.** One *segment trace* (`N_seg` rows; enforces only a
*subset* of instruction semantics inline) + three *chips*: Keccak, Poseidon,
Range-check (each holds all calls/checks of that type in the segment).
Consistency trace↔chips is enforced by a **bus** + lookup arguments (the
concrete lookup mechanism is left as a TODO for teams to fill in).

**Bus `B`:** `B = {(op^(i),S1^(i),S2^(i))}_{i=1..b}, op∈{keccak,poseidon}
∪ {(range,S^(j))}_{j=1..r}`. Filter predicates:
`φ_keccak(B):=⋀_{(keccak,S1,S2)∈B} φ_keccak(S1,S2)` (sim. poseidon, range).

**Bus-deferred step predicate:**
```
φ_step(S1,S2,B) := φ_step,bus(S1,S2,B) ∧ φ_keccak(B) ∧ φ_poseidon(B) ∧ φ_range(B)
```
`φ_step,bus` routes by op-class: memory ops + non-range arithmetic verified
**inline**; range-checked arithmetic verifies the arithmetic inline but
**defers** the check via `(range,S1)∈B`; precompiles are **fully deferred**
(step only checks `(op,S1,S2)∈B ∧ mem2=mem1`). Footnote: this rewritten form
is slightly *stronger* than the original (also asserts correctness of bus
entries the segment doesn't reference) — an efficiency-motivated
over-approximation, not a completeness gap.

**Committed memory.** `mem` replaced by a Merkle vector commitment
`Com=(Commit,Open,Verify)`: `Commit(mem)`→root; `Open(mem,i)`→auth path;
`Verify(C,i,v,π)=1` iff `π` certifies position `i` under `C` holds `v`.
Committed state `Ŝ:=(pc,regs,mem̂)`, `mem̂:=Commit(mem)`. Opening proofs are
**explicit witness fields** (not existentially quantified) — essential to the
proof: binding only applies to proofs a PPT prover actually produced, so the
extractor must read them out of the witness.
```
φ̂_read(Ŝ1,Ŝ2,π) := φ'_read(Ŝ1.pc,Ŝ1.regs,Ŝ2.pc,Ŝ2.regs) ∧ Ŝ1.mem=Ŝ2.mem
                    ∧ Verify(Ŝ1.mem, Ŝ1.regs[0], Ŝ2.regs[1], π)=1
φ̂_write(Ŝ1,Ŝ2,π^mem) := φ'_write(Ŝ1.pc,Ŝ1.regs,Ŝ2.pc,Ŝ2.regs)
   ∧ Verify(Ŝ1.mem, Ŝ1.regs[0], π^mem.v_old, π^mem.π_writ)=1
   ∧ Verify(Ŝ2.mem, Ŝ1.regs[0], Ŝ1.regs[1], π^mem.π_writ)=1
```
(`π^mem=(π_writ,v_old)`: one shared path opening old value under `Ŝ1.mem` and
new value under `Ŝ2.mem`.) Full committed step relation:
`φ̂_step(Ŝ1,Ŝ2,B̂,π^mem) := φ̂_step,bus(...) ∧ φ̂_keccak(B̂) ∧ φ̂_poseidon(B̂) ∧ φ̂_range(B̂)`
(the three chip predicates are syntactically unchanged, memory-free).

**Warning (important for Lean).** Satisfying `φ̂_step` does **not** imply
`φ_step`, even computationally — opening a commitment to the *full* memory
vector may be infeasible. The gap is bounded (not eliminated) by
position/update-binding of `Com_mem` — Proposition `memory-extractability`,
§5 below.

---

## 3. Correct-execution relation R* (ch03, formalized in ch05 `rem:cte-ks`)

Plain (uncommitted, bus-free) target relation of the whole proof:
```
R* = { ((S_0,S_T); (S_1,...,S_(T-1))) | ∀ i∈[T]: φ_step(S_(i-1),S_i) = TRUE }
```
Associated *verification algorithm* (turns "correct-trace extractability"
into ordinary knowledge soundness):
1. `Ŝ_0 := (pc_0,regs_0,Commit(mem_0))`, `Ŝ_T := (pc_T,regs_T,Commit(mem_T))`.
2. Output `Π_4.Verify((Ŝ_0,Ŝ_T), π^4)`.

The verifier only ever sees committed boundary states + the final proof
`π^4`; correctness of the entire intermediate trace (memory ops, precompiles,
range checks, bus consistency, all recursion layers) is exactly what the R*
witness must certify. This matches Lean's `ZkVM.Rstar`/`TraceValid`
(statement=boundary pair, witness=full `ℕ`-indexed trace, membership=per-step
predicate), except: the paper threads the *specific* `φ_step` disjunction of
§1/§2, and additionally derives `Ŝ_0,Ŝ_T` from `S_0,S_T` via `Commit` — a step
the abstract Lean `ZkVM.Stmt/initial/terminal` (bare projections, no
commitment structure) does not model.

---

## 4. Proof architecture (ch04)

**Topology — leaf layer of 4 circuits + 4 recursion layers:**

| Circuit | Purpose | Relation |
|---|---|---|
| `inner-step` | segment trace (leaf) | `R_{0,step}` |
| `inner-keccak` | Keccak precompile (leaf) | `R_{0,keccak}` |
| `inner-poseidon` | Poseidon precompile (leaf) | `R_{0,poseidon}` |
| `inner-range` | range checks (leaf) | `R_{0,range}` |
| `segment` | verifies the 4 inner proofs | `R_1` |
| `convert` | 1-to-1 normalization | `R_2` |
| `combine` | 2-to-1 recursive merge | `R_3` |
| `embed` | final proof | `R_4` |

**Recursion tree** (Fig. `fig:topo`): binary tree of `convert` leaves merged
pairwise by `combine` nodes to a root, capped by one `embed`. Example shown:
8 segments → 8 `convert` (each atop a `segment` atop 4 `inner-*`) → 3 levels
of `combine` → 1 `embed`. Not required to be balanced — `combine`'s relation
only needs `N_L+N_R=N` with each divisible by `N_seg` and `≥N_seg`; any binary
decomposition works, and `combine` is applied exactly `m-1` times total
across the tree for `m=T/N_seg` segments (Lemma "Combine tree unrolling").

**Relations:**
- `R_{0,step}` — chains `N_seg` committed steps `Ŝ_in→Ŝ_out`, bus committed
  in the public input; `code` is hard-wired into the circuit (so the
  verification key binds the proof to the fixed program):
  ```
  R_{0,step} = { ((Ŝ_in,Ŝ_out,C_B̂); (B̂,{Ŝ_i}_{i=1..N_seg+1},{π^mem_i}_{i=1..N_seg})) |
      Ŝ_1=Ŝ_in ∧ Ŝ_{N_seg+1}=Ŝ_out
      ∧ ⋀_{i=1}^{N_seg} φ̂_step,bus(Ŝ_i,Ŝ_{i+1},B̂,π^mem_i) = TRUE
      ∧ C_B̂ = Com_bus(B̂) }
  ```
- `R_{0,keccak}`, `R_{0,poseidon}`, `R_{0,range}`:
  `{ (C_B̂; B̂) | φ̂_j(B̂)=TRUE ∧ C_B̂=Com_bus(B̂) }`, `j∈{keccak,poseidon,range}`.
- `R_1` (`segment`) — verifies the 4 inner proofs under shared `C_B̂`:
  `Π_{0,step}.Verify((Ŝ_in,Ŝ_out,C_B̂),π_step)=1 ∧ Π_{0,keccak}.Verify(C_B̂,π_keccak)=1
  ∧ Π_{0,poseidon}.Verify(C_B̂,π_poseidon)=1 ∧ Π_{0,range}.Verify(C_B̂,π_range)=1`.
- `R_2` (`convert`, 1-to-1) — carries `N_seg` as public input (rejects any
  other value): `{ ((Ŝ_0,Ŝ_N,N_seg); π_1) | Π_1.Verify((Ŝ_0,Ŝ_N),π_1)=1 }`.
- `R_3` (`combine`, 2-to-1) — two children, each either `convert` (`Π_2`) or
  `combine` (`Π_3`), chained through witness state `Ŝ_N^L`:
  ```
  R_3 = { ((Ŝ_0^L,Ŝ_N^R,N); (π^L,π^R,Ŝ_N^L,N_L,N_R)) |
      (Vfy_2((Ŝ_0^L,Ŝ_N^L,N_L),π^L)=1 ∨ Vfy_3((Ŝ_0^L,Ŝ_N^L,N_L),π^L)=1)
      ∧ (Vfy_2((Ŝ_N^L,Ŝ_N^R,N_R),π^R)=1 ∨ Vfy_3((Ŝ_N^L,Ŝ_N^R,N_R),π^R)=1)
      ∧ N_L+N_R=N ∧ N_seg|N_L ∧ N_seg|N_R ∧ N_L≥N_seg ∧ N_R≥N_seg }
  ```
  (divisibility + `≥N_seg` side conditions make each child's step count
  strictly smaller than the parent's ⇒ well-founded recursion, Remark
  `rem:wellfounded`).
- `R_4` (`embed`, final) — `T` is a *fixed system parameter* (not
  adversary-chosen), `N_seg|T`, `T≥2N_seg` (so every execution has ≥2
  segments; `R_3` forces `N≥2N_seg`, so a single-segment execution has no
  valid tree), `T≤poly(λ)`:
  `R_4 = { ((Ŝ_0,Ŝ_T); π_3) | Π_3.Verify((Ŝ_0,Ŝ_T,T),π_3)=1 }`.

**Composition.** `zkVM = ({φ_op}, Com_bus, Com_mem, Π_0,Π_1,Π_2,Π_3,Π_4)`
(Definition "zkVM system", ch05). Each `Π_i.Verify` calls the next relation's
`Verify` inside its own relation's definition (`R_1↦Π_{0,j}`, `R_2↦Π_1`,
`R_3↦Π_2/Π_3`, `R_4↦Π_3`) — this is proof-carrying data (PCD), not a flat
SNARK.

---

## 5. Security (ch05)

### 5.1 Main theorem — exact statement

**`def:cte` (Correct-trace extractability).** Experiment
`Exp^cte_{zkVM,E_zkVM,A}(λ)`: `A` picks `S_0,S_T,π^4` (`code`,`T` fixed, not
adversary-chosen); verifier commits `Ŝ_0,Ŝ_T`, checks `Π_4.Verify`; if it
verifies, run `E_zkVM(S_0,S_T,π^4)` to get full-memory states `S_0..S_T`;
`A` **wins** iff the extracted trace disagrees with the claimed boundary
(`pc/regs/mem` at `0` or `T`) or `φ_step(S_i,S_{i+1})≠TRUE` for some `i`.
`zkVM` is CTE iff `Adv^cte_zkVM(A)≤negl(λ)` ∀ PPT `A`, for a fixed PPT `E_zkVM`.

**`rem:cte-ks`.** CTE is *exactly* knowledge soundness (`def:extractable`) of
the R*-verification algorithm of §3 — the paper's analogue of Lean's
`cte_iff_knowledgeSound`, except the R*-verifier here additionally performs
the `Commit(mem_0),Commit(mem_T)` step, which Lean's `ZkVM.Stmt/initial/
terminal` abstracts away entirely.

**`thm:main` (Correct-trace extractability) — exact bound.** Let
`m:=T/N_seg`. For every PPT `A` with `ε:=Adv^cte_zkVM(A)`, ∃ PPT reductions
`D_4,D_3,D_2,D_1,{D_{0,j}}_j,D_bus,{D^pos_k}_{k=1}^T,{D^upd_k}_{k=1}^T`:
```
ε ≤ Adv^ks_{Π_4}(D_4)
  + (m-1)·Adv^ks_{Π_3}(D_3)
  + m·Adv^ks_{Π_2}(D_2)
  + m·( Adv^ks_{Π_1}(D_1) + Σ_{j∈{step,keccak,poseidon,range}} Adv^ks_{Π_{0,j}}(D_{0,j})
        + Adv^cr_{Com_bus}(D_bus) )
  + Σ_{k=1}^{T} ( Adv^pos_{Com_mem}(D^pos_k) + Adv^upd_{Com_mem}(D^upd_k) )
```
All reductions run in `Time(A)+poly(λ)`; overall
`Time(E_zkVM) ≤ c·Time(A)+poly(λ)`, `c=3m+T` (`A` invoked once per
Embed/Convert/Combine call = `2m` total, plus `m` Segment calls, plus `T`
per-step memory-reconstruction calls). Negligible RHS ⇒ CTE.

### 5.2 Reduction structure — one lemma per layer, outermost→innermost, plus
a per-step memory argument

1. **Embed** (`lem:embed`): assumes `Π_4` KS; `D_4` just forwards `A`'s
   `(x,π^4)` to the `Π_4` challenger ⇒ `Adv^embed_{E_4}(A) ≤ Adv^ks_{Π_4}(D_4)`.
   Base case, coefficient 1.

2. **Combine** (`lem:combine`, "tree unrolling"): assumes `Π_3` KS. `E_3`
   recursively unrolls the tree (well-founded, `rem:wellfounded`: child step
   counts strictly `<N`). Bad event `B_t` at internal node `t`: node's proof
   verifies but `E_{Π_3}` fails to return an `R_3` witness. Exactly `m-1`
   internal nodes ⇒ `Adv^comb_{N,E_3}(A) ≤ (m-1)·Adv^ks_{Π_3}(D_3)`. Base case
   `N=N_seg` (`m=1`) is vacuous by *arithmetic contradiction*
   (`N_L+N_R=N_seg` with both `≥N_seg` is impossible).

3. **Convert** (`lem:convert`): assumes `Π_2` KS; single reduction,
   `Adv^conv_{E_2}(A) ≤ Adv^ks_{Π_2}(D_2)`, applied once per segment (`m`
   times total).

4. **Segment** (`lem:segment`): assumes `Π_1` KS + all four `Π_{0,j}` KS +
   `Com_bus` collision-resistant. *Six* bad events: `B_1` (`Π_1` extraction
   fails), `B_{0,step}`, `B_{0,j}` (`j∈{keccak,poseidon,range}`, inner
   extraction fails), `B_bus` (the four extracted buses `B̂_step, B̂_keccak,
   B̂_poseidon, B̂_range` aren't all equal despite committing to the same
   `C_B̂` — a `Com_bus` collision). Off all six, unify buses as `B̂:=B̂_step`
   and combine the four predicates via Eq. `eq:step-bus2` to get full
   `φ̂_step`. Bound: `Adv^seg_{E_1}(A) ≤ Adv^ks_{Π_1} + Adv^ks_{Π_{0,step}}
   + Adv^ks_{Π_{0,keccak}} + Adv^ks_{Π_{0,poseidon}} + Adv^ks_{Π_{0,range}}
   + Adv^cr_{Com_bus}`. **This is exactly Lean's `Bus.System.segment_extract`**
   — same six assumptions bundled as `Bus.System.Assumptions`, same
   bus-unification argument (`hbus`).

5. **Inner-circuit** (`lem:inner`): each `Π_{0,j}` KS directly gives its
   extractor; `Adv^inner_{j,E_{0,j}}(A) = Adv^ks_{Π_{0,j}}(A)` — no reduction
   loss (this game *is* the KS game).

6. **Memory extractability** (`prop:memory-extractability`) — not a
   recursion layer but a crypto-to-crypto bridge from committed-memory to
   plain full-memory correctness, applied once **per step** `k=0..T-1`:
   - Assumptions on `Com_mem` (`def:binding`): **position-binding**
     (`Adv^pos_{Com}(A):=Pr[Verify(C,i,v,π)=1 ∧ Verify(C,i,v',π')=1 ∧ v≠v']`
     negl.) and **update-binding**
     (`Adv^upd_{Com}(A):=Pr[Verify(C,addr,m[addr],π)=1 ∧ Verify(C',addr,x,π)=1
     ∧ C'≠Commit(m[addr↦x])]` negl.). Remark: Merkle trees get both from
     hash collision-resistance.
   - Statement: given `A` outputting `(Ŝ1,Ŝ2,mem1,mem2,B̂,π^mem)` with the
     commitment invariant, `φ̂_step` holding, but `φ_step(S1,S2)` (for
     `S_j:=(Ŝ_j.pc,Ŝ_j.regs,mem_j)`) failing with prob. `ε`, then
     `ε ≤ Adv^pos_{Com_mem}(D^pos) + Adv^upd_{Com_mem}(D^upd)`.
   - Proof: two bad events `E_pos,E_upd` (position/update collisions), one
     reduction each; then a case-split over every op kind (arithmetic w/wo
     range, read, write, precompile) showing off both bad events
     `φ̂_step ⇒ φ_step(...,B) ⇒ φ_step(...)` — the second implication ("Step
     B: bus elimination") needs no crypto, purely predicate unfolding.
   - Used in `thm:main` Step 6 to inductively rebuild `mem_0..mem_T` from the
     committed-state chain + per-step memory-opening witnesses `{π^mem_k}`
     extracted at the Segment layer, contributing the
     `Σ_{k=1}^T(Adv^pos_k+Adv^upd_k)` tail. **Entirely absent from Lean** (§6).

### 5.3 Composition and running time

`E_zkVM` composes the five layer-extractors `E_4,E_3,E_2,E_1,{E_{0,j}}`
sequentially (Steps 1-4), then the per-step memory-reconstruction argument
(Steps 5-6). Every reduction is a single run of `A` + `poly(λ)`
(`Time(D)=Time(A)+poly(λ)`); the aggregate `c=3m+T` blow-up in
`Time(E_zkVM)` comes purely from *invocation count* (once per
Embed/Convert/Combine, `m` for Segment, `T` for memory reconstruction), not
from expensive individual reductions.

### 5.4 Idealization caveats (flagged by the paper itself, `rem:idealized`)

(i) `def:extractable` postulates a **straight-line** extractor in
`Time(A)+poly(λ)` — impossible for *succinct* proofs in the plain model,
only exists in the ROM. (ii) Composing straight-line extraction *across
recursion layers* (PCD) needs each SNARK knowledge-sound *relative to the
same random oracle* ("relativized"), and relativized SNARKs provably don't
exist in general (`EPRINT:relativized`) — the paper explicitly idealizes over
this. So `thm:main`'s bounds validate the **reduction structure/topology**,
not a concrete security level.

---

## 6. Gap list for Lean formalization

Baseline (`VanillaZkVM/{Zkvm,Bus,Twostep,Crypto}.lean`): `Zkvm.lean` has the
abstract `ZkVM` structure, `R*=ZkVM.Rstar`, `CTE=ZkVM.CTE`, keystone
`cte_iff_knowledgeSound`, plus `concatTrace`/`chain_flatten`. `Crypto.lean`
has `Relation`, `ArgumentSystem` (verifier-only), `Extractor`,
`KnowledgeSound` (**perfect**: `∃E,∀ x p, verify → rel`, no `λ`/`negl`/
running time), `VectorCommitment` with `PositionBinding`/`PuncturedBinding`
(perfect), `HashCommitment` with `CollisionResistant` (perfect: injective
`hash`). `Twostep.lean`: 2-layer toy (`RSeg→RFinal`), `TwoStep.System.cte`
from `Assumptions:={ksSeg,ksFinal}` — no bus, no inner circuits,
`Com_mem`/`VC` declared but its binding never invoked. `Bus.lean`: leaf/
segment layer only (`RInnerStep/Keccak/Poseidon/Range`, `RSegment`,
`RSegmentTrace`), `Bus.System.segment_extract` proves `KnowledgeSound
ASSegmentTrace` from `Assumptions:={busCR,ksInnerStep,ksInnerKeccak,
ksInnerPoseidon,ksInnerRange,ksSegment}` — a faithful perfect-probability
analogue of `lem:segment`; states are `CommittedVMState`, but memory-opening
witnesses (`StepAux`) are an opaque type parameter.

**(a) Committed memory / memory-commitment properties — largest gap.** Lean
has `PositionBinding` + `PuncturedBinding` (shared opening at `addr` under
`C,C'` ⇒ agreement at every *other* index). The paper's **update-binding**
is different and more direct: an opening at `addr` valid under honest
`C=Commit(m)` and some `C'` forces `C'=Commit(m[addr↦x])` outright (full
re-commitment equality). Related (Merkle trees get both from hash CR per the
paper's Remark) but not interchangeable; no Lean lemma derives one from the
other or reconstructs a full memory vector. Missing: (i) `prop:memory-
extractability` itself — no bridge from `CommittedVMState` back to `VMState`
(full `Addr→Byte` memory); `VMState`/`memUpdate` exist in `Zkvm.lean` but are
never connected to `CommittedVMState` by any theorem; (ii) no per-op
predicates `φ_read/write`, `φ'_read/write`, the commitment-opening equations
(`eq:op-mem-comm-read/write`), or the memory-reconstruction invariant
(`rem:mem-inheritance`) — `Bus.lean`'s `stepBus`/`StepAux` are fully
abstract, so read/write aren't distinguished from any other opcode; (iii) no
per-step probability accounting (see (e)).

**(b) Multi-layer recursion — capped at 2 layers.** `Twostep.lean` has only
`RSeg→RFinal`; the paper has leaf(`inner-*`)→`segment`(`R_1`)→
`convert`(`R_2`, **missing**)→`combine`(`R_3`, **missing**, binary
self-recursive)→`embed`(`R_4`, **missing**). Lean's `RFinal` flattens the
`m`-way merge directly (`∀ i<m`), sidestepping the recursion-tree reasoning
that `lem:combine`'s strong induction and `(m-1)` coefficient are about.
Specifically missing: `R_2`/`convert` (trivial 1-to-1 wrapper +
`lem:convert`-style lemma); `R_3`/`combine` (binary 2-to-1 relation with
`N_L+N_R=N`, divisibility, well-foundedness side conditions, plus a
tree-unrolling extraction lemma generalizing `chain_flatten` to trees);
`R_4`/`embed` (fixed `T≥2N_seg`, `N_seg|T`, plus the "no valid tree for a
single segment" argument); the binary-tree topology itself (Fig.
`fig:topo`) is nowhere represented as data — `Twostep`'s indexing is a flat
list, not a tree.

**(c) Additional ISA ops (arithmetic, hash calls) — currently fully opaque.**
`Bus.lean`'s `stepBus`, `keccak`, `poseidon`, `range` are abstract
`Prop`-valued fields, matching the paper's "treat as black box" stance for op
*semantics*, but the paper still names/structures `read`, `write`,
`op_1..op_10` (arithmetic, no range check), `op_11..op_20` (arithmetic +
range check, `φ_op_i=φ'_op_i∧φ_range(S1)`), and the disjunctive
`φ_step:=⋁_op φ_op`. None of this taxonomy, nor the bus-membership
disjunction `φ_step,bus` (Eq. `eq:step-expanded`) routing each op-class to
inline-vs-deferred, is represented — `Bus.System.step` just conjuncts
`stepBus ∧ keccak ∧ poseidon ∧ range` without modeling why a given step
contributes to which chip/bus entry. Would need a concrete (even parametric)
opcode enumeration, per-class `φ_op`/`φ'_op` splits, and the disjunctive step
predicate rebuilt from those pieces.

**(d) Bus per segment.** `Bus.lean` already models *one* segment's bus
faithfully to `lem:segment` (good shape). Missing: *lifting* it across a
whole execution — `thm:main` Step 4 applies the segment lemma **m times**
(once per segment) and Step 5 concatenates the resulting per-segment
bus-satisfying chains into one length-`T` chain, carrying a *distinct* bus
`B̂_i` per segment (segments' buses are never claimed equal to each other,
only internally self-consistent). No Lean code combines `Bus.System` with
`concatTrace`/`chain_flatten`, nor extends `Twostep`-style concatenation to
carry per-segment `StepAux`/bus data into a full-VM memory reconstruction.

**(e) Explicit reductions to hardness assumptions — systematically absent.**
`Crypto.lean` is deliberately **perfect/probability-free** (`KnowledgeSound`
is `∃E,∀ x p, verify→rel`, no adversary/`λ`/`negl`/`Adv(·)`/running time).
Consequences: no notion of advantage (`Adv^ks_Π`, `Adv^pos_Com`,
`Adv^upd_Com`, `Adv^cr_Com`) anywhere, so `thm:main`'s weighted sum of
advantage terms (each with an explicit reduction adversary and running time
`Time(A)+poly(λ)`) has no Lean counterpart — the *qualitative* skeleton
(compose extractors layer by layer) exists in `Bus.segment_extract`/
`Twostep.cte`, but with no error accumulation: a perfect-KS proof composes
"for free" (no union bound needed), unlike the real bound's scaling with `m`
and `T`. No PPT-adversary type, no security-parameter families, no
negligibility predicate, no explicit reduction-adversary construction (the
paper spells these out per-lemma, e.g. `D_3^(t)`: "run `A` once, unroll the
tree to node `t`, forward to the `Π_3` challenger" — no challenger/experiment
formalism exists in Lean at all), no running-time bookkeeping. Formalizing
the *real* theorem (not just its proof skeleton) needs: (1) a
probabilistic/PPT-adversary layer (e.g. via `PMF`, as `Crypto.lean`'s own
docstring flags as future work); (2) redefining `KnowledgeSound`/
`PositionBinding`/`UpdateBinding`/`CollisionResistant` as `≤negl(λ)`-bounded
advantages; (3) reproving all five layer lemmas + memory-extractability as
genuine probabilistic reductions with union bounds (`(m-1)·`, `m·`,
`Σ_{k=1}^T` coefficients); (4) tracking reduction running times through the
composition. None of these exist yet.

Smaller gaps: the paper's CTE experiment derives `Ŝ_0,Ŝ_T` from plain
`S_0,S_T` via `Commit` as part of verification (`rem:cte-ks`); Lean's
`ZkVM.Stmt/initial/terminal` is fully abstract and imposes no such structure
— even the outermost CTE statement isn't tied to `VMState`/`CommittedVMState`
via `Com_mem`. The paper's own idealization caveat (`rem:idealized`: ROM
straight-line extraction, non-existent relativized SNARKs for PCD
composition) has no Lean counterpart since perfect KS sidesteps
rewinding-vs-straight-line distinctions by fiat.

**Implementation-priority ordering** (not requested, but useful): (c) and
(d) are least structural (bookkeeping/plumbing on `Bus.lean`); (b) needs new
relation types (`convert`,`combine`,`embed`) + a tree-induction lemma
generalizing `chain_flatten`; (a) needs new definitions (`UpdateBinding`,
full-memory reconstruction, `prop:memory-extractability`) on top of (b)+(d);
(e) is deepest — a probabilistic re-foundation of `Crypto.lean` is a
prerequisite before any other gap's lemmas can carry real quantitative
bounds.
