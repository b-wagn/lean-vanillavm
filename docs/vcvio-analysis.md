# VCVio Analysis for lean-vanillavm zkVM Security Proofs

Source: `C:/Dmitry/Research/FV/VCVio-main` (467 .lean files; sampled ~15 files + 6 docs/agents/*.md
+ README/AGENTS/CONTRIBUTING, not the full tree).

## Purpose & scope

VCVio = "Verifying Cryptography via Interactions and Oracles." A Lean 4 / Mathlib library for
machine-checked cryptographic proofs, in the lineage of FCF (Foundational Cryptography Framework,
Rocq). Core abstraction: `OracleComp spec α`, a free monad over the polynomial functor induced by
an oracle signature `spec : OracleSpec ι := ι → Type`. `ProbComp α := OracleComp unifSpec α`
specializes to pure probabilistic computation (only oracle = uniform sampling).

Three semantic views obtained by `simulateQ` (the universal fold of the free monad) into different
target monads:
- `support` — into `Set`/`SetM` (possible outputs, no probabilities).
- `evalDist` / `probOutput` / `Pr[...]` — into `SPMF = OptionT PMF` (needs `[IsProbabilitySpec spec]`;
  uniform-specific lemmas need `[IsUniformSpec spec]`).
- `simulateQ impl` generally — into any monad, used to *implement* oracles (random oracle,
  logging, caching, reductions that answer queries by embedding a challenge).

On top of this framework: generic crypto primitives (encryption, signatures, Σ-protocols,
commitments), transforms (Fiat-Shamir, Fischlin), hardness assumptions (DLog/CDH/DDH, LWE, SIS),
forking lemmas (Bellare-Neven seeded fork, replay fork), a program logic (pRHL-style relational +
Hoare-style unary triples, with interactive tactics `by_equiv`/`by_hoare`/`rvcstep`/`vcstep`/
`game_trans`), and a full query-cost/expected-cost/asymptotic-security layer. `LatticeCrypto/`
builds ML-DSA, ML-KEM, Falcon on top; `HashSig/` builds SLH-DSA (SPHINCS+).

The project's own self-assessment (README): "well suited to concrete security bounds for
reductions... Asymptotic security and query-cost and expected-cost reasoning are also supported.
**Polynomial-time infrastructure and some tooling and automation remain under active
development.**" This is corroborated in the code (see "PolyTime scaffolding" below) — directly
relevant since our project's own PPT/cost layer is still to be built.

## Directory map

| Dir | Contents |
|---|---|
| `VCVio/` | oracle-computation framework, probability semantics, program logic, generic crypto abstractions, query-tracking/cost |
| `VCVio/OracleComp/` | core `OracleComp`, `SimSemantics`, `Coercions`/`SubSpec`, `Constructions`, `QueryTracking/` (cost model), `ProbComp` |
| `VCVio/CryptoFoundations/` | `SecExp`, `HardnessAssumptions/` (DLog/CDH/DDH, hard relations), `Asymptotics/` (`Security.lean`, `Negligible.lean`), `SeededFork.lean`, `ReplayFork.lean`, `Fischlin.lean`, `FiatShamir/`, `FujisakiOkamoto/`, encryption/signature/commitment structures |
| `VCVio/ProgramLogic/` | relational (`by_equiv`) and unary (`by_hoare`) proof modes, `Tactics.lean` |
| `VCVio/Interaction/UC/` | computational UC-style composition/emulation layer |
| `ToMathlib/` | Mathlib-facing utilities not yet upstreamed (writer monad cost facts, PMF tail sums) |
| `LatticeCrypto/` | lattice algebra, hardness assumptions (LWE/SIS), ML-DSA/ML-KEM/Falcon specs + concrete impls |
| `HashSig/` | SLH-DSA (SPHINCS+) |
| `Extern/` | native FFI bindings — proof libraries must never import this (link-safety isolation) |
| `Interop/` | experimental Rust-verification bridges (hax/aeneas) — strict one-way TCB isolation, enforced by a CI script |
| `Examples/` | compact canonical worked proofs: OneTimePad, ElGamal, Schnorr, program-logic walkthroughs |
| `docs/agents/*.md` | ~10 topic guides (oracle-comp, probability, crypto, query-tracking, program-logic, proof-workflows, gotchas, notation, lattice, interaction, interop, end-to-end-examples) — this is the most valuable artifact in the repo for a newcomer |
| `LatticeCryptoTest/`, `HashSigTest/`, `VCVioTest/` | ACVP vectors, differential tests vs. native code, smoke tests |

## Reusable components

Assessment against: a project that currently idealizes crypto as "perfect" (probability-free) and
wants to *later* add concrete/asymptotic security, running time/cost of reductions, and explicit
reductions to hardness assumptions.

1. **`VCVio/CryptoFoundations/Asymptotics/Security.lean`** — `SecurityExp`/`SecurityGame Adv`
   package an advantage function (`ℕ → ℝ≥0∞` or `Adv → ℕ → ℝ≥0∞`) *decoupled* from how the game is
   defined, plus generic meta-theorems: `secureAgainst_of_reduction` (tight reduction),
   `secureAgainst_of_poly_reduction` (polynomial-loss reduction), `secureAgainst_of_close`
   (game-hop with negligible slack `ε`), `secureAgainst_of_hybrid` (chain of k games). **This is
   the single most directly transplantable piece**: if lean-vanillavm ever wants "scheme X secure
   against PPT adversaries assuming hardness of Y," this file is a near-drop-in scaffold — you
   supply your own `advantage`/`isPPT`/`reduce`, get the composition lemmas for free.
2. **`VCVio/CryptoFoundations/Asymptotics/Negligible.lean`** — `negligible := SuperpolynomialDecay
   atTop (↑x) f` over `ℕ → ℝ≥0∞`, with closure lemmas (`negligible_add`, `negligible_const_mul`,
   `negligible_sum`, `negligible_polynomial_mul`, `negligible_pow_mul`, `negligible_of_le`). Small,
   self-contained, ~90 lines, easy to lift wholesale as the negligibility vocabulary once concrete
   security bounds are wanted.
3. **`VCVio/OracleComp/QueryTracking/{WriterCost,QueryCost,CostModel}.lean`** — a layered
   running-time model: writer-monad pathwise cost (`Cost[oa] ≤ w`), generic weighted query-cost
   accounting (`QueryCost[oa in runtime by costFn] ≤ w`), expected cost via `wp`/Markov's
   inequality (`probEvent_cost_gt_le_expectedCost_div`), and an `OracleComp`-specific facade
   (`CostModel`, `expectedCost`, `WorstCaseCostBound`/`ExpectedCostBound`). Directly relevant if
   lean-vanillavm wants to state "reduction B runs in time ≤ p(λ)·time(A) + poly(λ)" — the
   pattern (structure holding a per-query cost function, `AddWriterT`-based accumulation, bridge
   from pathwise bound to expectation via Markov) is reusable even without importing the code.
4. **`VCVio/OracleComp/QueryTracking/QueryBound.lean`** — `IsQueryBound`/`IsPerIndexQueryBound`
   (worst-case per-oracle query counts) and `PolyQueries`/`PolyQueryUpperBound` (query counts
   polynomially bounded in security parameter). Useful vocabulary for "adversary makes at most
   `q(λ)` queries."
5. **`VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`** — a complete, compact
   worked example of the exact thing our project wants to do later: define hardness assumptions
   (DLog/CDH/DDH) as `Type → Type → ProbComp _` adversary types + experiments, then write explicit
   **reduction functions** (`cdhToDDHReduction`, `dlogToCDHReduction`, `dlogToDDHReduction` — plain
   `def`s that embed one challenge into another adversary's interface) and prove **concrete
   (non-asymptotic) advantage-loss theorems** relating them (`dlogSuccess_sq_le_cdhSuccess_...`).
   This is the cleanest template for "if adversary A breaks our scheme, reduction R(A) breaks
   assumption H" with an explicit, checkable probability bound — exactly the shape a future
   concrete-security pass over lean-vanillavm's idealized proofs would need.
6. **`VCVio/CryptoFoundations/SeededFork.lean` / `ReplayFork.lean`** — mechanized Bellare-Neven
   forking lemma with expected-query-count bounds on the forked adversary
   (`expectedQueryCount_seededForkWithSeedValue_le`, `seededForkExpectedQueryWork_le`) — a
   reusable pattern for rewinding-style reductions with running-time accounting, should
   Fiat-Shamir-style extraction ever be relevant to a zkVM proof.
7. **`VCVio/CryptoFoundations/{SymmEncAlg,AsymmEncAlg,SignatureAlg,CommitmentScheme}.lean`,
   `SigmaProtocol`/`IdenSchemeWithAbort`** — plain monad-parametric `structure`s for primitives
   (see docs/agents/crypto.md for the exact signatures). Good precedent for how to keep an
   "idealized" primitive interface (`m` abstract) that can later be instantiated at `ProbComp` for
   concrete security without touching the interface.
8. **`docs/agents/*.md`** — not code, but immediately reusable *documentation infrastructure*: a
   per-topic guide format (What/Main files/Worked examples/Gotchas/When-to-prove-which-theorem)
   that could be adapted as `docs/agents/*.md` in lean-vanillavm once its own layers stabilize.

Lower priority / likely not directly reusable: `LatticeCrypto/`, `HashSig/`, `Extern/`, `Interop/`
are scheme-specific or infra-specific and not obviously relevant to a zkVM proof unless
lean-vanillavm starts modeling a specific PQ signature inside the VM.

## Writing style & conventions

- **File prologue** is fixed and enforced by convention (not tooling): copyright/license/authors
  header block, blank line, imports, blank line, module docstring (`/-! ... -/`). Exactly one
  blank line between each block.
  ```lean
  /-
  Copyright (c) 2024 Devon Tuma. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Devon Tuma, Quang Dao
  -/
  import VCVio.CryptoFoundations.SymmEncAlg
  ...

  /-!
  # One Time Pad
  ...
  -/
  ```
- **Module docstrings** open with a `#` title, a short paragraph, then `## Main Definitions` /
  `## Main Results` bullet lists naming the key declarations (not restating their statements).
  References/notation tables go in the module docstring when they materially help (see the
  DLog/CDH/DDH file's additive-vs-multiplicative notation table).
- **Section headers inside a file** use Mathlib-style `/-! ## Title -/` doc-comments, never ASCII
  banner comments (`-- ====...`). This is explicitly mandated in CONTRIBUTING.md/AGENTS.md
  *because* ASCII banners don't render in `doc-gen4` output and make files feel artificially
  partitioned — "if a section is large enough to want a loud header, it's usually large enough to
  want its own namespace or file."
  ```lean
  /-! ## DDH (Decisional Diffie-Hellman) -/
  ```
- **Naming**: strict Mathlib convention. Structures/types/classes in `UpperCamelCase`
  (`SecExp`, `SymmEncAlg`, `DLogAdversary`); theorem/lemma names in `snake_case` following
  `{head_symbol}_{operation}_{rhs_form}` (e.g. `probOutput_bind_eq_tsum`, `negligible_const_mul`,
  `dlogSuccess_sq_le_cdhSuccess_dlogToCDHReduction`); ordinary term-level functions in
  `lowerCamelCase` (`dlogExp`, `cdhToDDHReduction`, `ddhGuessAdvantage`).
- **Declaration docstrings** (`/-- ... -/`) describe *what a definition is or what a theorem
  states*, never its history. Explicit repo rule: never write "replaces X" / "renamed from Y" /
  mention removed declarations — docstrings are meant to be read cold, standalone.
  ```lean
  /-- A DLog adversary receives a generator and a group element, and tries to find the
  discrete logarithm (scalar). -/
  def DLogAdversary (F G : Type) := G → G → ProbComp F
  ```
- **Structure vs class vs def**: crypto primitives (`SymmEncAlg`, `SigmaProtocol`,
  `CostModel`, `SecurityExp`) are plain `structure`s parametrized over an abstract monad `m` —
  *not* typeclasses. Typeclasses (`[IsProbabilitySpec spec]`, `[IsUniformSpec spec]`,
  `[SampleableType F]`) are reserved for semantic capabilities the ambient spec/type needs to
  support (uniform sampling, decidability, fintype-ness), threaded through `variable` sections
  and kept as narrow as possible per theorem (explicit style guidance in query-tracking.md:
  "put only genuinely shared assumptions in section variable blocks... if a proof needs extra
  decidability or classical choice, install it locally").
- **Namespacing**: one namespace per file/topic matching the file's main definition
  (`namespace DiffieHellman ... end DiffieHellman`, `namespace oneTimePad ... end oneTimePad`),
  with nested `section`/`variable` blocks scoping typeclass assumptions to just the lemmas that
  need them.
- **Adversaries are always plain functions**, not bundled structures with an implicit efficiency
  field — e.g. `DLogAdversary F G := G → G → ProbComp F`. Efficiency (query bounds / poly-time) is
  a *separate* predicate applied to the adversary (`IsPerIndexQueryBound`, `PolyQueries`), not
  baked into the type. `BoundedAdversary` (a structure bundling `run` + a query-bound proof) is
  the one place efficiency is bundled, and it's reserved for cases where the bound must travel
  with the value.
- **Reductions are literal `def`s**, not existence proofs: a reduction from breaking H to breaking
  H' is a concrete function `Adversary(H) → Adversary(H')` (e.g. `cdhToDDHReduction`), and the
  security theorem is a `≤` inequality between advantage functions evaluated at the reduction's
  image. Advantage-loss composition (tight / polynomial-loss / hybrid) is handled by generic
  lemmas over abstract advantage functions (`SecurityGame.secureAgainst_of_*`), so the same lemma
  serves any concrete instantiation.
- **Tactic style**: heavy use of a custom `simp`-set macro `monad_norm` (bundles `pure_bind`,
  `bind_assoc`, `bind_pure`, `map_pure`, etc.) as the default monadic normalizer, with an explicit
  repo rule to prefer it over hand-rolled lemma lists ("documents intent, keeps proofs robust").
  Program-logic tactics (`by_equiv`, `by_hoare`, `rvcstep`, `vcstep`, `game_trans`) provide an
  interactive layer over the raw simp/rewrite proofs for game-hopping arguments.
- **Attribution discipline** (CONTRIBUTING.md): new files get a fresh header with current-year +
  author; routine edits preserve the existing header untouched; only "genuinely new or materially
  replaced" files get re-attributed. No separate "AI-assisted" attribution line is ever added.
- **`autoImplicit` is off globally** (set once in `lakefile.lean`), never per-file — every
  variable must be explicit. Similarly, no linter is ever silenced locally to dodge a warning;
  the one documented repo-wide exception (`weak.linter.unicodeLinter, false`, for FIPS math
  notation) is called out explicitly rather than left silent.
- **Module layering is written down as an explicit DAG** in AGENTS.md (e.g. `ToMathlib → Prelude →
  EvalDist/Defs → OracleComp core → EvalDist bridge → {SimSemantics, QueryTracking,
  Constructions, Coercions, ProbComp} → {ProgramLogic, CryptoFoundations,
  CryptoFoundations/Asymptotics} → Examples`) and enforced by CI shell scripts for the two
  sharpest boundaries (`Extern` link-safety isolation, `Interop` TCB isolation).
- **"Currently unused / scaffolding" is stated candidly in docstrings** rather than deleted, e.g.
  `TotalQueryUpperBound`/`PolyQueryUpperBound` in `QueryBound.lean` are explicitly marked
  "Currently unused outside this file; retained as scaffolding for future asymptotic analyses."
  This is a useful convention for a project (like ours) that's deliberately building
  infrastructure ahead of the theorems that will consume it.

## Modeling of reductions / running time / advantages

This is the part most load-bearing for lean-vanillavm's stated future direction.

**Advantage functions** are always plain numeric functions, never wrapped in a class:
- `SecExp.advantage := 1 - Pr[⊥ | exp.main]` (failure-based; "advantage" = success probability).
- `ProbComp.guessAdvantage`, `boolBiasAdvantage`, `distAdvantage`, `boolDistAdvantage` — all return
  `ℝ` via `.toReal`, deliberately *not* `ℝ≥0∞`, because `ℝ≥0∞` subtraction truncates at 0 and would
  silently hide "adversary does worse than random" cases.
- Asymptotically, `SecurityExp := { advantage : ℕ → ℝ≥0∞ }` and
  `SecurityGame Adv := { advantage : Adv → ℕ → ℝ≥0∞ }` are deliberately decoupled from any
  specific game shape — smart constructors (`ofSecExp`, `ofDistGame`, `ofGuessGame`) convert a
  concrete game family into this abstract shape, and all the meta-theorems (reduction, game-hop,
  hybrid, polynomial-loss) are stated once against the abstract `advantage : Adv → ℕ → ℝ≥0∞` and
  reused for every concrete instantiation.

**Reductions** are always concrete, computable functions `reduce : Adv → Adv'` between adversary
types (e.g. `dlogToCDHReduction`, `cdhToDDHReduction`), composed by ordinary function composition
(`dlogToDDHReduction := cdhToDDHReduction ∘ dlogToCDHReduction`, written point-free via
partial application). The *security theorem* is always stated as an inequality:
`g.advantage A n ≤ g'.advantage (reduce A) n` (tight) or `≤ loss(n) * g'.advantage (reduce A) n`
(polynomial loss) or `≤ g'.advantage (reduce A) n + ε n` (game-hop with slack), then
`secureAgainst_of_*` lemmas lift these into "if target is secure, so is source." Concretely (in
`DiffieHellman.lean`) this is proved down to explicit `tsum`/probability manipulation, not left
abstract — e.g. `dlogSuccess_sq_le_cdhSuccess_dlogToCDHReduction` is a fully constructive,
non-asymptotic probability bound.

**Efficiency / running time** is handled as a *separate concern* layered on top of the pure
probability semantics, via `simulateQ` into a writer monad that additively accumulates cost:
- Pathwise (worst-case) cost: `AddWriterT.PathwiseCostAtMost`, exposed as
  `QueryCost[ oa in runtime by costFn ] ≤ w` / `Queries[ oa in runtime ] ≤ n`.
- Output-determined cost: `UsesCostAs`/`CostsAs` — cost is a function of the final output; used
  when every run producing a given output pays the same cost (e.g. one Fiat-Shamir attempt).
- Expected cost: `ExpectedQueryCost[...]`/`ExpectedQueries[...]`, derived from pathwise bounds or
  `UsesCostAs` via generic bridge lemmas, with Markov's-inequality-style tail bounds
  (`probEvent_cost_gt_le_expectedCost_div`) and PMF tail-sum identities
  (`E[T] = ∑ Pr[i < T]`) for stopping-time-style loops (retry/abort constructions).
- Query-count *bounds* (`IsQueryBound`, `IsPerIndexQueryBound`, `PolyQueries`) are the
  "polynomial-time" surrogate actually used today; genuine asymptotic PPT/poly-time
  infrastructure is explicitly flagged as **under active development** — e.g.
  `WorstCasePolyTime`/`ExpectedPolyTime` are *named and documented* in `CostModel.lean`'s module
  docstring ("Asymptotic polynomial-time predicates for computation families... Strict
  polynomial time implies expected polynomial time") but **no such definitions currently exist in
  the file** — this is aspirational scaffolding, not implemented API. Worth knowing before
  assuming this piece is ready to borrow.
- The abstract efficiency predicate in the security-game layer, `isPPT : Adv → Prop`, is left
  fully abstract in `Security.lean` — callers instantiate it with `PolyQueries` or any custom
  notion. This is a deliberate design choice: the reduction/hybrid meta-theorems don't need to
  know what "efficient" means, only that it's preserved by `reduce`.

**Takeaway for lean-vanillavm**: the advantage/reduction/game-hop layer (`Security.lean`,
`Negligible.lean`, the DiffieHellman reduction pattern) is mature and directly reusable as design
inspiration. The running-time/cost layer (`QueryCost`/`CostModel`/`WriterCost`) is more developed
than the asymptotic-PPT layer, which is still partly aspirational — so if/when lean-vanillavm adds
its own cost model, expect to build the PPT-family definitions from scratch rather than finding a
ready-made one here, but the query-bound/expected-cost machinery underneath is a solid template.

## Recommended adoptions

Ranked by (usefulness to stated future direction) × (ease of adapting without pulling in the
whole framework):

1. **Advantage/negligibility vocabulary** (`Negligible.lean`, ~90 lines) — smallest, cleanest,
   zero framework dependency beyond Mathlib's `SuperpolynomialDecay`. Adopt near-verbatim whenever
   concrete-security statements are needed.
2. **`SecurityExp`/`SecurityGame` reduction & game-hop meta-theorems** (`Security.lean`) — adopt
   the *pattern* (decouple advantage from game shape; state reduction/hybrid/poly-loss lemmas once
   against an abstract advantage function) even if the concrete Lean is rewritten for
   lean-vanillavm's own probability/cost stack.
3. **Explicit reduction-as-function + inequality-theorem style** (`DiffieHellman.lean`) — adopt
   as the house style for any future "assumption ⇒ scheme security" proof: define the reduction
   as a plain computable term, state security as a probability inequality between the original
   and reduced adversary, prove it by direct calculation.
4. **Writing-style conventions**: `/-! ## -/` section headers (never ASCII banners), module
   docstrings with `Main Definitions`/`Main Results` bullets, `{head}_{op}_{rhs}` snake_case
   lemma naming, ahistorical docstrings, narrow per-theorem typeclass assumptions. Cheap to adopt
   immediately and independent of any code reuse decision.
5. **`docs/agents/*.md` per-topic guide format** — worth mirroring once lean-vanillavm's own
   layering stabilizes (e.g. a `docs/agents/cost-model.md` once a cost layer exists), as a way to
   keep AGENTS.md itself short while giving deep guidance per subsystem.
6. **Query-cost / expected-cost layering pattern** (`WriterCost`/`QueryCost`/`CostModel`) — most
   valuable but also most work to adapt, since it presupposes an `OracleComp`-style free-monad
   representation of computations that lean-vanillavm may not have. Treat as a design reference
   (three cost notions: pathwise / output-indexed / expected; Markov's-inequality bridge) rather
   than code to import.
7. **Module-layering DAG + CI isolation scripts** (`AGENTS.md` diagram +
   `scripts/check-extern-isolation.sh` / `check-interop-isolation.sh`) — adopt the *idea* (write
   down the intended import DAG explicitly, enforce the sharpest boundaries with a CI script) if
   lean-vanillavm ever grows enough modules to need it; not urgent at current size.
