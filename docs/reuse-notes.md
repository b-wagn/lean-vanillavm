# Reuse notes

Short, greppable "to do X, use Y in Z" entries so agents don't re-derive existing
machinery (`CONVENTIONS.md` §2, the Hicks anti-duplication trick). Add an entry
whenever you build something a later layer will want to share.

## Reductions (Issue 2)

**To phrase a security proof as a reduction**, use the extract-or-break
vocabulary in `Reduction.lean` — do not hand-roll a per-layer shape:

1. **Package the hardness assumption** as a `Reduction.Assumption`: its `Break`
   type (the witness a reduction outputs) and `IsBreak` predicate. It *holds* iff
   `Reduction.Assumption.Holds` (no genuine break exists). Existing instance:
   `Reduction.crAssumption H k` (collision resistance at key `k`; break = a
   colliding pair under `k`).
2. **State the layer lemma** as `∃ E B, Reduction.ExtractOrBreak AS A E B` — a
   witness-extractor `E` and a **break-extractor `B`** (both plain functions,
   `CONVENTIONS.md` §1), such that every accepting proof yields a valid witness
   *or* a genuine break. Never assume the assumption inside this lemma; *produce*
   the break.
3. **Recover knowledge soundness** from
   `Reduction.knowledgeSound_of_extractOrBreak` (the one place the assumption is
   consumed) plus an `Assumption.Holds` hypothesis. For collision resistance at a
   key `k`, that hypothesis is `(crAssumption H k).Holds` ("no pair collides under
   `k`"), which `CollisionResistant H` supplies at every key — no bridge lemma.

Worked instance: `Reduction.crAssumption H k` (collision resistance at key `k`).
The first layer to *apply* the vocabulary end-to-end is the segment/bus layer in
Issue 5 (`lem:segment`), instantiated at the execution's bus key — a
break-extractor returning a disagreeing bus copy as a collision.

**To state collision resistance**, use `Crypto.CollisionResistant` (keyed,
finder-based; the finder is a plain function of the key). In the perfect model it
equals per-key injectivity via `CryptoSanity.collisionResistant_iff_injective`;
efficiency/probability are Issue 6. Do **not** add a second CR notion.

**To witness a break type is inhabited-and-recognizable** (I6 non-vacuity), give a
model where the assumption holds — e.g. `CryptoSanity.idHashCommitment` /
`collisionResistant_idHashCommitment` for collision resistance.
