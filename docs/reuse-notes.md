# Reuse notes

Short, greppable "to do X, use Y in Z" entries so agents don't re-derive existing
machinery (`CONVENTIONS.md` §2, the Hicks anti-duplication trick). Add an entry
whenever you build something a later layer will want to share.

## Reductions (Issue 2)

**To phrase a security proof as a reduction**, use the extract-or-break
vocabulary in `Reduction.lean` — do not hand-roll a per-layer shape:

1. **Package the hardness assumption** as a `Reduction.HardnessAssumption`: its `Break`
   type (the witness a reduction outputs) and `IsBreak` predicate. It *holds* iff
   `Reduction.HardnessAssumption.Holds` (no genuine break exists). Existing instance:
   `Reduction.crAssumption H` (collision resistance; break = a colliding pair).
2. **State the layer lemma** as `∃ E B, Reduction.ExtractOrBreak AS A E B` — an
   extractor `E` and a **reduction `B`** (to the assumption; both plain functions,
   `CONVENTIONS.md` §1), such that every accepting proof yields a valid witness
   *or* a genuine break. Never assume the assumption inside this lemma; *produce*
   the break.
3. **Recover knowledge soundness** from
   `Reduction.knowledgeSound_of_extractOrBreak` (the one place the assumption is
   consumed) plus a `HardnessAssumption.Holds` hypothesis. For collision resistance,
   that hypothesis is `(crAssumption H).Holds` ("no colliding pair exists"), which is
   exactly `CollisionResistant H` (injectivity) — no bridge lemma.

Worked instance: `Reduction.crAssumption H` (collision resistance). The first
layer to *apply* the vocabulary end-to-end is the segment/bus layer in Issue 5
(`lem:segment`) — a reduction returning a disagreeing bus copy as a collision.

**To state collision resistance**, use `Crypto.CollisionResistant` — injectivity of
`hash` (the idealized, probability-free model). Do **not** add a second CR notion.

**To witness a break type is inhabited-and-recognizable** (I6 non-vacuity), give a
model where the assumption holds — e.g. `CryptoSanity.idHashCommitment` /
`collisionResistant_idHashCommitment` for collision resistance.
