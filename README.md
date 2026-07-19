# VanillaZkVM

Note. This is WIP. This is *purely AI made* so far, and I just did some sanity checks so far.


Things that are not done at all:
* extraction of non-committed memory
* actual recursion; so far it is just a two step proof: (1) prove each segment (2) merge these proofs

The proposition-level core of bus delegation is modeled in `VanillaZkVM/Bus.lean`:
the segment extractor composes the four inner-circuit extractors and uses
collision-resistance to show that their extracted buses are identical. Concrete
bus entries and opcode predicates remain abstract.
