# VanillaZkVM

Note. This is WIP. This is *purely AI made* so far, and I just did some sanity checks so far.


Things that are not yet complete:
* full-trace reconstruction of non-committed memory (`step_mem_extract` and
  extraction of the per-step descriptors/openings are implemented)
* delegating to a bus
* actual recursion; so far it is just a two step proof: (1) prove each segment (2) merge these proofs
