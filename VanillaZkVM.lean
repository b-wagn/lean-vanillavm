import VanillaZkVM.Crypto   -- generic cryptography: relations, arguments, commitments
import VanillaZkVM.Zkvm     -- abstract zkVM system, CTE, and CTE ↔ knowledge soundness
import VanillaZkVM.Memory   -- committed/full-memory steps and explicit reconstruction
import VanillaZkVM.MemoryTrace -- trace fold and full initial/final boundaries
import VanillaZkVM.MemorySanity -- non-vacuity model and append-bit counterexample
import VanillaZkVM.Bus      -- four inner circuits and collision-resistant bus unification
import VanillaZkVM.BusMemory -- Bus extraction composed with full-memory reconstruction
import VanillaZkVM.Twostep  -- minimal two-relation zkVM instantiating the abstract one
