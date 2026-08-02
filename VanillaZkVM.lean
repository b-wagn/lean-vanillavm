import VanillaZkVM.Crypto        -- generic cryptography (defs only): relations, arguments, commitments
import VanillaZkVM.CryptoSanity  -- non-vacuity models for the crypto kernel (trivialAS)
import VanillaZkVM.Zkvm          -- abstract zkVM system, CTE, and CTE ↔ knowledge soundness
import VanillaZkVM.Step          -- canonical plain/committed/bus step-interface contract
import VanillaZkVM.ZkvmSanity    -- accepting one-step non-vacuity model (private examples)
import VanillaZkVM.Trace         -- reusable trace-concatenation lemma (concatTrace / chain_flatten)
import VanillaZkVM.Memory        -- memory extractability: committed↔full step lift and trace fold
import VanillaZkVM.MemorySanity  -- positive/negative binding models (update binding strictly stronger)
import VanillaZkVM.Bus           -- four inner circuits and collision-resistant bus unification
import VanillaZkVM.Twostep       -- minimal two-relation zkVM instantiating the abstract one
