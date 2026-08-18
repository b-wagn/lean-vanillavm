# Normative Vanilla zkVM paper revision

The ground truth for this formalization is the Vanilla zkVM in
`zkvm-whitepaper/sampleVM/`. Until the paper-side correction is merged into that
repository's default branch, this repository pins the following revision:

```text
repository: https://github.com/khovratovich/zkvm-whitepaper
revision:   a0f5e0b63395a2fddce3f949c4de1df9264a174b
branch:     proof
```

On **2026-07-29**, Dmitry accepted the review finding that this discrepancy
needed correction. This Issue 0 draft pins the available corrected revision
above; the exact hash should be confirmed when the PR is reviewed.

## Why the pin is necessary

At the 2026-07-29 review point, the default paper branch had an internal
mismatch:

- `def:cte` lets the adversary select the program code and step count `T`;
- `thm:main` treats `T` as a fixed system parameter; and
- Lean's abstract `ZkVM` likewise stores one fixed `T`.

The pinned revision corrects `def:cte`: program code and `T` are fixed zkVM
system parameters, while the adversary selects the boundary states and final
proof. Thus the current Lean signature

```text
ZkVM.T : Nat
```

is intentional and faithful to the pinned revision. It is not an unnoticed
restriction of the adversary.

## Known terminology residue

The last sentence following `eq:step-bus2` in ch03 still says
“punctured-binding advantages.” The normative `def:binding`,
`prop:memory-extractability`, and Step 6 of `thm:main` in ch05 all use
**position binding plus update binding**, and explain why update binding is the
property that forces an accepted commitment after a write to equal `Commit` of
the updated memory.
Issue 1 follows those formal statements; the ch03 occurrence is treated as a
stale term, not as a third commitment assumption.

## Change control

When the correction lands on the whitepaper's default branch, replace this pin
with the merged commit and re-check every affected `CORRESPONDENCE.md` row. A
future decision to make `T` statement-dependent would change the frozen
`ZkVM`/`TraceValid` interface (I4) and therefore requires an explicit
constitutional change; it must not happen as an incidental refactor.
