import Proof.CaseAnalysis.FinalLedgerAssembly
import Proof.MachineModel.TopDownSelectedAssembly
import Proof.MachineModel.TopDownWorkspaceSelectedBudget

/-! # R1: the runtime contract, proved before the source fuel exists

Paper: `paper.tex:1111-1112` "This charge is added to, and never multiplied by, the
`2^{q-K}` enumeration of columns"; `:1222-1231` "`q^{h_D}2^{q-K}poly(q) ≤ 2^q/q^σ` by the
choice of κ. The preprocessing term is added"; `:2303-2307` "take `κ ≥ h_D+σ+c_1`"; order
`:1184-1188`. Consumer: the last conjunct of `MaskedRecipe`
(`Proof/SourceAssembly/MaskSource.lean`) at `tableDegree = 0` (plan.md §12.1).
Charged to: that recipe's `remainingCoefficient`, `remainingOnset`, `tableCoefficient`.

For ANY fuel `F` that splits, eventually, into the three paper classes
* source polynomial `cP*(n+1)^dP`,
* table `cT*((q+1)^hT*2^(q-normalizedLiveCount q L))` with `hT+σ+2 ≤ L` (L after hT),
* small `cS*((q+1)^hS*2^(q/m))`, `2 ≤ m` (`m = 4` covers Header and fixed smallSize powers),
the consumer's inequality holds with the SAME degree `dP` and `tableDegree = 0`. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RuntimeShape
open SupplierEstimator SupplierCapacity

/-! ## 1. The logarithm facts the table saving uses -/

/-! ## 2. Absorption of each class into the consumer's allowance -/

/-! ## 3. The shape theorem, generic in the width function -/

/-! ## 4. At the consumer's own width, logarithm and sigma -/

open P1TopDown



end NearCubicWires.RuntimeShape
