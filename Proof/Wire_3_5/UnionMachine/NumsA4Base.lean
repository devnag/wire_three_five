import Proof.Wire_3_5.UnionMachine.NumsA3Base
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLk
import Proof.Wire_3_5.Primitive.SeedFix.C4BudD
import Proof.Wire_3_5.Primitive.Writers.ReqBridge
import Proof.Wire_3_5.FinalPass.FpInLenBase
import Proof.Wire_3_5.FinalPass.SymSz1Base
import Proof.Wire_3_5.UnionMachine.NumsPh2Base

/-! # NW phase (a), part 4: the SYM numbers at a SYM request, at a polynomial capacity

P3:2929-2941, 2987-2988, 3011-3016, 3044-3048: at a SYM request `r` of the family, the SYM numbers program
(`C4Set.numsSW`, `numsS_spec`) runs from the cell's entry (the framed input `frame fpIn` on stream `0`, the counts
`unaryList (symCounts …)` on stream `113`) at the capacity `cap₀ ≥ K₀·(|fpIn|+1)^{D₀}`, `D₀ = K_F(fe) + 2`: its needs
from `sym_needsG` at `KQ = 2^{c_A+K_F}(n+2)^{K_F}2^k ≤ 2^{c_A+2K_F}(|fpIn|+1)^{K_F+2}` (`2^k = (2^{k_h})² ≤ Q²`,
`Q ≤ |fpIn|`, the printed sample). Its registers `G 21 = |E|`, `G 41 = |FlatSeed|`, `KB 52 = Q` multiply to `vOf r`.

* `numsP`, `countsOf`, `D0`, `K0`, `stV_one`, `q_le_fpIn`, **`numsAt`**.

Paper quantities of the main type: `|E|`, `|FlatSeed|`, `Q = symCount` at the request (`V = |E|·|FlatSeed|·Q`). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

/-- The SYM request's counts (the carriers' sizes, then the circuits' bottom counts); `[]` at THR. -/
noncomputable def countsOf : PrimRequest → List ℕ
  | ⟨_, .sym, a', _, Cs, carriers, _⟩ => Data.symCounts a' Cs carriers
  | ⟨_, .thr, _, _, _, _, _⟩ => []

section Gate
variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem stV_one (m0 m1 m2 m3 : ℕ) : 1 ≤ SymDec.stV m0 m1 m2 m3 := by
  unfold SymDec.stV; exact Nat.succ_le_of_lt (by positivity)

theorem vec21 (n capS err M nc L kh a' m0 m1 m2 m3 : ℕ) :
    SymDec.numsVec n capS err M nc L kh a' m0 m1 m2 m3 21 = 2 ^ (SymDec.gP n capS err).seedBits := rfl

theorem vec41 (n capS err M nc L kh a' m0 m1 m2 m3 : ℕ) :
    SymDec.numsVec n capS err M nc L kh a' m0 m1 m2 m3 41 = 2 ^ FlatNums.fbv M (SymDec.bV nc capS) (L + 5) := rfl

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
