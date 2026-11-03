import Proof.Wire_3_5.UnionMachine.FrontSemPathCapsBase

/-! # C6 front, the semantic core (19): the master size bound at the pinned setup (P3:3485-3491, 3669-3691)

At the pinned setup `SUE` a single polynomial **`MS c₀ q`** of the width dominates every size of every guess the
front reads past the onset (**`MS_pq`**): the PCPP output (`Kp`, the size law), the mass and the grid (`Λ̄ ≤ K_Λ(q+2)³`,
`s = C_δ Λ̄²`), the atoms' codes at the description envelope (`Kc`), the atoms' codes words, the carriers' codes
(the fold's writers, `Wc_le`), the translation (`r` codes below `2^s ≤ q+1`), the constant, the description bits,
`c_r`, and a free constant `c₀`. **`genv_of`**: every guess within the size cap that passes the atom test has the
size envelope `GEnv g Λ̄(q) (MS c₀ q)`.

Paper quantity of the main types: the guess's sizes against the width `q`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnvS
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (PQ)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (codesWord)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound (lc)

section SUE
variable (l : Literals) (e coef A : ℕ) (L : Language) 

/-- The carriers' code exponent (both modes). -/
noncomputable def Lc : ℕ :=
  lc (FrontCh5.PwM .thr) (FrontCh5.CwM .thr) + lc (FrontCh5.PwM .sym) (FrontCh5.CwM .sym) + 2

/-- The constant's code word bound. -/
def CC : ℕ := (natWord (CWConst.constCode .thr)).length + (natWord (CWConst.constCode .sym)).length

end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnvS
