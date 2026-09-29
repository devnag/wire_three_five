import Proof.Wire_3_5.Primitive.Writers.ThrStage1
import Proof.Wire_3_5.Primitive.Writers.ThrSet5

/-! # c4 THR block, the THR stage from its setup (`thrStage_run`)

The THR stage's machine `thrStageM`: the wrapper with the THR setup `setupT` (the big bank), the decision loop of a
child family of the shape, the THR finisher. From the setup's run hypotheses (`setupT_run`), the numbers machine's
words (`symClean` at the call's numbers), and the numbers' links to the child family (`ThrLinks`: `SymBank`
link fields), the stage ends with `sampleWord kh (seedPairs P s) ++ hbF` on port `2`.

Paper quantity of the main type: the THR stage's output, the fixed seed's samples then the hash bits (P3:2932-2937,
3011-3016, 3034-3038, 2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- **The numbers' links to the child family** (`SymBank` link fields). -/
structure ThrLinks (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT q uu : ℕ) (v : List Bool)
    (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) : Prop where
  e_ell : P.ell = ell
  e_kh : P.kh = kh
  e_Q : P.Q = Q
  e_ellQ : ell = max (kh + kh) (Nat.clog 2 Q)
  e_TW : fr 0 = TWd
  e_Cap : fr 1 = Cap
  e_q : fr 2 = q
  e_dd : dd = derVals Q kh TWd Cap
  e_cnt : cnt = nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh)
  e_mod : P.modulus = GF.firstPrimitive ell
  e_uu : uu = 2 ^ d2
  e_v : v = SeedFix.blockWord ents
  h_ell1 : 1 ≤ ell

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
