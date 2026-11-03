import Lean
import Proof.Wire_3_5.UnionMachine.FrontSemCap3
import Proof.Wire_3_5.UnionMachine.FrontFoldBound2
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.FrontSemPath
import Proof.Wire_3_5.UnionMachine.FrontSemTW
import Proof.Wire_3_5.UnionMachine.FrontSemFoldBase


noncomputable section
set_option maxRecDepth 4096


/-! # C6 front, the semantic core (15): the writers' fold at the machine's capacities (P3:3669-3672)

M-FoldBound2 sized the fold at its own capacity `T = value eT 2^eT s`. The front runs it at the machine's
`T = value De Ce W`, `tot = value Dt Ct W` (fixed exponents, the width `W`): **`rcostT_le`** (every round at any
`T ≤ (s+2)^t`, any atom width `≤ s + 2`, within `(s+2)^{eMt + 6}`), **`widthT_le`** (every kept tape within `tot`),
**`envFit_mono`**, **`value_mono`**, **`valueW_le`**, and at a guess **`foldCapsG`** (PathCaps' `env`, `cwT`, `len`,
`Z0`).

Paper quantity: none (the front's time, a fixed polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemFold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound
open NearCubicWires.WireExponent3_5.UnionMachine.CWIface (ParityWriterJ CarrierWriterJ)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (bitmap codesWord carrierOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode (envCodeCost atomsOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (cropBCost appendBCost)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldCat (catCost efCost)
open NearCubicWires.BlockPlatform.UnaryCalc (value tapes)

section Gen

end Gen

section Guess
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (nvG)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z)

/-- **The fold's caps at a guess** (PathCaps' `env`, `cwT`, `len`, `Z0`): with `K` bounding `q`, the variable count
and the atoms' codes words, `K ≤ W`, the envelope exponent above both modes' `eT`, `value De Ce W ≤ (K+2)^t`, and the
tape capacity's exponent above both modes' `eMt … t + 6`. -/
theorem foldCapsG (K W De Ce Dt Ct t deg : ℕ) (hq : g.q ≤ K) (hnv : nvG g ≤ K)
    (hA : ∀ X, X < nvG g → (codesWord g.mode ((foldOf (g.checkData g.translation)).atoms X)).length ≤ K)
    (hKW : K ≤ W) (hDe : ∀ m : Mode, eT (FrontCh5.PwM m) (FrontCh5.CwM m) deg ≤ De)
    (hCe : ∀ m : Mode, 2 ^ eT (FrontCh5.PwM m) (FrontCh5.CwM m) deg ≤ Ce)
    (hT : value De Ce W ≤ (K + 2) ^ t) (hDt : ∀ m : Mode, eMt (FrontCh5.PwM m) (FrontCh5.CwM m) deg t + 6 ≤ Dt)
    (hCt : 2 * 2 ^ Dt ≤ Ct) :
    (∀ X < (foldOf (g.checkData g.translation)).nv,
      EnvFit ((foldOf (g.checkData g.translation)).car X) deg (value De Ce W)) ∧
    FrontSemPath.cwG g (value De Ce W) + 1 ≤ value Dt Ct W ∧
    (∀ X ≤ (foldOf (g.checkData g.translation)).nv, ∀ t',
      ((foldOf (g.checkData g.translation)).st deg (value De Ce W) (value Dt Ct W) X (FrontCh5.PwM g.mode).t
        (FrontCh5.CwM g.mode).t t').length ≤ value Dt Ct W) ∧
    (foldOf (g.checkData g.translation)).nv + 1 ≤ value Dt Ct W := by
  have hnvF : (foldOf (g.checkData g.translation)).nv = nvG g := rfl
  have hsysF : (foldOf (g.checkData g.translation)).sys ≤ K := by
    show g.pcpp.systematicBits ≤ K
    have : nvG g = g.pcpp.systematicBits + g.pcpp.auxiliaryBits := rfl
    omega
  have hA' : ∀ X < (foldOf (g.checkData g.translation)).nv,
      (codesWord g.mode ((foldOf (g.checkData g.translation)).atoms X)).length ≤ K := fun X hX => hA X hX
  have hnv' : (foldOf (g.checkData g.translation)).nv ≤ K := hnv
  have hE := hDt g.mode
  have hEt : t ≤ eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t := by unfold eMt; omega
  have hE1 : 1 ≤ eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t := by unfold eMt; omega
  have hv := pow_le_value K W (eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t + 6) Dt Ct hKW hE hCt
  have hv0 := pow_le_value K W (eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t) Dt Ct hKW (by omega) hCt
  have hp6 : (K + 2) ^ eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t ≤
      (K + 2) ^ (eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t + 6) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpt : (K + 2) ^ t ≤ (K + 2) ^ eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t :=
    Nat.pow_le_pow_right (by omega) hEt
  have hK2 : K + 2 ≤ (K + 2) ^ eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t :=
    Nat.le_self_pow (by omega) _
  refine ⟨fun X hX => ?_, ?_, fun X hX t' => ?_, by omega⟩
  · exact envFit_mono (FrontFoldBound.envFit (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode)
      (foldOf (g.checkData g.translation)) K deg hq X (hA' X hX)) (value_mono (hDe g.mode) (hCe g.mode) hKW)
  · have hWa : FrontSemPath.WaG g ≤ K + 2 := by
      have := foldr_max_le ((foldOf (g.checkData g.translation)).as.map List.length) K (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
        exact FrontFoldBound.as_len _ K hA' a ha)
      unfold FrontSemPath.WaG; omega
    have hc : FrontSemPath.cwG g (value De Ce W) ≤
        (K + 2) ^ (eMt (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) deg t + 6) := by
      unfold FrontSemPath.cwG
      exact supR_le _ _ _ (fun X hX => rcostT_le (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode)
        (foldOf (g.checkData g.translation)) K deg hq hA' X hX hnv' (value De Ce W) t (FrontSemPath.WaG g) hT hWa)
    omega
  · exact widthT_le (FrontCh5.PwM g.mode) (FrontCh5.CwM g.mode) (foldOf (g.checkData g.translation)) K deg hq hnv'
      hsysF hA' X hX (value De Ce W) t (value Dt Ct W) (by omega) (by omega) _ _ t'

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemFold

end
