import Proof.SourceAssembly.SourceFactorSelWordsCost
import Proof.Packets.SrcStartBankCost

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsCost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

section sb
variable (a : DecompositionAlgorithm)

theorem sb_cost : PolB a (fun x => (NearCubicWires.SourceStart.Bank.sb a).cost x.1) := by
  have hb : PolB a (fun x => x.1.nativeWord.length + x.1.q + 1) :=
    pLin a 3 _ (fun x => by obtain ⟨hq, hn, _⟩ := sizes_le a x.1; omega)
  exact PolB.mul (PolB.const NearCubicWires.SourceStart.Bank.bankK) (PolB.pow hb 4 (fun _ => le_refl _))
    (fun x => NearCubicWires.SourceStart.Bank.bankCost_le a x.1)

theorem sb_sizes : PolB a (fun x => (NearCubicWires.SourceStart.Bank.sb a).B x.1 +
    (NearCubicWires.SourceStart.Bank.sb a).w x.1 + (NearCubicWires.SourceStart.Bank.sb a).Pc x.1) := by
  have hb : PolB a (fun x => x.1.nativeWord.length + x.1.q + 1) :=
    pLin a 3 _ (fun x => by obtain ⟨hq, hn, _⟩ := sizes_le a x.1; omega)
  have hP : PolB a (fun x => 16777216 * (x.1.nativeWord.length + x.1.q + 1) ^ 3) :=
    PolB.mul (PolB.const 16777216) (PolB.pow hb 3 (fun _ => le_refl _)) (fun _ => le_refl _)
  refine PolB.add (PolB.mul (PolB.const 2) hb (fun _ => le_refl _)) hP (fun x => ?_)
  show x.1.nativeWord.length + (x.1.nativeWord.length + x.1.q + 1) +
      PCJ6e421fabe2aa4155_SourcePoolCapacity.value x.1.nativeWord.length x.1.q ≤ _
  unfold PCJ6e421fabe2aa4155_SourcePoolCapacity.value
  omega

theorem wordsCost_sb_poly (mask : MaskProducer) :
    ∃ wC wE : ℕ, ∀ (r : Request) (MB : List Bool),
      Words.wordsCost mask (NearCubicWires.SourceStart.Bank.sb a) r MB ≤ wC * (Yb a (r, MB)) ^ wE :=
  wordsCost_poly a (NearCubicWires.SourceStart.Bank.sb a) mask (sb_cost a) (sb_sizes a)

def wC (mask : MaskProducer) : ℕ := Classical.choose (wordsCost_sb_poly a mask)

def wE (mask : MaskProducer) : ℕ := Classical.choose (Classical.choose_spec (wordsCost_sb_poly a mask))

end sb

end
end NearCubicWires.SourceFactorSel.WordsCost

