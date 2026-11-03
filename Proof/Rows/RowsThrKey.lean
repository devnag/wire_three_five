import Proof.CaseAnalysis.CaseTwoBinaryField
import Proof.CaseAnalysis.FinalCompareDockLit
import Proof.MachineModel.ClockUnaryProduct
import Proof.PCP.ProjectionNormalizationDriverAtoms
import Proof.Packets.PacketsPrimeService
import Proof.Rows.CountFlags
import Proof.Rows.RowsKeyTop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrKey
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.LexSucc NearCubicWires.RepairOrdinary.RecoveryRootRound
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeySucc RowsConstruction.KeyTop
noncomputable section

/-! ## 0. Ports of the prime stage (generic in `NI`) -/

section Ports
variable (NI : Nat)

theorem initPort_val (i : Fin NI) : (initPort NI i).val = 2 + i.val := by
  simp [initPort]

theorem initPort_ne_master (i : Fin NI) (k : Fin 254) : initPort NI i ≠ masterPort NI k := by
  intro h
  have := congrArg Fin.val h
  rw [initPort_val, masterPort_val] at this
  have := i.isLt
  omega

theorem master_ne (i k : Fin 254) (h : i ≠ k) : masterPort NI i ≠ masterPort NI k := by
  intro e
  have := congrArg Fin.val e
  rw [masterPort_val, masterPort_val] at this
  exact h (Fin.ext (by omega))

theorem cell_ne_master (c : Fin 257) (k : Fin 254) : cellPort NI c ≠ masterPort NI k := by
  intro h
  have := congrArg Fin.val h
  rw [cellPort_val, masterPort_val] at this
  have := c.isLt
  omega

theorem wdock {t s n : Nat} {p : NearCubicWires.LocalBitMultitape.Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin t → Fin (2+rowsWork NI)) (hi : Function.Injective sl)
    (A : Fin (2+rowsWork NI) → List Bool) (hA : ∀ j, A (sl j) = tin j) :
    Step (RecoveryFocus.machine sl p) n (fun _ => 0) A (fun _ => 0) (install sl A tout) :=
  (h.dock sl hi _ A (fun _ => rfl) hA).congr
    (NearCubicWires.ExtDecompositionBatch.dockH_existing _ _ _ (fun _ => rfl)) rfl

end Ports

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-! ## 1. The prime-index level of the key successor -/

/-! ## 2. Masters of two keys with the same selection -/

theorem masters_at (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) (i : Fin 254) (hi : i ≠ 109) :
    thrMasters a r four L target R k i = keyPad thrKeySet R i
      (PCJ45bee56da9f34d5a_ThresholdTraversal.input a r four k.selection (thrLive r L) (fun _ => false)
        k.prime k.residue (RowsConstruction.ThrWidth.T a r four L target) L target (wT a r four L target)
        (Ff r.q (RowsConstruction.ThrWidth.T a r four L target)) (Uf r.q (RowsConstruction.ThrWidth.T a r four L target))
        (RowsConstruction.ThrWidth.T a r four L target) i) := by
  unfold thrMasters
  rw [if_neg hi]

/-! ## 3. Case P at the bank -/

variable (NI : Nat) (pub : Fin 2 → List Bool) (init : Fin NI → List Bool) (rcp : Fin 64 → List Bool) (C cC hF : Nat)

/-! ## 4. The prime stage docked on the work block -/

/-! ## 5. The prime-level machine on the both-carry bank -/

theorem cut_ge : 2 ≤ cut a r target := by
  have h : 563 ≤ CloseoutFinalC10ThresholdRows.primeCutoff a r target := by
    unfold CloseoutFinalC10ThresholdRows.primeCutoff
    exact canonicalPrimeCutoff_ge_563 _ _
  exact le_trans (by decide) h

end Thr

end
end RowsConstruction.ThrKey
