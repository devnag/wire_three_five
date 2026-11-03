import Proof.Packets.PacketsMetaStageRun

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.PacketsMeta.CutoffMath
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

namespace Stage
open Lev Setup Tail Prog Spec Bounds StageRun

/-- The THR program cost. -/
def thrPC (W : ℕ) (nw tw : List Bool) (ds : List CD) (nT : ℕ) : ℕ :=
  hdrCost nw tw W + 1 + ((2 * W + 3) + (((2 * W + 3) + 1 + (2 * W + 3)) + 0 + thrCost W ds nT + 2) + 0 + 2)

/-- The `|Sel|` tail's cost. -/
def selTailCost (W C : ℕ) : ℕ := (2 * W + 3) + 1 + (C + 1) * ((2 * W + 3) + ((2 * W + 3) + 1 + 1) + 2)

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : ℕ)

theorem thr_cut :
    LRuns (thrW a r four L target) (prog tailM)
      (thrPC (thrW a r four L target) (Request.nativeWord (.thr r four L target)) (twOf (dsOf a r)) (dsOf a r)
        (tailCost (thrW a r four L target) (Fv (dsOf a r)) (Cv (dsOf a r)) target))
      (σ0 (Request.nativeWord (.thr r four L target)) (twOf (dsOf a r)))
      (outOnly (cutOf (Fv (dsOf a r)) (Cv (dsOf a r)) target)) := by
  obtain ⟨h2, h5, hq, hL, ht, hR, hfit, hFm, hCm, hF, hT, hcut⟩ := thr_width a r four L target
  exact prog_thr _ (restOf r) r.q L target (nw_eq r four L target) (dsOf a r) (thrW a r four L target) rfl h2 hq hL ht
    (twOf (dsOf a r)).length hR hfit (rec_bound a r four L target) hFm hCm tailM _ _ _
    (fun b => tail_run (Fv (dsOf a r)) (Cv (dsOf a r)) target b h5 hF hT hcut) rfl

theorem thr_sel :
    LRuns (thrW a r four L target) (prog selTailM)
      (thrPC (thrW a r four L target) (Request.nativeWord (.thr r four L target)) (twOf (dsOf a r)) (dsOf a r)
        (selTailCost (thrW a r four L target) (Cv (dsOf a r))))
      (σ0 (Request.nativeWord (.thr r four L target)) (twOf (dsOf a r))) (outOnly (Cv (dsOf a r))) := by
  obtain ⟨h2, _, hq, hL, ht, hR, hfit, hFm, hCm, _, _, _⟩ := thr_width a r four L target
  exact prog_thr _ (restOf r) r.q L target (nw_eq r four L target) (dsOf a r) (thrW a r four L target) rfl h2 hq hL ht
    (twOf (dsOf a r)).length hR hfit (rec_bound a r four L target) hFm hCm selTailM _ _ _
    (fun b => selTail_run (Fv (dsOf a r)) (Cv (dsOf a r)) target b hCm) rfl

end Thr

/-! ## The other kinds -/

/-- The width of a request's two fields. -/
def reqW (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  32 * ((Request.nativeWord r).length + (Request.topWord a r).length)

theorem thrW_eq (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) : thrW a r four L target = reqW a (.thr r four L target) := by
  unfold thrW reqW
  rw [tw_eq a r four L target]

/-- **The program's step count per request.** -/
def pc {sT : ℕ} (a : DecompositionAlgorithm) (tailOf : ℕ → ℕ → ℕ → ℕ → ℕ) (_ : Machine 17 sT) : Request → ℕ
  | .terminal => hdrCost (Request.nativeWord .terminal) (Request.topWord a .terminal) (reqW a .terminal) + 1 +
      ((2 * reqW a .terminal + 3) + (((2 * reqW a .terminal + 3) + 1 + (2 * reqW a .terminal + 3)) + 0 + 0 + 2) + 0 + 2)
  | .sym r four L target => hdrCost (Request.nativeWord (.sym r four L target)) (Request.topWord a (.sym r four L target))
      (reqW a (.sym r four L target)) + 1 + ((2 * reqW a (.sym r four L target) + 3) + 0 + 0 + 2)
  | .thr r four L target => thrPC (thrW a r four L target) (Request.nativeWord (.thr r four L target))
      (twOf (dsOf a r)) (dsOf a r) (tailOf (thrW a r four L target) (Fv (dsOf a r)) (Cv (dsOf a r)) target)

theorem term_run {sT : ℕ} (a : DecompositionAlgorithm) (Tm : Machine 17 sT) :
    LRuns (reqW a .terminal) (prog Tm)
      (hdrCost (Request.nativeWord .terminal) (Request.topWord a .terminal) (reqW a .terminal) + 1 +
        ((2 * reqW a .terminal + 3) + (((2 * reqW a .terminal + 3) + 1 + (2 * reqW a .terminal + 3)) + 0 + 0 + 2) + 0 + 2))
      (σ0 (Request.nativeWord .terminal) (Request.topWord a .terminal)) (outOnly 0) := by
  have e3 : 1 ≤ (natWord 2).length := by
    rw [ReadNat.natWord_length]
    omega
  refine prog_term Tm _ _ (by simp [Request.nativeWord]) _ rfl ?_
  unfold reqW
  simp only [Request.nativeWord]
  omega

theorem sym_run {sT : ℕ} (a : DecompositionAlgorithm) (Tm : Machine 17 sT)
    (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r.circuits.length ≤ 4) (L target : ℕ) :
    LRuns (reqW a (.sym r four L target)) (prog Tm)
      (hdrCost (Request.nativeWord (.sym r four L target)) (Request.topWord a (.sym r four L target))
        (reqW a (.sym r four L target)) + 1 + ((2 * reqW a (.sym r four L target) + 3) + 0 + 0 + 2))
      (σ0 (Request.nativeWord (.sym r four L target)) (Request.topWord a (.sym r four L target))) (outOnly 0) := by
  have hnw : Request.nativeWord (.sym r four L target) = natWord 0 ++ (natWord r.q ++ natWord L ++ natWord target ++
      natWord r.circuits.length ++ r.circuits.flatMap (fun c => RepairOrdinary.frame (symWord c))) := by
    simp only [Request.nativeWord, List.append_assoc]
  have e0 : (natWord 0).length = 3 := by
    rw [ReadNat.natWord_length]
    simp [natBitLength]
  refine prog_sym Tm _ _ _ hnw _ rfl ?_
  unfold reqW
  rw [hnw]
  simp only [List.length_append, e0]
  omega

end Stage

end
end NearCubicWires.PacketsMeta

