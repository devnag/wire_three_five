import Proof.Wire_3_5.FinalPass.S5TW6
import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Cost
import Proof.Wire_3_5.Primitive.Writers.ThrData2

/-! # S5-THR, part 9: the THR front end and the data stage docked (P3:2543-2558, P3:3083-3086)

* the THR front end `topFront3` (`TopFrontPort3`) docked by `tfMap`: port `0` on the input, port `1` on `1^V`, the
  payloads' ports `2 … 5` on slots `9 … 12`; **`tf_dock`**.
* PA's data stage `thrDataStage2` (`ThrDataStage2`) docked by `tdMap`: its request on the input, its counts `1^n`,
  `1^L`, `1^W` on its block's tapes `2`, `3`, `4`, its tuple table `tabS` on slot `8`; **`td_dock`**.

Paper quantities of the main types: the circuits' payloads (`payOf`), the tuple's gate table (`gatesW`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (dockS updS)
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2InPorts tf2OutPorts TF2Ok)

variable (D x6 xt : ℕ) (cap : ℕ)

/-! ## The front end -/

theorem tf_in (σ : WState (nsL D x6 xt) nrL) (w : List Bool) (V : ℕ)
    (hIn : σ.st (tfMap D x6 xt ⟨0, by omega⟩) = frame w)
    (h1 : σ.st (tfMap D x6 xt ⟨1, by omega⟩) = List.replicate V true)
    (hblk : ∀ j : Fin (10 + xt), j.val ≠ 0 → j.val ≠ 1 → σ.st (tfMap D x6 xt j) = []) :
    (fun j : Fin (10 + xt) => σ.st (tfMap D x6 xt j)) =
      Fin.addCases (m := 10) (n := xt) (motive := fun _ => List Bool) (tf2InPorts w V) (fun _ => []) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · rw [Fin.addCases_left]
    unfold tf2InPorts
    have hi := i.isLt
    by_cases a0 : i.val = 0
    · have : (Fin.castAdd xt i : Fin (10 + xt)) = ⟨0, by omega⟩ := Fin.ext a0
      rw [this, hIn]; simp [a0]
    by_cases a1 : i.val = 1
    · have : (Fin.castAdd xt i : Fin (10 + xt)) = ⟨1, by omega⟩ := Fin.ext a1
      rw [this, h1]; simp [a1]
    rw [hblk _ (by simpa using a0) (by simpa using a1)]
    simp [a0, a1]
  · rw [Fin.addCases_right]
    exact hblk _ (by simp) (by simp; omega)

theorem tf_dock (alg : RepairRepresentation.DecompositionAlgorithm)
    (σ : WState (nsL D x6 (PrimThrW.TF3Cost.topFront3 alg).x) nrL) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (codes : List ℕ) (tl : List Bool) (V : ℕ)
    (hIn : σ.st (tfMap D x6 _ ⟨0, by omega⟩) = frame (PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs) codes tl))
    (h1 : σ.st (tfMap D x6 _ ⟨1, by omega⟩) = List.replicate V true)
    (hblk : ∀ j : Fin (10 + (PrimThrW.TF3Cost.topFront3 alg).x), j.val ≠ 0 → j.val ≠ 1 →
      σ.st (tfMap D x6 _ j) = [])
    (hsh : ∀ i, σ.sh i = 0) (hn : 1 ≤ n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26)
    (hok : TF2Ok Cs codes V) :
    ∃ J : Fin (PrimThrW.TF3Cost.topFront3 alg).x → List Bool,
      (∀ j, (J j).length ≤ (PrimThrW.TF3Cost.topFront3 alg).cost V) ∧
      Step (RecoveryFocus.machine (fun j => sTape (nr := nrL) (tfMap D x6 _ j)) (PrimThrW.TF3Cost.topFront3 alg).M)
        ((PrimThrW.TF3Cost.topFront3 alg).cost V) (wenc cap σ).H (wenc cap σ).A
        (wenc cap (updS (tfMap D x6 _) σ (fun _ => 0) (Fin.addCases (m := 10) (n := (PrimThrW.TF3Cost.topFront3 alg).x)
          (motive := fun _ => List Bool) (tf2OutPorts alg (PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs)
            codes tl) V Cs) J))).H
        (wenc cap (updS (tfMap D x6 _) σ (fun _ => 0) (Fin.addCases (m := 10) (n := (PrimThrW.TF3Cost.topFront3 alg).x)
          (motive := fun _ => List Bool) (tf2OutPorts alg (PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs)
            codes tl) V Cs) J))).A := by
  obtain ⟨J, hJ, hs⟩ := (PrimThrW.TF3Cost.topFront3 alg).run Cs codes tl V hn ha hd hok
  refine ⟨J, hJ, dockS cap (tfMap D x6 _) (tfMap_inj D x6 _) σ ?_⟩
  refine hs.congr_in ?_ ?_
  · funext j; exact (hsh _).symm
  · exact (tf_in D x6 _ σ _ V hIn h1 hblk).symm

/-! ## The data stage -/

theorem td_in (σ : WState (nsL D x6 xt) nrL) (w : List Bool) (n L W : ℕ)
    (hIn : σ.st (tdMap D x6 xt ⟨0, by decide⟩) = frame w)
    (h2 : σ.st (tdMap D x6 xt ⟨2, by decide⟩) = List.replicate n true)
    (h3 : σ.st (tdMap D x6 xt ⟨3, by decide⟩) = List.replicate L true)
    (h4 : σ.st (tdMap D x6 xt ⟨4, by decide⟩) = List.replicate W true)
    (hblk : ∀ j : Fin TDT, j.val ≠ 0 → j.val ≠ 2 → j.val ≠ 3 → j.val ≠ 4 → σ.st (tdMap D x6 xt j) = []) :
    (fun j : Fin (PrimAsm.Data.DS + 2 + PrimAsm.Data.DR + 1) => σ.st (tdMap D x6 xt j)) =
      Fin.addCases (m := PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) (n := 1) (motive := fun _ => List Bool)
        (PrimAsm.Data.rawIn w n L W) (fun _ : Fin 1 => List.replicate 0 false) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · rw [Fin.addCases_left]
    unfold PrimAsm.Data.rawIn
    have e0 : sTape (nr := PrimAsm.Data.DR) PrimAsm.Data.sIN = ⟨0, by decide⟩ := rfl
    have e2 : sTape (nr := PrimAsm.Data.DR) PrimAsm.Data.sNT = ⟨2, by decide⟩ := rfl
    have e3 : sTape (nr := PrimAsm.Data.DR) PrimAsm.Data.sLT = ⟨3, by decide⟩ := rfl
    have e4 : sTape (nr := PrimAsm.Data.DR) PrimAsm.Data.sCT = ⟨4, by decide⟩ := rfl
    rw [e0, e2, e3, e4]
    by_cases a0 : i.val = 0
    · rw [if_pos (Fin.ext a0)]
      have : (Fin.castAdd 1 i : Fin TDT) = ⟨0, by decide⟩ := Fin.ext a0
      rw [this, hIn]
    rw [if_neg (fun h => a0 (congrArg Fin.val h))]
    by_cases a2 : i.val = 2
    · rw [if_pos (Fin.ext a2)]
      have : (Fin.castAdd 1 i : Fin TDT) = ⟨2, by decide⟩ := Fin.ext a2
      rw [this, h2]
    rw [if_neg (fun h => a2 (congrArg Fin.val h))]
    by_cases a3 : i.val = 3
    · rw [if_pos (Fin.ext a3)]
      have : (Fin.castAdd 1 i : Fin TDT) = ⟨3, by decide⟩ := Fin.ext a3
      rw [this, h3]
    rw [if_neg (fun h => a3 (congrArg Fin.val h))]
    by_cases a4 : i.val = 4
    · rw [if_pos (Fin.ext a4)]
      have : (Fin.castAdd 1 i : Fin TDT) = ⟨4, by decide⟩ := Fin.ext a4
      rw [this, h4]
    rw [if_neg (fun h => a4 (congrArg Fin.val h))]
    exact hblk _ (by simpa using a0) (by simpa using a2) (by simpa using a3) (by simpa using a4)
  · rw [Fin.addCases_right]
    exact hblk _ (by simp [PrimAsm.Data.DS, PrimAsm.Data.DR]) (by simp [PrimAsm.Data.DS, PrimAsm.Data.DR])
      (by simp [PrimAsm.Data.DS, PrimAsm.Data.DR]) (by simp [PrimAsm.Data.DS, PrimAsm.Data.DR])

theorem td_dock (σ : WState (nsL D x6 xt) nrL) (w : List Bool) (n L W : ℕ)
    (hIn : σ.st (tdMap D x6 xt ⟨0, by decide⟩) = frame w)
    (h2 : σ.st (tdMap D x6 xt ⟨2, by decide⟩) = List.replicate n true)
    (h3 : σ.st (tdMap D x6 xt ⟨3, by decide⟩) = List.replicate L true)
    (h4 : σ.st (tdMap D x6 xt ⟨4, by decide⟩) = List.replicate W true)
    (hblk : ∀ j : Fin TDT, j.val ≠ 0 → j.val ≠ 2 → j.val ≠ 3 → j.val ≠ 4 → σ.st (tdMap D x6 xt j) = [])
    (hsh : ∀ i, σ.sh i = 0) {c m : ℕ} {tout : Fin (PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) → List Bool}
    (hs : Step PrimAsm.ThrData.thrDataStage2.M c (fun _ => 0)
      (Fin.addCases (m := PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) (n := 1) (motive := fun _ => List Bool)
        (PrimAsm.Data.rawIn w n L W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => 0)
      (Fin.addCases (m := PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) (n := 1) (motive := fun _ => List Bool) tout
        (fun _ : Fin 1 => List.replicate m false))) :
    Step (RecoveryFocus.machine (fun j => sTape (nr := nrL) (tdMap D x6 xt j)) PrimAsm.ThrData.thrDataStage2.M) c
      (wenc cap σ).H (wenc cap σ).A
      (wenc cap (updS (tdMap D x6 xt) σ (fun _ => 0) (Fin.addCases (m := PrimAsm.Data.DS + 2 + PrimAsm.Data.DR)
        (n := 1) (motive := fun _ => List Bool) tout (fun _ : Fin 1 => List.replicate m false)))).H
      (wenc cap (updS (tdMap D x6 xt) σ (fun _ => 0) (Fin.addCases (m := PrimAsm.Data.DS + 2 + PrimAsm.Data.DR)
        (n := 1) (motive := fun _ => List Bool) tout (fun _ : Fin 1 => List.replicate m false)))).A := by
  refine dockS cap (tdMap D x6 xt) (tdMap_inj D x6 xt) σ ?_
  refine hs.congr_in ?_ ?_
  · funext j; exact (hsh _).symm
  · exact (td_in D x6 xt σ w n L W hIn h2 h3 h4 hblk).symm

end NearCubicWires.WireExponent3_5.FinalPass.S5T
