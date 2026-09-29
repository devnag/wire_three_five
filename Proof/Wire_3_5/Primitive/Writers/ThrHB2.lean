import Proof.Wire_3_5.Primitive.Writers.ThrHB1

/-! # c4 THR block, the hash bits' program, run (`hbX_spec`)

From the cell's entry at the THR input word `reqW n true codes cc (natListWord tr ++ hbF)`: stream `121` holds
`marks hbF`, stream `0` is kept.

Paper quantity of the main type: the framed hash bits `hbF = frame hb` of the THR input word (P3:2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrHB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable (cap : ℕ)

/-- The hash bits' program's step bound. -/
def hbXCost (n a c Kb t hl L : ℕ) : ℕ :=
  (20 * natBitLength n + 20) + 1 + (1 + 1 + (1 + 1 + ((natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40) + 1 +
    ((a * (20 * Kb + 20 + 4) + 1) + 1 + ((natBitLength c + 2) * (40 * 2 ^ natBitLength c + 40) + 1 +
    ((c * (20 * Kb + 20 + 4) + 1) + 1 + (((t + 12) * (300 * t + 300) + 64 * L + 64) + 1 + (22 * hl + 1))))))))

/-- **The hash bits' program, run.** -/
theorem hbX_spec (n : ℕ) (codes cc tr : List ℕ) (hbF : List Bool) (Kb : ℕ) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb)
    (hKc : ∀ c ∈ cc, natBitLength c ≤ Kb) (c1 : natBitLength n + 1 ≤ cap)
    (c2 : 2 ^ (natBitLength codes.length + 1) ≤ cap) (c3 : 2 ^ (natBitLength cc.length + 1) ≤ cap)
    (c4 : Kb + 1 ≤ cap) (c5 : codes.length ≤ cap) (c6 : cc.length ≤ cap)
    (c7 : 8 * tr.length + 2 * (RepairRepresentation.natListWord tr).length + 16 ≤ cap)
    (c8 : 2 * hbF.length + 2 ≤ cap) :
    ∃ τ, WExec cap hbXW
        (CellLoopD.blankCellD 0 (Data.reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF)) [] 0 []) τ
        (hbXCost n codes.length cc.length Kb tr.length hbF.length (RepairRepresentation.natListWord tr).length) ∧
      τ.st sZ = marks hbF ∧
      τ.st (sk 0 0) = frame (Data.reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF)) ∧
      τ.cell = false := by
  set w := Data.reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF) with hwd
  set σ0 := CellLoopD.blankCellD 0 w [] 0 [] with hσ0
  have n0B : (sk 0 0 : Fin (LNS 0 + 1)) ≠ sk 0 113 := fun e => absurd (sk_inj 0 e) (by decide)
  have nD0 : (sD : Fin (LNS 0 + 1)) ≠ sk 0 0 := fun e => absurd (sk_inj 0 e) (by decide)
  have nD1 : (sD : Fin (LNS 0 + 1)) ≠ sk 0 1 := fun e => absurd (sk_inj 0 e) (by decide)
  have nD2 : (sD : Fin (LNS 0 + 1)) ≠ sk 0 2 := fun e => absurd (sk_inj 0 e) (by decide)
  have nDB : (sD : Fin (LNS 0 + 1)) ≠ sk 0 113 := fun e => absurd (sk_inj 0 e) (by decide)
  have nZ0 : (sZ : Fin (LNS 0 + 1)) ≠ sk 0 0 := fun e => absurd (sk_inj 0 e) (by decide)
  have nZ1 : (sZ : Fin (LNS 0 + 1)) ≠ sk 0 1 := fun e => absurd (sk_inj 0 e) (by decide)
  have nZ2 : (sZ : Fin (LNS 0 + 1)) ≠ sk 0 2 := fun e => absurd (sk_inj 0 e) (by decide)
  have nZB : (sZ : Fin (LNS 0 + 1)) ≠ sk 0 113 := fun e => absurd (sk_inj 0 e) (by decide)
  have nZD : (sZ : Fin (LNS 0 + 1)) ≠ sD := fun e => absurd (sk_inj 0 e) (by decide)
  have n01 : (sk 0 0 : Fin (LNS 0 + 1)) ≠ sk 0 1 := fun e => absurd (sk_inj 0 e) (by decide)
  have st00 : σ0.st (sk 0 0) = frame w := by simp [hσ0, CellLoopD.blankCellD, blankCell, n0B]
  have sh00 : σ0.sh (sk 0 0) = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, n01]
  have stD : σ0.st sD = [] := by simp [hσ0, CellLoopD.blankCellD, blankCell, nD0, nD1, nD2, nDB]
  have shD : σ0.sh sD = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, nD1]
  have stZ : σ0.st sZ = [] := by simp [hσ0, CellLoopD.blankCellD, blankCell, nZ0, nZ1, nZ2, nZB]
  have shZ : σ0.sh sZ = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, nZ1]
  have z0 : ∀ r, σ0.val r = 0 := fun r => by simp [hσ0, CellLoopD.blankCellD, blankCell]
  have cl0 : σ0.cell = false := by simp [hσ0, CellLoopD.blankCellD, blankCell]
  have hw := Data.enc_reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF)
  rw [CopyNat.enc_append] at hw
  rw [← hwd] at hw
  have eL : ∀ l : List Bool, (enc true l).length = 2 * l.length := fun l => by rw [ParseNat.enc_length]; rfl
  -- 1: skip `n`
  have e1 := skipNatM_spec cap true (sk 0 0) dF dC (by decide) n []
    (enc true [true] ++ (enc true (RepairRepresentation.natWord codes.length) ++
      (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
        (enc true (cc.flatMap RepairRepresentation.natWord) ++
          ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false]))))))
    σ0 (by rw [st00, hw]; rfl) (by rw [sh00]; rfl) (z0 _) (z0 _) c1
  obtain ⟨σ1, g1⟩ : ∃ y, y = σ0.seth (sk 0 0) (([] : List Bool).length + stp true *
      (RepairRepresentation.natWord n).length) := ⟨_, rfl⟩
  rw [← g1] at e1
  -- 2, 3: the mode bit
  have e2 := WExec.fwd (cap := cap) (sk 0 0) σ1
  obtain ⟨σ2, g2⟩ : ∃ y, y = σ1.seth (sk 0 0) (σ1.sh (sk 0 0) + 1) := ⟨_, rfl⟩
  rw [← g2] at e2
  have e3 := WExec.fwd (cap := cap) (sk 0 0) σ2
  obtain ⟨σ3, g3⟩ : ∃ y, y = σ2.seth (sk 0 0) (σ2.sh (sk 0 0) + 1) := ⟨_, rfl⟩
  rw [← g3] at e3
  have v3 : σ3.val = σ0.val := by rw [g3, g2, g1]; rfl
  have s3 : σ3.st = σ0.st := by rw [g3, g2, g1]; rfl
  have p3 : σ3.sh (sk 0 0) = (enc true (RepairRepresentation.natWord n) ++ enc true [true]).length := by
    rw [g3, g2, g1]; simp [eL, stp] <;> omega
  -- 4: `|codes|` into `dK`
  have e4 := readNatM_spec cap true (sk 0 0) dF dC dK dP dT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) codes.length
    (enc true (RepairRepresentation.natWord n) ++ enc true [true])
    (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
        (enc true (cc.flatMap RepairRepresentation.natWord) ++
          ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false]))))
    σ3 (by rw [s3, st00, hw]; simp only [List.append_assoc]) p3
    (by rw [v3, z0]) (by rw [v3, z0]) (by rw [v3, z0]) (by rw [v3, z0]) (by rw [v3, z0]; omega)
  obtain ⟨σ4, g4⟩ : ∃ y, y = (σ3.seth (sk 0 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [true]).length +
      stp true * (RepairRepresentation.natWord codes.length).length)).setv dK (σ3.val dK + codes.length) := ⟨_, rfl⟩
  rw [← g4] at e4
  have s4 : σ4.st = σ0.st := by rw [g4, ← s3]; rfl
  have k4 : ∀ r, r ≠ dK → σ4.val r = 0 := fun r hr => by rw [g4]; simp [Function.update_of_ne hr, v3, z0]
  have vK4 : σ4.val dK = codes.length := by rw [g4]; simp [v3, z0]
  -- 5: skip the codes
  have e5 := skipCodes_spec cap 0 codes
    (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++ enc true (RepairRepresentation.natWord codes.length))
    (enc true (RepairRepresentation.natWord cc.length) ++ (enc true (cc.flatMap RepairRepresentation.natWord) ++
      ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false])))
    Kb hKb σ4 (by rw [s4, st00, hw]; simp only [List.append_assoc])
    (by rw [g4]; simp [eL, stp] <;> omega) vK4 (k4 _ (by decide)) (k4 _ (by decide)) c4 c5
  obtain ⟨σ5, g5⟩ : ∃ y, y = (σ4.seth (sk 0 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length)).length +
      (enc true (codes.flatMap RepairRepresentation.natWord)).length)).setv dK 0 := ⟨_, rfl⟩
  rw [← g5] at e5
  have s5 : σ5.st = σ0.st := by rw [g5, ← s4]; rfl
  have z5 : ∀ r, σ5.val r = 0 := fun r => by
    rw [g5]
    by_cases hr : r = dK
    · subst hr; simp
    · simp [Function.update_of_ne hr, k4 r hr]
  -- 6: `|cc|` into `dK`
  have e6 := readNatM_spec cap true (sk 0 0) dF dC dK dP dT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) cc.length
    (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++ enc true (RepairRepresentation.natWord codes.length) ++
      enc true (codes.flatMap RepairRepresentation.natWord))
    (enc true (cc.flatMap RepairRepresentation.natWord) ++
      ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false]))
    σ5 (by rw [s5, st00, hw]; simp only [List.append_assoc]) (by rw [g5]; simp [eL, stp] <;> omega)
    (z5 _) (z5 _) (z5 _) (z5 _) (by rw [z5]; omega)
  obtain ⟨σ6, g6⟩ : ∃ y, y = (σ5.seth (sk 0 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord)).length +
      stp true * (RepairRepresentation.natWord cc.length).length)).setv dK (σ5.val dK + cc.length) := ⟨_, rfl⟩
  rw [← g6] at e6
  have s6 : σ6.st = σ0.st := by rw [g6, ← s5]; rfl
  have k6 : ∀ r, r ≠ dK → σ6.val r = 0 := fun r hr => by rw [g6]; simp [Function.update_of_ne hr, z5]
  have vK6 : σ6.val dK = cc.length := by rw [g6]; simp [z5]
  -- 7: skip the carriers' codes
  have e7 := skipCodes_spec cap 0 cc
    (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++ enc true (RepairRepresentation.natWord codes.length) ++
      enc true (codes.flatMap RepairRepresentation.natWord) ++ enc true (RepairRepresentation.natWord cc.length))
    ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false])
    Kb hKc σ6 (by rw [s6, st00, hw]; simp only [List.append_assoc])
    (by rw [g6]; simp [eL, stp] <;> omega) vK6 (k6 _ (by decide)) (k6 _ (by decide)) c4 c6
  obtain ⟨σ7, g7⟩ : ∃ y, y = (σ6.seth (sk 0 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord) ++
      enc true (RepairRepresentation.natWord cc.length)).length +
      (enc true (cc.flatMap RepairRepresentation.natWord)).length)).setv dK 0 := ⟨_, rfl⟩
  rw [← g7] at e7
  have s7 : σ7.st = σ0.st := by rw [g7, ← s6]; rfl
  have z7 : ∀ r, σ7.val r = 0 := fun r => by
    rw [g7]
    by_cases hr : r = dK
    · subst hr; simp
    · simp [Function.update_of_ne hr, k6 r hr]
  have sh7D : σ7.sh sD = 0 := by
    rw [g7, g6, g5, g4, g3, g2, g1]; simp [Function.update_apply, nD0, shD]
  have sh7Z : σ7.sh sZ = 0 := by
    rw [g7, g6, g5, g4, g3, g2, g1]; simp [Function.update_apply, nZ0, shZ]
  have p7 : σ7.sh (sk 0 0) = (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord) ++
      enc true (RepairRepresentation.natWord cc.length) ++ enc true (cc.flatMap RepairRepresentation.natWord)).length := by
    rw [g7]; simp [eL] <;> omega
  -- 8: the translation list to the scratch stream
  have e8 := CopyNat.copyNatListM_spec cap true (sk 0 0) sD (Ne.symm nD0) hQ tr
    (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++ enc true (RepairRepresentation.natWord codes.length) ++
      enc true (codes.flatMap RepairRepresentation.natWord) ++ enc true (RepairRepresentation.natWord cc.length) ++
      enc true (cc.flatMap RepairRepresentation.natWord))
    (enc true hbF ++ [false]) σ7 (by rw [s7, st00, hw]; simp only [List.append_assoc]) p7
    (by rw [sh7D, s7, stD]; rfl) (fun i _ => z7 _) (by rw [z7]; omega)
  obtain ⟨σ8, g8⟩ : ∃ y, y = (appendO σ7 sD (hQ 7) (marks (RepairRepresentation.natListWord tr))).seth (sk 0 0)
      ((enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
        enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord) ++
        enc true (RepairRepresentation.natWord cc.length) ++ enc true (cc.flatMap RepairRepresentation.natWord)).length +
        stp true * (RepairRepresentation.natListWord tr).length) := ⟨_, rfl⟩
  rw [← g8] at e8
  -- 9: the hash bits to `sZ`
  have st8 : σ8.st (sk 0 0) = (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord) ++
      enc true (RepairRepresentation.natWord cc.length) ++ enc true (cc.flatMap RepairRepresentation.natWord) ++
      enc true (RepairRepresentation.natListWord tr)) ++ enc true hbF ++ [false] := by
    rw [g8]; simp only [WState.seth_st, appendO_st, Function.update_apply, if_neg (Ne.symm nD0)]
    rw [s7, st00, hw]; simp only [List.append_assoc]
  have e9 := cpl_spec cap hbF σ8 _ st8 (by rw [g8]; simp [eL, stp] <;> omega)
    (by rw [g8]; simp [Function.update_apply, nZ0, nZD, sh7Z, s7, stZ])
    (by rw [g8]; simp [Function.update_apply, show hOP ≠ hQ 7 by decide, z7] <;> omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) (by unfold hbXCost; omega), ?_, ?_, ?_⟩
  · simp [Function.update_apply, g8, nZD, s7, stZ]
  · simp [Function.update_apply, g8, Ne.symm nZ0, Ne.symm nD0, s7, st00]
  · simp [g8, g7, g6, g5, g4, g3, g2, g1, cl0]

end NearCubicWires.WireExponent3_5.PrimAsm.ThrHB
