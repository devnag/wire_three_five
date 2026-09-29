import Proof.Wire_3_5.Primitive.Writers.ThrStrip4

/-! # c4 THR block, the request's strip, part 5: **`stripW_spec`**

From the cell's entry on the THR writer's input `w = reqW n true codes cc (natListWord tr ++ hbF)`, the strip program
leaves `frame (reqW n true codes cc (natListWord tr))` on `sY`, within `hbXW`'s bound plus `60·|w| + 20` steps.

Paper quantity of the main type: the THR request's word read off the THR input. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ThrHB
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable (cap : ℕ)

theorem hQ_ne (i : Fin 9) : hQ i ≠ rA ∧ hQ i ≠ rE := by
  constructor <;> intro h <;> have := congrArg Fin.val h <;> rw [hQ_val] at this <;> simp [rA, rE] at this <;> omega

/-- **The strip program's run.** -/
theorem stripW_spec (n : ℕ) (codes cc tr : List ℕ) (hbF : List Bool) (Kb : ℕ) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb)
    (hKc : ∀ c ∈ cc, natBitLength c ≤ Kb) (c1 : natBitLength n + 1 ≤ cap)
    (c2 : 2 ^ (natBitLength codes.length + 1) ≤ cap) (c3 : 2 ^ (natBitLength cc.length + 1) ≤ cap)
    (c4 : Kb + 1 ≤ cap) (c5 : codes.length ≤ cap) (c6 : cc.length ≤ cap)
    (c7 : 8 * tr.length + 2 * (RepairRepresentation.natListWord tr).length + 16 ≤ cap)
    (cw : (Data.reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF)).length ≤ cap) :
    ∃ (τ : WState (LNS 0) LNR) (c : ℕ), WExec cap stripW
        (CellLoopD.blankCellD 0 (Data.reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF)) [] 0 []) τ c ∧
      c ≤ hbXCost n codes.length cc.length Kb tr.length hbF.length (RepairRepresentation.natListWord tr).length +
        60 * (Data.reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF)).length + 20 ∧
      τ.st sY = frame (Data.reqW n true codes cc (RepairRepresentation.natListWord tr)) ∧
      τ.st (sk 0 0) = frame (Data.reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF)) := by
  set w := Data.reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF) with hwd
  set p := Data.reqW n true codes cc (RepairRepresentation.natListWord tr) with hpd
  have hwp : w = p ++ hbF := by rw [hwd, hpd]; unfold Data.reqW; simp [List.append_assoc]
  have hlen : w.length = p.length + hbF.length := by rw [hwp, List.length_append]
  set σ0 := CellLoopD.blankCellD 0 w [] 0 [] with hσ0
  have n0B : (sk 0 0 : Fin (LNS 0 + 1)) ≠ sk 0 113 := fun e => absurd (sk_inj 0 e) (by decide)
  have nD0 : (sD : Fin (LNS 0 + 1)) ≠ sk 0 0 := fun e => absurd (sk_inj 0 e) (by decide)
  have nD1 : (sD : Fin (LNS 0 + 1)) ≠ sk 0 1 := fun e => absurd (sk_inj 0 e) (by decide)
  have nD2 : (sD : Fin (LNS 0 + 1)) ≠ sk 0 2 := fun e => absurd (sk_inj 0 e) (by decide)
  have nDB : (sD : Fin (LNS 0 + 1)) ≠ sk 0 113 := fun e => absurd (sk_inj 0 e) (by decide)
  have nY0 : (sY : Fin (LNS 0 + 1)) ≠ sk 0 0 := fun e => absurd (sk_inj 0 e) (by decide)
  have nY1 : (sY : Fin (LNS 0 + 1)) ≠ sk 0 1 := fun e => absurd (sk_inj 0 e) (by decide)
  have nY2 : (sY : Fin (LNS 0 + 1)) ≠ sk 0 2 := fun e => absurd (sk_inj 0 e) (by decide)
  have nYB : (sY : Fin (LNS 0 + 1)) ≠ sk 0 113 := fun e => absurd (sk_inj 0 e) (by decide)
  have nYD : (sY : Fin (LNS 0 + 1)) ≠ sD := fun e => absurd (sk_inj 0 e) (by decide)
  have n01 : (sk 0 0 : Fin (LNS 0 + 1)) ≠ sk 0 1 := fun e => absurd (sk_inj 0 e) (by decide)
  have st00 : σ0.st (sk 0 0) = frame w := by simp [hσ0, CellLoopD.blankCellD, blankCell, n0B]
  have sh00 : σ0.sh (sk 0 0) = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, n01]
  have stD : σ0.st sD = [] := by simp [hσ0, CellLoopD.blankCellD, blankCell, nD0, nD1, nD2, nDB]
  have shD : σ0.sh sD = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, nD1]
  have stY : σ0.st sY = [] := by simp [hσ0, CellLoopD.blankCellD, blankCell, nY0, nY1, nY2, nYB]
  have shY : σ0.sh sY = 0 := by simp [hσ0, CellLoopD.blankCellD, blankCell, nY1]
  have z0 : ∀ r, σ0.val r = 0 := fun r => by simp [hσ0, CellLoopD.blankCellD, blankCell]
  have hAE : rA ≠ rE := by decide
  have hAD : rA ≠ rD := by decide
  have hED : rE ≠ rD := by decide
  -- A: count the word's pairs
  have eA := cnt3W_spec cap (sk 0 0) rA rE rD hAE hAD hED w σ0 [] (by rw [st00, frame_m]; simp) (by rw [sh00]; rfl)
    (by rw [z0]; omega) (by rw [z0]; omega) (by rw [z0]; omega)
  set σA := cntS (sk 0 0) rA rE rD σ0 w.length with hσA
  -- B: rewind
  have eB := rew2W_spec cap (sk 0 0) rD w.length σA (by rw [hσA]; simp [cntS, sh00])
    (by rw [hσA]; simp [cntS, z0]) cw
  set σB := (σA.seth (sk 0 0) 0).setv rD 0 with hσB
  have Bst : σB.st = σ0.st := by rw [hσB, hσA]; simp [cntS]
  have Bsh0 : σB.sh (sk 0 0) = 0 := by rw [hσB]; simp
  have BshD : σB.sh sD = 0 := by rw [hσB, hσA]; simp [cntS, Function.update_apply, nD0, shD]
  have BshY : σB.sh sY = 0 := by rw [hσB, hσA]; simp [cntS, Function.update_apply, nY0, shY]
  have BvA : σB.val rA = w.length := by rw [hσB, hσA]; simp [cntS, Function.update_apply, hAD, hAE, z0]
  have BvE : σB.val rE = w.length := by rw [hσB, hσA]; simp [cntS, Function.update_apply, hED, z0]
  have zB : ∀ r, r ≠ rA → r ≠ rE → σB.val r = 0 := fun r h1 h2 => by
    rw [hσB, hσA]; simp only [cntS, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all
  have Bcl : σB.cell = σ0.cell := by rw [hσB, hσA]; simp [cntS]
  -- C: the request's parse (hbXW's steps 1-8 at σB)
  have hw := Data.enc_reqW n true codes cc (RepairRepresentation.natListWord tr ++ hbF)
  rw [CopyNat.enc_append] at hw
  rw [← hwd] at hw
  have eL : ∀ l : List Bool, (enc true l).length = 2 * l.length := fun l => by rw [ParseNat.enc_length]; rfl
  have st0B : σB.st (sk 0 0) = frame w := by rw [Bst, st00]
  have e1 := skipNatM_spec cap true (sk 0 0) dF dC (by decide) n []
    (enc true [true] ++ (enc true (RepairRepresentation.natWord codes.length) ++
      (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
        (enc true (cc.flatMap RepairRepresentation.natWord) ++
          ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false]))))))
    σB (by rw [st0B, hw]; rfl) (by rw [Bsh0]; rfl) (zB _ (by decide) (by decide)) (zB _ (by decide) (by decide)) c1
  obtain ⟨σ1, g1⟩ : ∃ y, y = σB.seth (sk 0 0) (([] : List Bool).length + stp true *
      (RepairRepresentation.natWord n).length) := ⟨_, rfl⟩
  rw [← g1] at e1
  have e2 := WExec.fwd (cap := cap) (sk 0 0) σ1
  obtain ⟨σ2, g2⟩ : ∃ y, y = σ1.seth (sk 0 0) (σ1.sh (sk 0 0) + 1) := ⟨_, rfl⟩
  rw [← g2] at e2
  have e3 := WExec.fwd (cap := cap) (sk 0 0) σ2
  obtain ⟨σ3, g3⟩ : ∃ y, y = σ2.seth (sk 0 0) (σ2.sh (sk 0 0) + 1) := ⟨_, rfl⟩
  rw [← g3] at e3
  have v3 : σ3.val = σB.val := by rw [g3, g2, g1]; rfl
  have s3 : σ3.st = σB.st := by rw [g3, g2, g1]; rfl
  have p3 : σ3.sh (sk 0 0) = (enc true (RepairRepresentation.natWord n) ++ enc true [true]).length := by
    rw [g3, g2, g1]; simp [eL, stp] <;> omega
  have e4 := readNatM_spec cap true (sk 0 0) dF dC dK dP dT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) codes.length
    (enc true (RepairRepresentation.natWord n) ++ enc true [true])
    (enc true (codes.flatMap RepairRepresentation.natWord) ++ (enc true (RepairRepresentation.natWord cc.length) ++
        (enc true (cc.flatMap RepairRepresentation.natWord) ++
          ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false]))))
    σ3 (by rw [s3, st0B, hw]; simp only [List.append_assoc]) p3
    (by rw [v3]; exact zB dF (by decide) (by decide)) (by rw [v3]; exact zB dC (by decide) (by decide))
    (by rw [v3]; exact zB dP (by decide) (by decide)) (by rw [v3]; exact zB dT (by decide) (by decide))
    (by rw [v3, zB dK (by decide) (by decide)]; omega)
  obtain ⟨σ4, g4⟩ : ∃ y, y = (σ3.seth (sk 0 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [true]).length +
      stp true * (RepairRepresentation.natWord codes.length).length)).setv dK (σ3.val dK + codes.length) := ⟨_, rfl⟩
  rw [← g4] at e4
  have s4 : σ4.st = σB.st := by rw [g4, ← s3]; rfl
  have k4 : ∀ r, r ≠ dK → r ≠ rA → r ≠ rE → σ4.val r = 0 := fun r hr h1 h2 => by
    rw [g4]; simp [Function.update_of_ne hr, v3, zB r h1 h2]
  have vK4 : σ4.val dK = codes.length := by rw [g4]; simp [v3, zB dK (by decide) (by decide)]
  have e5 := skipCodes_spec cap 0 codes
    (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++ enc true (RepairRepresentation.natWord codes.length))
    (enc true (RepairRepresentation.natWord cc.length) ++ (enc true (cc.flatMap RepairRepresentation.natWord) ++
      ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false])))
    Kb hKb σ4 (by rw [s4, st0B, hw]; simp only [List.append_assoc])
    (by rw [g4]; simp [eL, stp] <;> omega) vK4 (k4 dF (by decide) (by decide) (by decide))
    (k4 dC (by decide) (by decide) (by decide)) c4 c5
  obtain ⟨σ5, g5⟩ : ∃ y, y = (σ4.seth (sk 0 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length)).length +
      (enc true (codes.flatMap RepairRepresentation.natWord)).length)).setv dK 0 := ⟨_, rfl⟩
  rw [← g5] at e5
  have s5 : σ5.st = σB.st := by rw [g5, ← s4]; rfl
  have z5 : ∀ r, r ≠ rA → r ≠ rE → σ5.val r = 0 := fun r h1 h2 => by
    rw [g5]
    by_cases hr : r = dK
    · subst hr; simp
    · simp [Function.update_of_ne hr, k4 r hr h1 h2]
  have e6 := readNatM_spec cap true (sk 0 0) dF dC dK dP dT (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) cc.length
    (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++ enc true (RepairRepresentation.natWord codes.length) ++
      enc true (codes.flatMap RepairRepresentation.natWord))
    (enc true (cc.flatMap RepairRepresentation.natWord) ++
      ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false]))
    σ5 (by rw [s5, st0B, hw]; simp only [List.append_assoc]) (by rw [g5]; simp [eL, stp] <;> omega)
    (z5 dF (by decide) (by decide)) (z5 dC (by decide) (by decide)) (z5 dP (by decide) (by decide))
    (z5 dT (by decide) (by decide)) (by rw [z5 dK (by decide) (by decide)]; omega)
  obtain ⟨σ6, g6⟩ : ∃ y, y = (σ5.seth (sk 0 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord)).length +
      stp true * (RepairRepresentation.natWord cc.length).length)).setv dK (σ5.val dK + cc.length) := ⟨_, rfl⟩
  rw [← g6] at e6
  have s6 : σ6.st = σB.st := by rw [g6, ← s5]; rfl
  have k6 : ∀ r, r ≠ dK → r ≠ rA → r ≠ rE → σ6.val r = 0 := fun r hr h1 h2 => by
    rw [g6]; simp [Function.update_of_ne hr, z5 r h1 h2]
  have vK6 : σ6.val dK = cc.length := by rw [g6]; simp [z5 dK (by decide) (by decide)]
  have e7 := skipCodes_spec cap 0 cc
    (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++ enc true (RepairRepresentation.natWord codes.length) ++
      enc true (codes.flatMap RepairRepresentation.natWord) ++ enc true (RepairRepresentation.natWord cc.length))
    ((enc true (RepairRepresentation.natListWord tr) ++ enc true hbF) ++ [false])
    Kb hKc σ6 (by rw [s6, st0B, hw]; simp only [List.append_assoc])
    (by rw [g6]; simp [eL, stp] <;> omega) vK6 (k6 dF (by decide) (by decide) (by decide))
    (k6 dC (by decide) (by decide) (by decide)) c4 c6
  obtain ⟨σ7, g7⟩ : ∃ y, y = (σ6.seth (sk 0 0) ((enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord) ++
      enc true (RepairRepresentation.natWord cc.length)).length +
      (enc true (cc.flatMap RepairRepresentation.natWord)).length)).setv dK 0 := ⟨_, rfl⟩
  rw [← g7] at e7
  have s7 : σ7.st = σB.st := by rw [g7, ← s6]; rfl
  have z7 : ∀ r, r ≠ rA → r ≠ rE → σ7.val r = 0 := fun r h1 h2 => by
    rw [g7]
    by_cases hr : r = dK
    · subst hr; simp
    · simp [Function.update_of_ne hr, k6 r hr h1 h2]
  have sh7D : σ7.sh sD = 0 := by
    rw [g7, g6, g5, g4, g3, g2, g1]; simp [Function.update_apply, nD0, BshD]
  have p7 : σ7.sh (sk 0 0) = (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
      enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord) ++
      enc true (RepairRepresentation.natWord cc.length) ++ enc true (cc.flatMap RepairRepresentation.natWord)).length := by
    rw [g7]; simp [eL] <;> omega
  have e8 := CopyNat.copyNatListM_spec cap true (sk 0 0) sD (Ne.symm nD0) hQ tr
    (enc true (RepairRepresentation.natWord n) ++ enc true [true] ++ enc true (RepairRepresentation.natWord codes.length) ++
      enc true (codes.flatMap RepairRepresentation.natWord) ++ enc true (RepairRepresentation.natWord cc.length) ++
      enc true (cc.flatMap RepairRepresentation.natWord))
    (enc true hbF ++ [false]) σ7 (by rw [s7, st0B, hw]; simp only [List.append_assoc]) p7
    (by rw [sh7D, s7, Bst, stD]; rfl) (fun i _ => z7 _ (hQ_ne i).1 (hQ_ne i).2)
    (by rw [z7 _ (hQ_ne 7).1 (hQ_ne 7).2]; omega)
  obtain ⟨σ8, g8⟩ : ∃ y, y = (appendO σ7 sD (hQ 7) (marks (RepairRepresentation.natListWord tr))).seth (sk 0 0)
      ((enc true (RepairRepresentation.natWord n) ++ enc true [true] ++
        enc true (RepairRepresentation.natWord codes.length) ++ enc true (codes.flatMap RepairRepresentation.natWord) ++
        enc true (RepairRepresentation.natWord cc.length) ++ enc true (cc.flatMap RepairRepresentation.natWord)).length +
        stp true * (RepairRepresentation.natListWord tr).length) := ⟨_, rfl⟩
  rw [← g8] at e8
  have eP : WExec cap parseW σB σ8 _ :=
    WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7 e8))))))
  -- the parse's exit
  have st8 : σ8.st (sk 0 0) = frame w := by
    rw [g8]; simp only [WState.seth_st, appendO_st, Function.update_apply, if_neg (Ne.symm nD0)]; rw [s7, st0B]
  have sh8 : σ8.sh (sk 0 0) = (marks p).length := by
    rw [g8, marks_len, hpd]; unfold Data.reqW
    simp [eL, stp, RepairRepresentation.natListWord, List.length_append]; ring
  have v8A : σ8.val rA = w.length := by
    rw [g8]; simp [Function.update_apply, (hQ_ne 7).1.symm]
    rw [g7, g6, g5, g4, g3, g2, g1]; simp [Function.update_apply, BvA, show rA ≠ dK by decide]
  have v8E : σ8.val rE = w.length := by
    rw [g8]; simp [Function.update_apply, (hQ_ne 7).2.symm]
    rw [g7, g6, g5, g4, g3, g2, g1]; simp [Function.update_apply, BvE, show rE ≠ dK by decide]
  have st8Y : σ8.st sY = [] := by
    rw [g8]; simp [Function.update_apply, nYD, s7, Bst, stY]
  have sh8Y : σ8.sh sY = 0 := by
    rw [g8, g7, g6, g5, g4, g3, g2, g1]; simp [Function.update_apply, nY0, nYD, BshY]
  -- D: count the hash suffix down
  have stP : σ8.st (sk 0 0) = marks p ++ marks hbF ++ [false] := by rw [st8, frame_m, hwp, marks_append]
  have eD := suf1W_spec cap (sk 0 0) rA hbF σ8 (marks p) stP sh8 (by rw [v8A]; exact cw)
  set σD := (σ8.seth (sk 0 0) ((marks p).length + 2 * hbF.length)).setv rA (σ8.val rA - hbF.length) with hσD
  -- E: rewind
  have eE := rew2W_spec cap (sk 0 0) rE w.length σD (by rw [hσD]; simp [marks_len, hlen]; ring)
    (by rw [hσD]; simp [Function.update_apply, show rE ≠ rA by decide, v8E]) cw
  set σE := (σD.seth (sk 0 0) 0).setv rE 0 with hσE
  -- F: copy the prefix's pairs
  have eF := cpyW_spec cap (sk 0 0) sY rA (Ne.symm nY0) σE [] [] p (marks hbF ++ [false])
    (by rw [hσE, hσD]; simp [stP]) (by rw [hσE]; simp)
    (by rw [hσE, hσD]; simp [st8Y]) (by rw [hσE, hσD]; simp [Function.update_apply, nY0, sh8Y])
    (by rw [hσE, hσD]; simp [Function.update_apply, show rA ≠ rE by decide, v8A, hlen])
    (by rw [hlen] at cw; omega)
  set σF := cpyS (sk 0 0) sY rA σE [] [] p p.length with hσF
  -- G: the terminator
  have eG := WExec.wr (cap := cap) sY false σF
  have stFY : σF.st sY = marks p := by rw [hσF]; simp [cpyS]
  have shFY : σF.sh sY = (marks p).length := by rw [hσF]; simp [cpyS, nY0, marks_len]
  refine ⟨_, _, WExec.seq eA (WExec.seq eB (WExec.seq eP (WExec.seq eD (WExec.seq eE (WExec.seq eF eG))))), ?_, ?_⟩
  · unfold hbXCost
    have hp : p.length ≤ w.length := by omega
    have hh : hbF.length ≤ w.length := by omega
    omega
  · refine ⟨?_, ?_⟩
    · simp only [WState.sets_st, Function.update_self]
      rw [stFY, shFY, PrimT.C4Pipe.write_end, frame_m]
    · simp only [WState.sets_st, Function.update_apply, if_neg (Ne.symm nY0)]
      rw [hσF]; simp only [cpyS, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply,
        if_neg (Ne.symm nY0)]
      rw [hσE, hσD]; simp only [WState.setv_st, WState.seth_st]
      exact st8

end NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
