import Proof.Wire_3_5.Primitive.SeedFix.C4HkF

/-! # The HASH stage, part 7: the loop's entry on the pre-loop bank

"For each candidate child prefix [...] Choose a child with no larger value" (P3:2327-2336). On the bank after the HASH
setup (C4H-a's `HBank2`) and the pre-loop stage (`PreBank`), every tape of the HASH child family's decision loop docked
by `hashExt` carries the loop's bank before its first decision (**`entry_H`**), so the dock is a `C4Wrap.LoopEntry`
(**`hash_entry`**).

Paper quantity of the main type: the loop's entry bank (the kept words of P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4Set (slx slx_some slx_none)

section Entry
variable {x : ℕ} (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (A : C4Iface.AsmStage)
  (wa : RepairRepresentation.WilliamsAlgorithm) (PRE POST : List Bool) (KW : Fin 94 → List Bool) (q uu W sh : ℕ)
  (bits : List Bool) (hF : HashFamAt2 A wa PRE POST KW q uu W sh bits)
  (B : Fin (3 + x) → List Bool) (w v : List Bool) (ρ : ℕ) (hkT : Fin 94 → Fin (3 + x)) (hqT : Fin (3 + x))
  (off : ℕ) (hB : HBank2 L hLx B w v PRE POST KW q uu ρ hkT hqT off)
  (hr : off + 12 ≤ 3 + x) (hn : off + 12 + (hF.F.T + 1 + 1 + 1) ≤ 3 + x)
  (B2 : Fin (3 + x) → List Bool) (hP : PreBank off hr (hF.F.T + 1 + 1 + 1) hn B B2 w sh (2 ^ ρ))
include hB hP

/-- **The loop's entry**: every docked tape carries `loopBank F (2^ρ) (2^ρ + 1) 0`. -/
theorem entry_H (j : Fin (hF.F.T + 1 + 1 + 1)) :
    B2 (slx (off + 12) hn (hashExt L hLx A wa hkT hqT off (by omega) hF.F.T) j) =
      C4Wrap.loopBank hF.F (2 ^ ρ) (2 ^ ρ + 1) 0 j := by
  have hFt := hF.ht
  have hFT : hF.F.T = 2 * hF.F.t + 6 := rfl
  have hN := C4Set.Lay.N_eq L
  have hk0 := hB.koff ⟨0, by omega⟩
  have hpre := L.S3.preS.isLt
  have hpost := L.S3.postS.isLt
  have hU : HU = 253 := rfl
  have hC : CTH A wa = A.t + (HU + C4Pipe.CN wa) := rfl
  obtain ⟨jv, hj⟩ := j
  by_cases hk : jv < CTH A wa ∧ hKeepN A wa jv = true
  · have hjT : jv < hF.F.T := by omega
    have hjt : jv < hF.F.t := by omega
    have hkp : hF.F.keep ⟨jv, hjt⟩ = true := by rw [hF.keep]; exact hk.2
    rw [slx_some (show hashExt L hLx A wa hkT hqT off (by omega) hF.F.T ⟨jv, hj⟩ =
      some (hashTgt L hLx A wa hkT hqT off (by omega) jv) by unfold hashExt; rw [if_pos hk])]
    rw [C4SymW.loopBank_lt hF.F _ _ ⟨jv, hj⟩ hjT, C4SymW.src_kept hF.F _ ⟨jv, hjT⟩ hjt hkp]
    by_cases hp : jv = A.t + 94
    · rw [C4SymW.cin_pfx hF.F _ hjt (by rw [hF.pfx]; exact hp)]
      have e : hashTgt L hLx A wa hkT hqT off (by omega) jv = ⟨off + 1, by omega⟩ := by
        unfold hashTgt; rw [if_neg (by omega), dif_neg (by omega), if_pos (by omega)]
      rw [e, hP.pT]; rfl
    · rw [C4SymW.cin_kept hF.F _ hjt (by rw [hF.pfx]; exact hp) hkp, hF.K]
      rcases tgt_cases L hLx A wa hkT hqT off (by omega) jv hk.1 hk.2 with
        ⟨a, e⟩ | ⟨a, e⟩ | ⟨h, b, e⟩ | ⟨a, e⟩ | ⟨b, a, e⟩ | ⟨b, a, e⟩
      · rw [e]; unfold gS
        rw [hP.keep _ (by simp only [C4Set.Lay.gPRE]; omega) (by simp only [C4Set.Lay.gPRE]; omega), hB.hPRE]
        unfold hKN2; rw [if_pos (by omega), if_pos a]
      · rw [e]; unfold gS
        rw [hP.keep _ (by simp only [C4Set.Lay.gPOST]; omega) (by simp only [C4Set.Lay.gPOST]; omega), hB.hPOST]
        have hab : jv ≠ A.pA.val := fun e' => A.hAB (Fin.ext (e'.symm.trans a))
        unfold hKN2; rw [if_pos (by omega), if_neg hab, if_pos a]
      · rw [e]
        have hk1 := hB.koff ⟨jv - A.t, h⟩
        rw [hP.keep _ (by omega) (by omega), hB.hKW]
        unfold hKN2; rw [if_neg (by omega), dif_pos h, if_pos (by omega)]
      · exact absurd a hp
      · rw [e, hP.keep _ (by have := hB.qoff; omega) (by have := hB.qoff; omega), hB.hQ]
        unfold hKN2; rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_pos hk.1, if_pos a]
      · rw [e]; unfold gS
        rw [hP.keep _ (by simp only [C4Set.Lay.gUU]; omega) (by simp only [C4Set.Lay.gUU]; omega), hB.hUU]
        have hQU : jv - A.t - HU ≠ (C4Pipe.childQQ wa).val := by
          rw [a]; simp [C4Pipe.childQQ, C4Pipe.childUU]
        unfold hKN2; rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_pos hk.1, if_neg hQU, if_pos a]
  · by_cases hlog : jv = hF.F.T
    · rw [slx_some (show hashExt L hLx A wa hkT hqT off (by omega) hF.F.T ⟨jv, hj⟩ = some (gS L hLx L.gLG) by
        unfold hashExt; rw [if_neg hk, if_pos hlog])]
      rw [C4SymW.loopBank_log hF.F _ _ ⟨jv, hj⟩ hlog]
      unfold gS
      rw [hP.keep _ (by simp only [C4Set.Lay.gLG]; omega) (by simp only [C4Set.Lay.gLG]; omega), hB.hLG]
    · by_cases hdrv : jv = hF.F.T + 1
      · rw [slx_some (show hashExt L hLx A wa hkT hqT off (by omega) hF.F.T ⟨jv, hj⟩ = some (gS L hLx L.gRR) by
          unfold hashExt; rw [if_neg hk, if_neg hlog, if_pos hdrv])]
        rw [C4SymW.loopBank_drv hF.F _ _ ⟨jv, hj⟩ hdrv]
        unfold gS
        rw [hP.keep _ (by simp only [C4Set.Lay.gRR]; omega) (by simp only [C4Set.Lay.gRR]; omega), hB.hRR]
      · by_cases hcnt : jv = hF.F.T + 2
        · rw [slx_some (show hashExt L hLx A wa hkT hqT off (by omega) hF.F.T ⟨jv, hj⟩ = some ⟨off + 2, by omega⟩ by
            unfold hashExt; rw [if_neg hk, if_neg hlog, if_neg hdrv, if_pos hcnt])]
          rw [C4SymW.loopBank_cnt hF.F _ _ ⟨jv, hj⟩ hcnt, hP.cT, hF.bound]
          rfl
        · have hnone : hashExt L hLx A wa hkT hqT off (by omega) hF.F.T ⟨jv, hj⟩ = none := by
            unfold hashExt; rw [if_neg hk, if_neg hlog, if_neg hdrv, if_neg hcnt]
          have hjT : jv < hF.F.T := by omega
          have hv := slx_none (hoff := hn) hnone
          rw [hP.cells _ (by rw [hv]; exact Nat.le_add_right _ _) (by rw [hv]; simp only; omega)]
          rw [C4SymW.loopBank_lt hF.F _ _ ⟨jv, hj⟩ hjT]
          symm
          apply C4SymW.src_scr
          unfold C4Loop.ChildFam.cellS
          split_ifs with hl
          · rw [hF.keep]
            simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
            by_cases hc : jv < CTH A wa
            · simp only [not_and] at hk
              have := hk hc
              simp only [Bool.not_eq_true] at this
              exact this
            · unfold hKeepN
              simp only [Fin.val_mk] at hl
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          · rfl

end Entry

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
