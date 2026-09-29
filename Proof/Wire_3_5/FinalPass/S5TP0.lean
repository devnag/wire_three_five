import Proof.Wire_3_5.FinalPass.S5TLay
import Proof.Wire_3_5.Primitive.SeedFix.TS4N

/-! # S5-THR, part 7: the prep docked (P3:3083-3086, P3:3425-3430)

The prep `p0M` (the numbers machine's three inputs: `1^{|carriers|}`, `1^{cap_T}`, `1^V`, `V = W_p + (n+1)^{26}`)
docked on the THR half's layout by `p0Map`: its request on the input stream, its fill count `1^{W_p}` on scratch
stream `0`, the rest on its block (`DockW.dockS`).

* `p0_in` (the prep's entry bank read off the layout); **`p0_dock`** (the docked run and the prep's outputs);
* **`capTL_eq_capOf`** (the capTOf join, by `rfl`): `capTL l F.cr n` is the ledger's THR cap
  `((gate0 l F).budget kclk coef A a ha).capOf .thr n` (`rowBBudget_capOf`, `gateRow`, `gateSp`).

Paper quantities of the main type: `|carriers|`, the THR cap `B_T(n)`, W6's count `V`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (dockS updS sTape_val)

variable (D x6 xt : ℕ) (cap : ℕ)

theorem p0_in (σ : WState (nsL D x6 xt) nrL) (w : List Bool) (Wp : ℕ)
    (hIn : σ.st (sIn D x6 xt) = frame w) (hC : σ.st (sMisc D x6 xt 0) = List.replicate Wp true)
    (hblk : ∀ j : Fin P0T, j.val ≠ 0 → j.val ≠ 2 → σ.st (p0Map D x6 xt j) = []) :
    (fun j : Fin (LNS 0 + 2 + LNR + 1) => σ.st (p0Map D x6 xt j)) =
      Fin.addCases (m := LNS 0 + 2 + LNR) (n := 1) (motive := fun _ => List Bool) (PrimT.TS4.rawS w Wp)
        (fun _ : Fin 1 => List.replicate 0 false) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · rw [Fin.addCases_left]
    unfold PrimT.TS4.rawS
    have e0 : sTape (nr := LNR) (sk 0 0) = ⟨0, by decide⟩ := rfl
    have e2 : sTape (nr := LNR) (sk 0 1) = ⟨2, by decide⟩ := rfl
    rw [e0, e2]
    by_cases h0 : i.val = 0
    · rw [if_pos (Fin.ext h0)]
      have : p0Map D x6 xt (Fin.castAdd 1 i) = sIn D x6 xt := by unfold p0Map; rw [if_pos (by simpa using h0)]
      rw [this, hIn]
    · rw [if_neg (fun h => h0 (congrArg Fin.val h))]
      by_cases h2 : i.val = 2
      · rw [if_pos (Fin.ext h2)]
        have : p0Map D x6 xt (Fin.castAdd 1 i) = sMisc D x6 xt 0 := by
          unfold p0Map; rw [if_neg (by simpa using h0), if_pos (by simpa using h2)]
        rw [this, hC]
      · rw [if_neg (fun h => h2 (congrArg Fin.val h))]
        exact hblk _ (by simpa using h0) (by simpa using h2)
  · rw [Fin.addCases_right]
    exact hblk _ (by simp [LNR]) (by simp [LNR])

theorem p0_dock (l : Literals) (cr : ℕ) (σ : WState (nsL D x6 xt) nrL) (n : ℕ) (codes cc : List ℕ)
    (tl : List Bool) (Wp : ℕ) (hIn : σ.st (sIn D x6 xt) = frame (PrimAsm.Data.reqW n true codes cc tl))
    (hC : σ.st (sMisc D x6 xt 0) = List.replicate Wp true)
    (hblk : ∀ j : Fin P0T, j.val ≠ 0 → j.val ≠ 2 → σ.st (p0Map D x6 xt j) = []) (hsh : ∀ i, σ.sh i = 0)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ Wp) (ha : codes.length ≤ 4) (hnc : cc.length ≤ 2)
    (hN : PrimT.TS4.needT l cr n ≤ 2 * Wp + 2) :
    ∃ (tout : Fin (LNS 0 + 2 + LNR) → List Bool) (m : ℕ),
      Step (RecoveryFocus.machine (fun j => sTape (nr := nrL) (p0Map D x6 xt j))
          (PrimT.TS4.p0M cr (gateCParams1 l).ζ (gateCδ1 l) (gateCap l)))
        (2 * PrimT.TS4.p0StageCost n cr (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) codes.length
          cc.length Wp Wp + 2)
        (wenc cap σ).H (wenc cap σ).A
        (wenc cap (updS (p0Map D x6 xt) σ (fun _ => 0) (Fin.addCases (m := LNS 0 + 2 + LNR) (n := 1)
          (motive := fun _ => List Bool) tout (fun _ : Fin 1 => List.replicate m false)))).H
        (wenc cap (updS (p0Map D x6 xt) σ (fun _ => 0) (Fin.addCases (m := LNS 0 + 2 + LNR) (n := 1)
          (motive := fun _ => List Bool) tout (fun _ : Fin 1 => List.replicate m false)))).A ∧
      tout (sTape (sk 0 0)) = frame (PrimAsm.Data.reqW n true codes cc tl) ∧
      tout (sTape (sk 0 1)) = List.replicate Wp true ∧ tout (sTape (sk 0 3)) = List.replicate cc.length true ∧
      tout (sTape (sk 0 4)) = List.replicate (PrimT.TS4.capTL l cr n) true ∧
      tout (sTape (sk 0 5)) = List.replicate (Wp + (n + 1) ^ 26) true := by
  obtain ⟨tout, m, hs, f0, f1, f3, f4, f5⟩ := PrimT.TS4.p0_step cr n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l)
    (gateCap l) true codes cc tl Wp Wp hKb (PrimT.TS4.p0need_of l cr n Wp codes.length cc.length ha hnc hN)
  refine ⟨tout, m, dockS cap (p0Map D x6 xt) (p0Map_inj D x6 xt) σ ?_, f0, f1, f3, f4, f5⟩
  refine hs.congr_in ?_ ?_
  · funext j; exact (hsh _).symm
  · exact (p0_in D x6 xt σ _ Wp hIn hC hblk).symm

/-- **The capTOf join**: the THR cap the prep prints (`capTL`, `1^{cap_T}` on port 4) is the ledger's
`B_T(n)` at the gate (`tr:B`, P3:3425-3430), definitionally. -/
theorem capTL_eq_capOf (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) :
    PrimT.TS4.capTL l F.cr n = ((gate0 l F).budget kclk coef A a ha).capOf .thr n := rfl

end NearCubicWires.WireExponent3_5.FinalPass.S5T
