import Proof.Wire_3_5.UnionMachine.NumsA8
import Proof.Wire_3_5.Primitive.Writers.SymDataCost
import Proof.Wire_3_5.Primitive.Writers.SymDecCounts
import Proof.Wire_3_5.FinalPass.S5TChABase

/-! # NW phase (a), part 9: the data stage on NW's bank and the counts onto stream `113`

At a SYM request `r`, from `PreDock` at `L = W = wOf |fpIn| n`: PA's data stage runs docked on `tmapA`
(`DataDock.dataDock_step`: its hypotheses from the call's envelope, the codes being words inside `fpIn`), leaving the
counts' word `dataWord (symCounts …) = false :: frame (unaryList …)` on `tOUT`; `unframeW` moves the counts onto stream
`113`. The result is the SYM numbers program's entry on NW's bank (`NumsIn`), the stash kept, the word streams blank,
every other stream of bounded length.

* `flat_len`, `dataIn_*`, `tmapA_inj`, `tmapA_ne`, `countsLen`, **`dockPost`**.

Paper quantities of the main type: the call's bottom counts (P3:3049-3050) on the numbers program's counts stream. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g)

theorem flat_len (f : ℕ → List Bool) : ∀ (xs : List ℕ) (y : ℕ), y ∈ xs → (f y).length ≤ (xs.flatMap f).length
  | [], y, hy => absurd hy (List.not_mem_nil)
  | a :: t, y, hy => by
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hy with h | h
    · subst h; omega
    · have := flat_len f t y h; omega

section DataIn
open NearCubicWires.WireExponent3_5.UnionMachine.DataDock

theorem dataIn_iIN (w : List Bool) (n L W : ℕ) : dataIn w n L W iIN = frame w := rfl
theorem dataIn_NT (w : List Bool) (n L W : ℕ) : dataIn w n L W (iOf Data.sNT) = List.replicate n true := rfl
theorem dataIn_LT (w : List Bool) (n L W : ℕ) : dataIn w n L W (iOf Data.sLT) = List.replicate L true := rfl
theorem dataIn_CT (w : List Bool) (n L W : ℕ) : dataIn w n L W (iOf Data.sCT) = List.replicate W true := rfl

theorem dataIn_other (w : List Bool) (n L W : ℕ) (j : Fin DT) (h0 : j.val ≠ 0) (h2 : j.val ≠ 2) (h3 : j.val ≠ 3)
    (h4 : j.val ≠ 4) : dataIn w n L W j = [] := by
  unfold dataIn
  revert h0 h2 h3 h4
  refine Fin.addCases (fun i => ?_) (fun o => ?_) j
  · intro h0 h2 h3 h4
    rw [Fin.addCases_left]
    unfold Data.rawIn
    have hv : (Fin.castAdd 1 i).val = i.val := rfl
    rw [hv] at h0 h2 h3 h4
    have n0 : i ≠ FinalPass.Tm.sTape Data.sIN := fun e => h0 (by rw [e, DockW.sTape_val]; rfl)
    have n1 : i ≠ FinalPass.Tm.sTape Data.sNT := fun e => h2 (by rw [e, DockW.sTape_val]; rfl)
    have n2 : i ≠ FinalPass.Tm.sTape Data.sLT := fun e => h3 (by rw [e, DockW.sTape_val]; rfl)
    have n3 : i ≠ FinalPass.Tm.sTape Data.sCT := fun e => h4 (by rw [e, DockW.sTape_val]; rfl)
    rw [if_neg n0, if_neg n1, if_neg n2, if_neg n3]
  · intro _ _ _ _
    rw [Fin.addCases_right]
    rfl

end DataIn

section Bank
variable (x : ℕ) (hx : DataDock.DT + 3 ≤ x)

theorem tmapA_inj : Function.Injective (tmapA x hx) :=
  DataDock.nwTmap_inj x (by omega) (sIn x) (by show 150 < 161; omega)

/-- A stream off `sIn` and off `161 … 160 + DT` is no data tape. -/
theorem tmapA_ne (i : Fin (LNS x + 1)) (h150 : i.val ≠ 150) (hlo : i.val < 161 ∨ 161 + DataDock.DT ≤ i.val) :
    ∀ j, tmapA x hx j ≠ i := by
  intro j e
  by_cases hj : j = DataDock.iIN
  · subst hj
    have : (tmapA x hx DataDock.iIN).val = 150 := by unfold tmapA DataDock.nwTmap; rw [if_pos rfl]; rfl
    rw [e] at this; exact h150 this
  · have := tmapA_val x hx j hj
    rw [e] at this
    have := j.isLt
    omega

end Bank

section Gate

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
