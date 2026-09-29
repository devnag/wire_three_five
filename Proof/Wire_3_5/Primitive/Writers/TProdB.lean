import Proof.Wire_3_5.Primitive.SeedFix.C4KWTypes

/-! # T-b: the kept words writer docked (`KwDock`, the contract, generic)

P3:3011-3016 (the Hb printer's static words, before the loop): the writer `W.M` focused onto the bank by `kwSl`
(outputs `oK + j`, inputs `kIn i < oK`, scratch `oK + 94 + k`) runs from the bank with its inputs on `kIn` and the
region blank (`install_existing`) and leaves the framed kept words on `oK + j`, its inputs unchanged, the scratch
falses (`W.run`, `Step.focus`).
* `kwSl_out`, `kwSl_in`, `kwSl_sc`, `kwSl_inj`; **`kwDock_ok`**: `∀ W x oK hK kIn, KwDock W x oK hK kIn`.

Paper quantity of the main type: the Hb printer's static words `KW` on the setup's tapes (P3:3011-3016). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.TProd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.PrimT.C4H NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound

section KW
variable (W : KWW) (x oK : ℕ) (hK : oK + 94 + W.x ≤ 3 + x) (kIn : Fin 12 → Fin (3 + x))

theorem kwSl_out (j : Fin 94) : kwSl W x oK hK kIn (Fin.castAdd W.x (Fin.castAdd 12 j)) = ⟨oK + j.val, by omega⟩ := by
  simp [kwSl]

theorem kwSl_in (i : Fin 12) : kwSl W x oK hK kIn (Fin.castAdd W.x (Fin.natAdd 94 i)) = kIn i := by
  simp [kwSl]

theorem kwSl_sc (k : Fin W.x) : kwSl W x oK hK kIn (Fin.natAdd (94 + 12) k) = ⟨oK + 94 + k.val, by omega⟩ := by
  simp [kwSl]

theorem kwSl_inj (hinj : Function.Injective kIn) (hlt : ∀ i, (kIn i).val < oK) :
    Function.Injective (kwSl W x oK hK kIn) := by
  intro a b
  refine Fin.addCases (fun a1 => ?_) (fun a2 => ?_) a
  · refine Fin.addCases (fun j => ?_) (fun i => ?_) a1
    · refine Fin.addCases (fun b1 => ?_) (fun b2 => ?_) b
      · refine Fin.addCases (fun j' => ?_) (fun i' => ?_) b1
        · intro h
          rw [kwSl_out, kwSl_out] at h
          have := congrArg Fin.val h
          simp only at this
          congr 2; exact Fin.ext (by omega)
        · intro h
          rw [kwSl_out, kwSl_in] at h
          have := congrArg Fin.val h; have := hlt i'; simp only at *; omega
      · intro h
        rw [kwSl_out, kwSl_sc] at h
        have := congrArg Fin.val h; simp only at this; have := j.isLt; omega
    · refine Fin.addCases (fun b1 => ?_) (fun b2 => ?_) b
      · refine Fin.addCases (fun j' => ?_) (fun i' => ?_) b1
        · intro h
          rw [kwSl_in, kwSl_out] at h
          have := congrArg Fin.val h; have := hlt i; simp only at *; omega
        · intro h
          rw [kwSl_in, kwSl_in] at h
          rw [hinj h]
      · intro h
        rw [kwSl_in, kwSl_sc] at h
        have := congrArg Fin.val h; have := hlt i; simp only at *; omega
  · refine Fin.addCases (fun b1 => ?_) (fun b2 => ?_) b
    · refine Fin.addCases (fun j' => ?_) (fun i' => ?_) b1
      · intro h
        rw [kwSl_sc, kwSl_out] at h
        have := congrArg Fin.val h; simp only at this; have := j'.isLt; omega
      · intro h
        rw [kwSl_sc, kwSl_in] at h
        have := congrArg Fin.val h; have := hlt i'; simp only at *; omega
    · intro h
      rw [kwSl_sc, kwSl_sc] at h
      have := congrArg Fin.val h
      simp only at this
      congr 1; exact Fin.ext (by omega)

/-- **T-b's producer**: the kept words writer, docked, meets `KwDock` at every layout. -/
theorem kwDock_ok : KwDock W x oK hK kIn := by
  intro hinj hlt D cap B hB hbl
  obtain ⟨B0, hrun, hout, hin, hscr⟩ := W.run D cap
  have hinjS := kwSl_inj W x oK hK kIn hinj hlt
  have s := hrun.focus (kwSl W x oK hK kIn) hinjS (fun _ => 0) B
  have hdz : dockH (kwSl W x oK hK kIn) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, kwSl W x oK hK kIn j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [dockH_slot _ hinjS]
    · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩)]
  have hins : install (kwSl W x oK hK kIn) B (partIn (no := 94) id W.x D cap) = B := by
    apply install_existing
    intro j
    refine Fin.addCases (fun j1 => ?_) (fun k => ?_) j
    · refine Fin.addCases (fun jo => ?_) (fun i => ?_) j1
      · rw [kwSl_out]
        simp only [partIn, Fin.addCases_left]
        exact hbl _ (by simp only; omega) (by simp only; have := jo.isLt; omega)
      · rw [kwSl_in]
        simp only [partIn, Fin.addCases_left, Fin.addCases_right, id]
        exact hB i
    · rw [kwSl_sc]
      simp only [partIn, Fin.addCases_right]
      exact hbl _ (by simp only; omega) (by simp only; have := k.isLt; omega)
  rw [hdz, hins] at s
  refine ⟨install (kwSl W x oK hK kIn) B B0, s, fun j => ?_, fun i hi => ?_, fun i h1 h2 => ?_⟩
  · have := install_slot (kwSl W x oK hK kIn) hinjS B B0 (Fin.castAdd W.x (Fin.castAdd 12 j))
    rw [kwSl_out] at this
    rw [this, hout j]
    rfl
  · by_cases hs : ∃ j, kwSl W x oK hK kIn j = i
    · obtain ⟨j, rfl⟩ := hs
      rw [install_slot _ hinjS]
      revert hi
      refine Fin.addCases (fun j1 => ?_) (fun k => ?_) j
      · refine Fin.addCases (fun jo => ?_) (fun i' => ?_) j1
        · intro hi
          rw [kwSl_out] at hi
          simp only at hi
          have := jo.isLt
          omega
        · intro _
          rw [kwSl_in, hin i', hB i']
          rfl
      · intro hi
        rw [kwSl_sc] at hi
        simp only at hi
        have := k.isLt
        omega
    · exact install_other _ _ _ _ (fun j h => hs ⟨j, h⟩)
  · obtain ⟨m, hm, hk⟩ := hscr ⟨i.val - (oK + 94), by omega⟩
    refine ⟨m, hm, ?_⟩
    have := install_slot (kwSl W x oK hK kIn) hinjS B B0 (Fin.natAdd (94 + 12) ⟨i.val - (oK + 94), by omega⟩)
    rw [kwSl_sc] at this
    have e : (⟨oK + 94 + (i.val - (oK + 94)), by omega⟩ : Fin (3 + x)) = i := Fin.ext (by simp only; omega)
    rw [e] at this
    rw [this, hk]

end KW

end NearCubicWires.WireExponent3_5.PrimAsm.TProd
