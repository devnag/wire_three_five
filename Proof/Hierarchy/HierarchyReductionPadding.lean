import Proof.Hierarchy.HierarchyReductionFields
import Proof.Hierarchy.HierarchySlice

/-! The exact slice driver, fixed hierarchy code, and literal three-frame
header/padding are produced on one shared finite layout. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def length (k C Cpad : ℕ) (code x : List Bool) := HierarchyBinary.inputLength k Cpad code.length C x.length
noncomputable def sliceProgram (k : ℕ) := RecoveryFocus.machine (sliceSlots k) (HierarchySlice.machine k)

theorem slice_ready (k C Cpad : ℕ) (code x : List Bool) (ambient : Fin (tapes k) → List Bool)
    (hf : Fields k C x ambient)
    (ha : ambient (extra k 7)=List.replicate (HierarchyBinary.allocation Cpad code.length C x.length) true)
    (hblank : HierarchyBound.Fresh ambient (base k+9)) :
    ∃ middle,ClockJoin.ReadyRun (sliceProgram k) (2*length k C Cpad code x+4) ambient middle ∧
      Fields k C x middle ∧ middle (extra k 9)=List.replicate (length k C Cpad code x) true ∧
      HierarchyBound.Fresh middle (base k+11) := by
  obtain ⟨r,hr,h0,h1,h2,hh,hs⟩ := HierarchySlice.slice_run k (HierarchyBinary.allocation Cpad code.length C x.length)
  have ht : r.final.tapes=![List.replicate (HierarchyBinary.allocation Cpad code.length C x.length) true,
      List.replicate (length k C Cpad code x) true,List.replicate (length k C Cpad code x+1) false] := by
    funext i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have h := (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    (sliceSlots k) (slice_injective k) ambient
    (by intro j; fin_cases j
        · exact ha
        · exact hblank _ (by simp [sliceSlots,extra])
        · exact hblank _ (by simp [sliceSlots,extra]))
  have hslots (j : Fin 3) : base k+7 ≤ (sliceSlots k j).val := by
    fin_cases j <;> simp [sliceSlots,extra]
  have hb := bound_bounds k
  have hl := base_lower k
  refine ⟨_,h,⟨?_,?_⟩,install_slot _ (slice_injective k) _ _ 1,?_⟩
  · rw [HierarchyBound.keep_install _ _ _ _ hslots _ (by change 2<base k+7; omega)]
    exact hf.1
  · rw [HierarchyBound.keep_install _ _ _ _ hslots _ (by omega)]
    exact hf.2
  · apply HierarchyBound.fresh_install _ _ _ (base k+9) _ (by omega) hblank
    intro j
    fin_cases j <;> simp [sliceSlots,extra]

def codeCost (code : List Bool) := 2*(frame code).length+2
theorem code_ready (k C Cpad : ℕ) (code x : List Bool) (ambient : Fin (tapes k) → List Bool)
    (hf : Fields k C x ambient) (hn : ambient (extra k 9)=List.replicate (length k C Cpad code x) true)
    (hblank : HierarchyBound.Fresh ambient (base k+11)) :
    ∃ middle,ClockJoin.ReadyRun (codeProgram k code) (codeCost code) ambient middle ∧
      Fields k C x middle ∧ middle (extra k 9)=List.replicate (length k C Cpad code x) true ∧
      middle (extra k 11)=frame code ∧ HierarchyBound.Fresh middle (base k+13) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (frame code)
  have h := (show ClockJoin.ReadyRun _ _ _ _ from ⟨r,hr,ht,hh,hs.le⟩).focus
    (codeSlots k) (code_injective k) ambient
    (by intro j; fin_cases j <;> exact hblank _ (by simp [codeSlots,extra]))
  have hslots (j : Fin 2) : base k+11 ≤ (codeSlots k j).val := by
    fin_cases j <;> simp [codeSlots,extra]
  have hb := bound_bounds k
  have hl := base_lower k
  refine ⟨_,h,⟨?_,?_⟩,?_,install_slot _ (code_injective k) _ _ 0,?_⟩
  · rw [HierarchyBound.keep_install _ _ _ _ hslots _ (by change 2<base k+11; omega)]
    exact hf.1
  · rw [HierarchyBound.keep_install _ _ _ _ hslots _ (by omega)]
    exact hf.2
  · rw [HierarchyBound.keep_install _ _ _ _ hslots _ (by simp [extra])]
    exact hn
  · apply HierarchyBound.fresh_install _ _ _ (base k+11) _ (by omega) hblank
    intro j
    fin_cases j <;> simp [codeSlots,extra]

end NearCubicWires.RepairOrdinary.HierarchyReduction
