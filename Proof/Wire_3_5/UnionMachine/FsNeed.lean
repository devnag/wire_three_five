import Proof.Wire_3_5.UnionMachine.FsReady

/-! # C6, the FILTER setup, part 7: the capacity need

The setup's capacity need (**`fsNeed`**, `10^5·(M+1)^3` for the values' sum `M = len + cap + err + L + r4 + G + off + S`,
`S = |GapSeed P|`) implies every capacity fact of the stages and of `FiltReady` (**`fsCap_of_need`**): the filter's
numbers are below the seeds' count (`seedBits = 256·(3·labelBits − 1) + 512·fieldBits + 160·(walkLen − 1) < S`,
`GapNums.sbOf`), the slice's labels below `off + L + (r4 + 4)·G` (**`slice_lab_le`**), and the FILTER row's input word
has an explicit length (**`filtEmit_length`**, `FiltRec.filtEmit_eq`).

Paper quantity: the setup's capacity, polynomial in the call's values and the seeds' count (filt:gap, P3:2029-2030). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FsNeed
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.SupplierWalk NearCubicWires.WireExponent3_5.UnionMachine

/-- **The setup's capacity need.** -/
def fsNeed (len cap err L r4 G off S : ℕ) : ℕ := 100000 * (len + cap + err + L + r4 + G + off + S + 1) ^ 3

/-! ## Words and labels -/

theorem reps_length : ∀ (n : ℕ) (u : List Bool), (reps n u).length = n * u.length
  | 0, _ => by simp
  | n + 1, u => by rw [reps_succ, List.length_append, reps_length n u, Nat.succ_mul]

theorem flatMap_m2_length : ∀ tw : List Bool, (tw.flatMap m2).length = 4 * tw.length
  | [] => rfl
  | b :: tw => by
    rw [List.flatMap_cons, List.length_append, flatMap_m2_length tw, List.length_cons]
    simp [m2]
    ring

theorem labE_length (lab : ℕ) : (labE lab).length = 4 * lab + 4 := by
  simp [labE, reps_length, m2]
  ring

/-- **The FILTER row's input word's length.** -/
theorem filtEmit_length (Lp d cap1 thr c : ℕ) (tw : List Bool) (labs : List ℕ) :
    (filtEmit Lp d cap1 thr c tw labs).length = 32 * Lp + 4 * d + (labs.flatMap labE).length + 4 * cap1 +
      4 * tw.length + 4 * thr + 32 * c + 133 := by
  simp [filtEmit, reps_length, flatMap_m2_length, m2, m3]
  ring

theorem slice_lab_le (r4 G off L lab : ℕ) (h : lab ∈ sliceLabs r4 G off L) : lab ≤ off + L + (r4 + 4) * G := by
  simp only [sliceLabs, gateLabs, List.mem_flatMap, List.mem_range', List.mem_map, List.mem_range] at h
  obtain ⟨gi, ⟨i, hi, rfl⟩, k, hk, rfl⟩ := h
  have : (r4 + k) * G ≤ (r4 + 4) * G := Nat.mul_le_mul_right _ (by omega)
  omega

theorem sum_lab_le (B : ℕ) : ∀ labs : List ℕ, (∀ lab ∈ labs, lab ≤ B) →
    (labs.map fun lab => 2 * lab + 10).sum ≤ labs.length * (2 * B + 10)
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x List.mem_cons_self
    have h2 := sum_lab_le B xs (fun l hl => h l (List.mem_cons_of_mem x hl))
    have e : (xs.length + 1) * (2 * B + 10) = xs.length * (2 * B + 10) + (2 * B + 10) := by ring
    rw [e]
    omega

theorem labE_sum_le (B : ℕ) : ∀ labs : List ℕ, (∀ lab ∈ labs, lab ≤ B) →
    (labs.flatMap labE).length ≤ labs.length * (4 * B + 4)
  | [], _ => by simp
  | x :: xs, h => by
    rw [List.flatMap_cons, List.length_append, labE_length, List.length_cons]
    have h1 := h x List.mem_cons_self
    have h2 := labE_sum_le B xs (fun l hl => h l (List.mem_cons_of_mem x hl))
    have e : (xs.length + 1) * (4 * B + 4) = xs.length * (4 * B + 4) + (4 * B + 4) := by ring
    rw [e]
    omega

/-! ## The need implies the capacity facts -/

theorem fsCap_of_need (cap : ℕ) (P : GapParams) (g L r4 G off : ℕ) (hg : g < Fintype.card (GapSeed P))
    (hlen : (sliceLabs r4 G off L).length = 4 * L)
    (h : fsNeed P.len P.cap P.errExp L r4 G off (Fintype.card (GapSeed P)) ≤ cap) :
    FsReady.FsCap cap P L r4 G off g := by
  obtain ⟨S, hS⟩ : ∃ S, S = Fintype.card (GapSeed P) := ⟨_, rfl⟩
  rw [← hS] at hg h
  have hS2 : S = 2 ^ P.seedBits := by rw [hS]; exact seedCount_eq P
  have hlt : P.seedBits < S := by rw [hS2]; exact Nat.lt_two_pow_self
  have hsbv : P.seedBits = 2 * (128 * (P.labelBits + (P.labelBits - 1) + P.labelBits + 2 * P.fieldBits)) +
      160 * (P.walkLen - 1) := by rw [GapNums.seedBits_eq]; rfl
  obtain ⟨A, hA⟩ : ∃ A, A = P.len + P.cap + P.errExp + L + r4 + G + off + S + 1 := ⟨_, rfl⟩
  have hN : 100000 * A ^ 3 ≤ cap := by rw [hA]; unfold fsNeed at h; exact h
  have hpb : P.prefixBits ≤ P.labelBits := le_max_left _ _
  have hlbA : P.labelBits ≤ A := by omega
  have hfbA : P.fieldBits ≤ A := by omega
  have hwlA : P.walkLen ≤ A := by omega
  have hpbA : P.prefixBits ≤ A := by omega
  have hgA : g ≤ A := by omega
  have hLA : L ≤ A := by omega
  have hr4A : r4 ≤ A := by omega
  have hGA : G ≤ A := by omega
  have hoffA : off ≤ A := by omega
  have hA1 : 1 ≤ A := by omega
  have hcA : P.cap ≤ A := by omega
  have hlenA : P.len ≤ A := by omega
  have herrA : P.errExp ≤ A := by omega
  have hSA : S ≤ A := by omega
  have hAA : A ≤ A * A := Nat.le_mul_self A
  have hA3 : A * A ≤ A ^ 3 := by
    have : A ^ 2 ≤ A ^ 3 := Nat.pow_le_pow_right hA1 (by norm_num)
    rw [sq] at this; exact this
  have he4 : P.errExp / 4 ≤ A := by omega
  have hth : (P.walkLen + 1) / 2 ≤ A := by omega
  have hlb1 : P.labelBits - 1 ≤ A := by omega
  have hwn : P.walkLen - 1 ≤ A := by omega
  have pWL : P.walkLen * L ≤ A * A := Nat.mul_le_mul hwlA hLA
  have pEL : P.errExp / 4 * L ≤ A * A := Nat.mul_le_mul he4 hLA
  have hMl : off + L + (r4 + 4) * G ≤ 7 * (A * A) := by
    have : (r4 + 4) * G ≤ (A + 4) * A := Nat.mul_le_mul (by omega) hGA
    linarith
  have pLM : L * (off + L + (r4 + 4) * G) ≤ A * (7 * (A * A)) := Nat.mul_le_mul hLA hMl
  have hA3' : A * (7 * (A * A)) = 7 * A ^ 3 := by ring
  have hlabs : ∀ lab ∈ sliceLabs r4 G off L, lab ≤ off + L + (r4 + 4) * G := slice_lab_le r4 G off L
  have hsum := sum_lab_le _ _ hlabs
  have hflat := labE_sum_le _ _ hlabs
  rw [hlen] at hsum hflat
  have hlS : labSum (sliceLabs r4 G off L) ≤ 5 + 4 * L * (2 * (off + L + (r4 + 4) * G) + 10) := by
    unfold labSum; omega
  have hlF : ((sliceLabs r4 G off L).flatMap labE).length ≤ 4 * L * (4 * (off + L + (r4 + 4) * G) + 4) := hflat
  have hwOf : wOf P.fieldBits P.labelBits = 2 * P.fieldBits + P.labelBits + (P.labelBits - 1) + P.labelBits := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [pow_succ, ← hS2]; linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [hwOf]; linarith
  · linarith
  · linarith
  · intro e
    rw [filtDeg_filterTable, tableWord_length, cap37_filterTable, filtEmit_eq, filtEmit_length, filtDeg_filterTable,
      cap1C_eq _ _ hlen, cap37_filterTable, tableWord_length]
    unfold majorityThreshold
    refine ⟨by linarith only [hN, hA3, hAA, hA1, hLA, hwlA, hr4A, hGA, hoffA], by linarith only [hN, hA3, hAA, hA1, hLA, hwlA, hr4A, hGA, hoffA, hlF, hlS, pLM, hA3', hMl],
      by linarith only [hN, hA3, hAA, hA1, hLA, hwlA, hr4A, hGA, hoffA, hlF, hlS, pWL, pLM, hA3'], by linarith only [hN, hA3, hAA, hA1, hLA, hwlA, hr4A, hGA, hoffA, hlF, hlS, pWL, hth, pLM, hA3'],
      by linarith only [hN, hA3, hAA, hA1, hLA, hwlA, hr4A, hGA, hoffA, hlF, hlS, pWL, hth, pLM, hA3']⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FsNeed
