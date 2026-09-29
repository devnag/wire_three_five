import Proof.Wire_3_5.FinalPass.WordAux

/-! # S4 (f1), the tables writer, part 2: the unit's emission (P3:2036-2101)

After a unit's table stages, the table `tw = tableWord (filterTable P e L)` is on a stream `T` (head `0`) and its
length in a register `c`. **`emitE`** appends `frame tw` to the output `O` (head at the output's end, its last cell
the blank marker) when the flag bit on `F` is set, and nothing otherwise, then advances the unit counter `K`
(`1^j ↦ 1^(j+1)`, counting in `d`). Word programs with parametric streams and registers:

* `cpBody`, `cpLoopE`, **`cpLoopE_spec`** (the table framed onto the output, bit by bit);
* `copyE`, **`copyE_spec`** (then the frame's end marker and the output's blank marker);
* `incE`, **`incE_spec`** (the counter);
* **`emitE_spec`**: the output becomes `out ++ (if flag then frame tw else []) ++ [false]`, the counter `1^(j+1)`.

Paper quantity of the main type: the tables word's piece `frame (tableWord (filterTable P e L))` of one seed and mask
length. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

section Gen
variable {ns nr : ℕ} (cap : ℕ) (T O K F : Fin (ns + 1)) (c d : Fin nr)

theorem wz (A Z : List Bool) (hZ : Z.length ≤ 1) (b : Bool) : writeTapeBit (A ++ Z) A.length b = A ++ [b] := by
  match Z, hZ with
  | [], _ => rw [List.append_nil]; exact writeTapeBit_end' A b
  | [z], _ => exact writeTapeBit_mid' A [] z b
  | _ :: _ :: _, h => simp at h

theorem frameP_take_succ (tw : List Bool) (i : ℕ) (hi : i < tw.length) :
    frameP (tw.take (i + 1)) = frameP (tw.take i) ++ [true, tw.getD i false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
  unfold frameP
  rw [List.flatMap_append]
  rfl

/-! ## The table framed onto the output -/

/-- One table bit: the marker, the bit, both heads advanced. -/
def cpBody : WM ns nr :=
  .seq (.dec c) (.seq (.wr O true) (.seq (.fwd O) (.seq (.ifs T (.wr O true) (.wr O false)) (.seq (.fwd O) (.fwd T)))))

theorem cpBody_spec (hTO : T ≠ O) (tw out Z : List Bool) (i m : ℕ) (σ : WState ns nr) (hc : σ.val c = m + 1)
    (hcc : m + 1 ≤ cap) (hT : σ.st T = tw) (hTh : σ.sh T = i) (hi : i < tw.length)
    (hO : σ.st O = out ++ frameP (tw.take i) ++ Z) (hZ : Z.length ≤ 1) (hOh : σ.sh O = out.length + 2 * i) :
    ∃ σ' : WState ns nr, WExec cap (cpBody T O c) σ σ' 12 ∧ σ'.st O = out ++ frameP (tw.take (i + 1)) ∧
      σ'.sh O = out.length + 2 * (i + 1) ∧ σ'.sh T = i + 1 ∧ σ'.val c = m ∧ σ'.st T = tw ∧
      (∀ s, s ≠ O → σ'.st s = σ.st s) ∧ (∀ s, s ≠ O → s ≠ T → σ'.sh s = σ.sh s) ∧
      (∀ r, r ≠ c → σ'.val r = σ.val r) ∧ σ'.cell = σ.cell := by
  have hA : (out ++ frameP (tw.take i)).length = out.length + 2 * i := by
    simp only [List.length_append, frameP_length, List.length_take]; omega
  have e1 := WExec.dec (cap := cap) c σ (by omega)
  rw [hc, Nat.add_sub_cancel] at e1
  have e2 := WExec.wr (cap := cap) O true (σ.setv c m)
  have w2 : writeTapeBit ((σ.setv c m).st O) ((σ.setv c m).sh O) true = out ++ frameP (tw.take i) ++ [true] := by
    simp only [WState.setv_st, WState.setv_sh]
    rw [hO, hOh, ← hA, wz _ Z hZ]
  rw [w2] at e2
  have e3 := WExec.fwd (cap := cap) O ((σ.setv c m).sets O (out ++ frameP (tw.take i) ++ [true]))
  obtain ⟨σ3, h3⟩ : ∃ y : WState ns nr, y = ((σ.setv c m).sets O (out ++ frameP (tw.take i) ++ [true])).seth O
      (((σ.setv c m).sets O (out ++ frameP (tw.take i) ++ [true])).sh O + 1) := ⟨_, rfl⟩
  rw [← h3] at e3
  have hb : wbit σ3 T = tw.getD i false := by
    unfold wbit
    rw [h3]
    simp only [WState.seth_st, WState.seth_sh, WState.sets_st, WState.sets_sh, WState.setv_st, WState.setv_sh]
    rw [Function.update_of_ne hTO, Function.update_of_ne hTO, hT, hTh]
    rfl
  have h3O : σ3.st O = out ++ frameP (tw.take i) ++ [true] := by rw [h3]; simp
  have h3Oh : σ3.sh O = out.length + 2 * i + 1 := by rw [h3]; simp [hOh]
  have e4 : WExec cap (.ifs T (.wr O true) (.wr O false)) σ3
      (σ3.sets O (out ++ frameP (tw.take i) ++ [true] ++ [tw.getD i false])) 2 := by
    have w4 : ∀ v : Bool, writeTapeBit (σ3.st O) (σ3.sh O) v = out ++ frameP (tw.take i) ++ [true] ++ [v] := by
      intro v
      have hl : out.length + 2 * i + 1 = (out ++ frameP (tw.take i) ++ [true]).length := by
        simp only [List.length_append, List.length_singleton, frameP_length, List.length_take]; omega
      rw [h3O, h3Oh, hl, writeTapeBit_end']
    cases hg : tw.getD i false
    · have := WExec.wr (cap := cap) O false σ3
      rw [w4] at this
      exact WExec.ifsF (by rw [hb, hg]) this
    · have := WExec.wr (cap := cap) O true σ3
      rw [w4] at this
      exact WExec.ifsT (by rw [hb, hg]) this
  have e5 := WExec.fwd (cap := cap) O (σ3.sets O (out ++ frameP (tw.take i) ++ [true] ++ [tw.getD i false]))
  have e6 := WExec.fwd (cap := cap) T ((σ3.sets O (out ++ frameP (tw.take i) ++ [true] ++ [tw.getD i false])).seth O
    ((σ3.sets O (out ++ frameP (tw.take i) ++ [true] ++ [tw.getD i false])).sh O + 1))
  refine ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [WState.seth_st, WState.sets_st, Function.update_self]
    rw [frameP_take_succ tw i hi]
    simp
  · simp only [WState.seth_sh, WState.sets_sh]
    rw [Function.update_of_ne hTO.symm, Function.update_self, h3Oh]
    ring
  · simp only [WState.seth_sh, WState.sets_sh, Function.update_self]
    rw [h3]
    simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_of_ne hTO, hTh]
  · simp only [WState.seth_val, WState.sets_val]
    rw [h3]
    simp
  · simp only [WState.seth_st, WState.sets_st]
    rw [Function.update_of_ne hTO, h3]
    simp only [WState.seth_st, WState.sets_st, WState.setv_st]
    rw [Function.update_of_ne hTO, hT]
  · intro s hs
    simp only [WState.seth_st, WState.sets_st]
    rw [Function.update_of_ne hs, h3]
    simp only [WState.seth_st, WState.sets_st, WState.setv_st]
    rw [Function.update_of_ne hs]
  · intro s hs hsT
    simp only [WState.seth_sh, WState.sets_sh]
    rw [Function.update_of_ne hsT, Function.update_of_ne hs, h3]
    simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh]
    rw [Function.update_of_ne hs]
  · intro r hr
    simp only [WState.seth_val, WState.sets_val]
    rw [h3]
    simp only [WState.seth_val, WState.sets_val, WState.setv_val]
    rw [Function.update_of_ne hr]
  · rw [h3]
    rfl

/-- The table framed onto the output, while `c` counts down. -/
def cpLoopE : WM ns nr := .whr c (cpBody T O c)

theorem cpLoopE_spec (hTO : T ≠ O) (tw out : List Bool) :
    ∀ (m i : ℕ) (Z : List Bool) (σ : WState ns nr), i + m = tw.length → σ.val c = m → m ≤ cap →
      σ.st T = tw → σ.sh T = i → σ.st O = out ++ frameP (tw.take i) ++ Z → Z.length ≤ 1 →
      σ.sh O = out.length + 2 * i →
      ∃ (σ' : WState ns nr) (Zf : List Bool), WExec cap (cpLoopE T O c) σ σ' (m * 14 + 1) ∧
        σ'.st O = out ++ frameP tw ++ Zf ∧ Zf.length ≤ 1 ∧ σ'.sh O = out.length + 2 * tw.length ∧
        (∀ s, s ≠ O → σ'.st s = σ.st s) ∧ (∀ s, s ≠ O → s ≠ T → σ'.sh s = σ.sh s) ∧
        (∀ r, r ≠ c → σ'.val r = σ.val r) ∧ σ'.cell = σ.cell
  | 0, i, Z, σ, hl, hc, _, _, _, hO, hZ, hOh => by
    have hi : i = tw.length := by omega
    refine ⟨σ, Z, WExec.cast cap (WExec.whrF hc) rfl (by omega), ?_, hZ, by rw [hOh, hi], fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩
    rw [hO, hi, List.take_of_length_le le_rfl]
  | m + 1, i, Z, σ, hl, hc, hcc, hT, hTh, hO, hZ, hOh => by
    obtain ⟨σ1, e1, o1, oh1, th1, c1, t1, s1, h1, v1, l1⟩ :=
      cpBody_spec cap T O c hTO tw out Z i m σ hc hcc hT hTh (by omega) hO hZ hOh
    obtain ⟨σ2, Zf, e2, o2, z2, oh2, s2, h2, v2, l2⟩ := cpLoopE_spec hTO tw out m (i + 1) [] σ1 (by omega) c1
      (by omega) t1 th1 (by rw [o1, List.append_nil]) (by simp) oh1
    refine ⟨σ2, Zf, WExec.cast cap (WExec.whrT (by rw [hc]; omega) e1 e2) rfl (by ring_nf; omega), o2, z2, oh2,
      fun s hs => (s2 s hs).trans (s1 s hs), fun s hs hsT => (h2 s hs hsT).trans (h1 s hs hsT),
      fun r hr => (v2 r hr).trans (v1 r hr), l2.trans l1⟩

/-- **The frame of the table appended**: the loop, the frame's end marker, the output's blank marker. -/
def copyE : WM ns nr := .seq (cpLoopE T O c) (.seq (.wr O false) (.seq (.fwd O) (.wr O false)))

def copyCost (L : ℕ) : ℕ := L * 14 + 1 + 1 + (1 + 1 + (1 + 1 + 1))

theorem copyE_spec (hTO : T ≠ O) (tw out : List Bool) (σ : WState ns nr) (hc : σ.val c = tw.length)
    (hcc : tw.length ≤ cap) (hT : σ.st T = tw) (hTh : σ.sh T = 0) (hO : σ.st O = out ++ [false])
    (hOh : σ.sh O = out.length) :
    ∃ σ' : WState ns nr, WExec cap (copyE T O c) σ σ' (copyCost tw.length) ∧
      σ'.st O = out ++ frame tw ++ [false] ∧ σ'.sh O = (out ++ frame tw).length ∧
      (∀ s, s ≠ O → σ'.st s = σ.st s) ∧ (∀ s, s ≠ O → s ≠ T → σ'.sh s = σ.sh s) ∧
      (∀ r, r ≠ c → σ'.val r = σ.val r) ∧ σ'.cell = σ.cell := by
  obtain ⟨σ1, Zf, e1, o1, z1, oh1, s1, h1, v1, l1⟩ := cpLoopE_spec cap T O c hTO tw out tw.length 0 [false] σ
    (by omega) hc hcc hT hTh (by rw [hO]; simp) (by simp) (by rw [hOh]; ring)
  have hA : (out ++ frameP tw).length = out.length + 2 * tw.length := by simp
  have e2 := WExec.wr (cap := cap) O false σ1
  rw [o1, oh1, ← hA, wz _ Zf z1] at e2
  have e3 := WExec.fwd (cap := cap) O (σ1.sets O (out ++ frameP tw ++ [false]))
  have e4 := WExec.wr (cap := cap) O false ((σ1.sets O (out ++ frameP tw ++ [false])).seth O
    ((σ1.sets O (out ++ frameP tw ++ [false])).sh O + 1))
  have w4 : writeTapeBit (((σ1.sets O (out ++ frameP tw ++ [false])).seth O
      ((σ1.sets O (out ++ frameP tw ++ [false])).sh O + 1)).st O)
      (((σ1.sets O (out ++ frameP tw ++ [false])).seth O ((σ1.sets O (out ++ frameP tw ++ [false])).sh O + 1)).sh O)
      false = out ++ frameP tw ++ [false] ++ [false] := by
    simp only [WState.seth_st, WState.seth_sh, WState.sets_st, WState.sets_sh, Function.update_self]
    rw [oh1, show out.length + 2 * tw.length + 1 = (out ++ frameP tw ++ [false]).length by simp; omega,
      writeTapeBit_end']
  rw [w4] at e4
  refine ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.sets_st, Function.update_self]
    rw [frame_eq_frameP]
    simp
  · simp only [WState.sets_sh, WState.seth_sh, Function.update_self]
    rw [oh1, frame_eq_frameP]
    simp
    omega
  · intro s hs
    simp only [WState.sets_st, WState.seth_st]
    rw [Function.update_of_ne hs, Function.update_of_ne hs]
    exact s1 s hs
  · intro s hs hsT
    simp only [WState.sets_sh, WState.seth_sh]
    rw [Function.update_of_ne hs]
    exact h1 s hs hsT
  · intro r hr
    simp only [WState.sets_val, WState.seth_val]
    exact v1 r hr
  · simp only [WState.sets_cell, WState.seth_cell]
    exact l1

/-! ## The unit counter -/

def cntLoopE : WM ns nr := .whs K (.seq (.fwd K) (.inc d))

theorem cntLoopE_spec (j : ℕ) (hj : j ≤ cap) :
    ∀ (m i : ℕ) (σ : WState ns nr), i + m = j → σ.st K = List.replicate j true → σ.sh K = i → σ.val d = i →
      ∃ σ' : WState ns nr, WExec cap (cntLoopE K d) σ σ' (m * 7 + 1) ∧ σ'.sh K = j ∧ σ'.val d = j ∧
        σ'.st = σ.st ∧ (∀ s, s ≠ K → σ'.sh s = σ.sh s) ∧ (∀ r, r ≠ d → σ'.val r = σ.val r) ∧ σ'.cell = σ.cell
  | 0, i, σ, hl, hK, hKh, hd => by
    have hi : i = j := by omega
    have hr : wbit σ K = false := by
      unfold wbit
      rw [hK, hKh, hi]
      unfold readTapeBit
      simp
    exact ⟨σ, WExec.cast cap (WExec.whsF hr) rfl (by omega), by rw [hKh, hi], by rw [hd, hi], rfl,
      fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  | m + 1, i, σ, hl, hK, hKh, hd => by
    have hr : wbit σ K = true := by
      unfold wbit
      rw [hK, hKh]
      unfold readTapeBit
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    have e1 := WExec.fwd (cap := cap) K σ
    have e2 := WExec.inc (cap := cap) d (σ.seth K (σ.sh K + 1)) (by simp only [WState.seth_val]; omega)
    obtain ⟨σ2, e3, h3, d3, s3, o3, v3, l3⟩ := cntLoopE_spec j hj m (i + 1)
      ((σ.seth K (σ.sh K + 1)).setv d ((σ.seth K (σ.sh K + 1)).val d + 1)) (by omega) (by simpa using hK)
      (by simp [hKh]) (by simp [hd])
    refine ⟨σ2, WExec.cast cap (WExec.whsT hr (WExec.seq e1 e2) e3) rfl (by ring_nf; omega), h3, d3, ?_, ?_, ?_, ?_⟩
    · rw [s3]; rfl
    · intro s hs
      rw [o3 s hs]
      simp only [WState.setv_sh, WState.seth_sh]
      rw [Function.update_of_ne hs]
    · intro r hr
      rw [v3 r hr]
      simp only [WState.setv_val, WState.seth_val]
      rw [Function.update_of_ne hr]
    · rw [l3]; rfl

/-- **The unit counter advanced**: to the end, one more mark, back. -/
def incE : WM ns nr := .seq (cntLoopE K d) (.seq (.wr K true) (WM.rewind K d))

def incCostE (j : ℕ) : ℕ := j * 7 + 1 + 1 + (1 + 1 + (5 * j + 1))

theorem incE_spec (j : ℕ) (hj : j + 1 ≤ cap) (σ : WState ns nr) (hK : σ.st K = List.replicate j true)
    (hKh : σ.sh K = 0) (hd : σ.val d = 0) :
    ∃ σ' : WState ns nr, WExec cap (incE K d) σ σ' (incCostE j) ∧ σ'.st K = List.replicate (j + 1) true ∧
      σ'.sh K = 0 ∧ (∀ s, s ≠ K → σ'.st s = σ.st s) ∧ (∀ s, s ≠ K → σ'.sh s = σ.sh s) ∧
      (∀ r, σ'.val r = σ.val r) ∧ σ'.cell = σ.cell := by
  obtain ⟨σ1, e1, h1, d1, s1, o1, v1, l1⟩ := cntLoopE_spec cap K d j (by omega) j 0 σ (by omega) hK hKh hd
  have e2 := WExec.wr (cap := cap) K true σ1
  have hw : writeTapeBit (List.replicate j true) j true = List.replicate (j + 1) true := by
    have := writeTapeBit_end' (List.replicate j true) true
    rw [List.length_replicate] at this
    rw [this, List.replicate_succ']
  rw [s1, h1, hK, hw] at e2
  have e3 := wrewind_spec cap K d j (σ1.sets K (List.replicate (j + 1) true))
    (by simpa using d1) (by simp only [WState.sets_val]; omega)
  refine ⟨_, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st, WState.setv_st, WState.sets_st, Function.update_self]
  · simp only [WState.seth_sh, Function.update_self, WState.setv_sh, WState.sets_sh]
    rw [h1]
    simp
  · intro s hs
    simp only [WState.seth_st, WState.setv_st, WState.sets_st]
    rw [Function.update_of_ne hs, s1]
  · intro s hs
    simp only [WState.seth_sh, WState.setv_sh, WState.sets_sh]
    rw [Function.update_of_ne hs, o1 s hs]
  · intro r
    simp only [WState.setv_val, WState.seth_val, WState.sets_val]
    by_cases hr : r = d
    · subst hr
      rw [Function.update_self, hd]
    · rw [Function.update_of_ne hr, v1 r hr]
  · simp only [WState.seth_cell, WState.setv_cell, WState.sets_cell]
    exact l1

/-! ## The emission -/

end Gen

end NearCubicWires.WireExponent3_5.FinalPass.TabW
