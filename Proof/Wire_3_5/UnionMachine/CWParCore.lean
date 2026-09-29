import Proof.Wire_3_5.UnionMachine.CWParLoop

/-! # C6 front, U5, the code writers: the parity writer's core, for any top

The parity writer (P3:3092-3094) is four machines on one bank (`1300 + tT` tapes): the prefix (`CWParPre.preM`: the
shared codes and counts from the bitmap on tape `0`), the bottoms loop (`CWParLoop.loopM C`), a top machine (either
class mode's, `tT` tapes, reading the count word on its tape `0`, writing the top's and the tag's codes on its tapes
`aT`, `bT`), and the suffix (`CWParSuf.sufM`: the circuit code's `natWord` on tape `1`).

**`parCore_step`**: from `frame l` on tape `0`, the output tape holds
`frame (natWord (sufCode (accOf (WLv l) (P3v l) k) k topv tagv))`, `k = l.count true`, for any top machine whose run
is given (`htop`) and any capacity that dominates the loop (`hcw`, `hcwT`, `hlen`).

Paper quantity of the main type: the code of the encoding parity atom, as `natWord`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParCore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParRound
open NearCubicWires.WireExponent3_5.UnionMachine.CWParPre (preM preIn preCost pre_step WLv P3v)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParLoop (loopM loopIn loopCost loop_step)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParSuf (sufM sufIn sufCost suf_step sufCode)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-! ## The layout -/

def preS (tT : ℕ) (j : Fin 344) : Fin (1300 + tT) := ⟨if j.val = 0 then 0 else j.val + 1, by split_ifs <;> omega⟩
def loopS (tT : ℕ) (j : Fin 396) : Fin (1300 + tT) :=
  ⟨if j.val = 0 then 135 else if j.val = 1 then 341 else if j.val = 332 then 6 else if j.val = 333 then 343
    else if j.val < 332 then j.val + 343 else j.val + 341, by split_ifs <;> omega⟩
def topS (tT : ℕ) (j : Fin tT) : Fin (1300 + tT) := ⟨if j.val = 0 then 6 else 1300 + j.val, by split_ifs <;> omega⟩
def sufS (tT aT bT : ℕ) (haTb : aT < tT) (hbTb : bT < tT) (j : Fin 571) : Fin (1300 + tT) :=
  ⟨if j.val = 0 then 345 else if j.val = 1 then 6 else if j.val = 2 then 346 else if j.val = 3 then 347
    else if j.val = 4 then 1300 + aT else if j.val = 5 then 1300 + bT else if j.val = 6 then 1 else j.val + 730,
    by split_ifs <;> omega⟩

theorem preS_inj (tT : ℕ) : Function.Injective (preS tT) := by
  intro a b h; have hv := congrArg Fin.val h; simp only [preS] at hv; apply Fin.ext; split_ifs at hv <;> omega
set_option maxHeartbeats 4000000 in
theorem loopS_inj (tT : ℕ) : Function.Injective (loopS tT) := by
  intro a b h; have hv := congrArg Fin.val h; simp only [loopS] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem topS_inj (tT : ℕ) : Function.Injective (topS tT) := by
  intro a b h; have hv := congrArg Fin.val h; simp only [topS] at hv; apply Fin.ext; split_ifs at hv <;> omega
set_option maxHeartbeats 4000000 in
theorem sufS_inj (tT aT bT : ℕ) (haT : 1 ≤ aT) (hbT : 1 ≤ bT) (haTb : aT < tT) (hbTb : bT < tT) (hab : aT ≠ bT) :
    Function.Injective (sufS tT aT bT haTb hbTb) := by
  intro a b h; have hv := congrArg Fin.val h; simp only [sufS] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega

/-! ## The machine and its run -/

/-- **The parity writer's core** at the capacity coefficient `C`, with the top machine `topM`. -/
noncomputable def parCoreM (C : ℕ) {tT sT : ℕ} (topM : Machine tT sT) (aT bT : ℕ) (haTb : aT < tT) (hbTb : bT < tT) :=
  Composition.machine (RecoveryFocus.machine (preS tT) preM)
    (Composition.machine (RecoveryFocus.machine (loopS tT) (loopM C))
      (Composition.machine (RecoveryFocus.machine (topS tT) topM)
        (RecoveryFocus.machine (sufS tT aT bT haTb hbTb) sufM)))

/-- The core's entry: the bitmap framed on tape `0`. -/
def coreIn (tT : ℕ) (l : List Bool) : Fin (1300 + tT) → List Bool := fun t => if t.val = 0 then frame l else []

/-- A top machine's entry: the count word on tape `0`. -/
def topIn (tT k : ℕ) : Fin tT → List Bool := fun t => if t.val = 0 then CompareMachine.word k else []

theorem zeroH' {N t : ℕ} (sl : Fin t → Fin N) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- **The parity writer's core run.** -/
theorem parCore_step (l : List Bool) (C cw : ℕ)
    (hcw : ∀ j < l.count true, roundPCost (WLv l) (P3v l) j (accOf (WLv l) (P3v l) j) ≤ cw)
    (hcwT : cw + 1 ≤ BlockPlatform.UnaryCalc.value 24 C l.length)
    (hlen : ∀ j ≤ l.count true, ∀ t, (Qp (WLv l) (P3v l) j t).length ≤ BlockPlatform.UnaryCalc.value 24 C l.length)
    {tT sT : ℕ} (topM : Machine tT sT) (aT bT : ℕ) (haT : 1 ≤ aT) (hbT : 1 ≤ bT) (haTb : aT < tT) (hbTb : bT < tT)
    (hab : aT ≠ bT) (topv tagv ctop : ℕ)
    (htop : ∃ out : Fin tT → List Bool, Step topM ctop (fun _ => 0) (topIn tT (l.count true)) (fun _ => 0) out ∧
      out ⟨0, by omega⟩ = CompareMachine.word (l.count true) ∧ out ⟨aT, haTb⟩ = frame topv.bits ∧
      out ⟨bT, hbTb⟩ = frame tagv.bits) :
    ∃ out : Fin (1300 + tT) → List Bool,
      Step (parCoreM C topM aT bT haTb hbTb)
        (preCost l + 1 + (loopCost (l.count true) l.length C cw + 1 + (ctop + 1 +
          sufCost (accOf (WLv l) (P3v l) (l.count true)) (l.count true) topv tagv)))
        (fun _ => 0) (coreIn tT l) (fun _ => 0) out ∧
      out ⟨0, by omega⟩ = frame l ∧
      out ⟨1, by omega⟩ = frame (natWord (sufCode (accOf (WLv l) (P3v l) (l.count true)) (l.count true) topv tagv)) := by
  set k := l.count true with hk
  set B0 := coreIn tT l with hB0
  have f0 : ∀ t : Fin (1300 + tT), t.val ≠ 0 → B0 t = [] := fun t ht => by simp only [hB0, coreIn]; rw [if_neg ht]
  -- 1: the prefix
  obtain ⟨o1, s1, p0, p134, p340, -, p5, p342⟩ := pre_step l
  have d1 := s1.dock (preS tT) (preS_inj tT) (fun _ => 0) B0 (fun _ => rfl) (by
    intro j
    show B0 (preS tT j) = preIn l j
    by_cases h0 : j.val = 0
    · rw [show preS tT j = ⟨0, by omega⟩ from Fin.ext (by simp [preS, h0])]; simp [hB0, coreIn, preIn, h0]
    · rw [f0 _ (by simp only [preS]; rw [if_neg h0]; omega)]; simp [preIn, h0])
  rw [zeroH'] at d1
  set B1 := install (preS tT) B0 o1 with hB1
  have b1h : ∀ j, B1 (preS tT j) = o1 j := fun j => install_slot _ (preS_inj tT) _ _ _
  have b1 : ∀ t : Fin (1300 + tT), (t.val = 1 ∨ 345 ≤ t.val) → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [preS] at hv; have := j.isLt; split_ifs at hv <;> omega)
  -- 2: the bottoms loop
  obtain ⟨o2, s2, q0, q1, q2, q3, q4, q332⟩ := loop_step (WLv l) (P3v l) k l.length C cw hcw hcwT hlen
  have d2 := s2.dock (loopS tT) (loopS_inj tT) (fun _ => 0) B1 (fun _ => rfl) (by
    intro j
    show B1 (loopS tT j) = loopIn (frame (WLv l).bits) (frame (P3v l).bits) (CompareMachine.word k)
      (List.replicate l.length true) j
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · rw [show loopS tT j = preS tT 134 from Fin.ext (by simp [loopS, preS, h0]), b1h, p134]; simp [loopIn, h0]
    · by_cases h1 : j.val = 1
      · rw [show loopS tT j = preS tT 340 from Fin.ext (by simp [loopS, preS, h1]), b1h, p340]; simp [loopIn, h1]
      · by_cases h2 : j.val = 332
        · rw [show loopS tT j = preS tT 5 from Fin.ext (by simp [loopS, preS, h2]), b1h, p5]; simp [loopIn, h2]; rfl
        · by_cases h3 : j.val = 333
          · rw [show loopS tT j = preS tT 342 from Fin.ext (by simp [loopS, preS, h3]), b1h, p342]
            simp [loopIn, h3]
          · rw [b1 _ (by simp only [loopS]; split_ifs <;> omega), f0 _ (by simp only [loopS]; split_ifs <;> omega)]
            simp [loopIn, h0, h1, h2, h3])
  rw [zeroH'] at d2
  set B2 := install (loopS tT) B1 o2 with hB2
  have b2h : ∀ j, B2 (loopS tT j) = o2 j := fun j => install_slot _ (loopS_inj tT) _ _ _
  have b2 : ∀ t : Fin (1300 + tT), (t.val < 6 ∨ (6 < t.val ∧ t.val < 135) ∨ 737 ≤ t.val) → B2 t = B1 t :=
    fun t ht => install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [loopS] at hv; have := j.isLt; split_ifs at hv <;> omega)
  -- 3: the top
  obtain ⟨o3, s3, t0, tA, tB⟩ := htop
  have d3 := s3.dock (topS tT) (topS_inj tT) (fun _ => 0) B2 (fun _ => rfl) (by
    intro j
    show B2 (topS tT j) = topIn tT k j
    by_cases h0 : j.val = 0
    · rw [show topS tT j = loopS tT 332 from Fin.ext (by simp [topS, loopS, h0]), b2h, q332]; simp [topIn, h0]
    · rw [b2 _ (by simp only [topS]; rw [if_neg h0]; omega), b1 _ (by simp only [topS]; rw [if_neg h0]; omega),
        f0 _ (by simp only [topS]; rw [if_neg h0]; omega)]
      simp [topIn, h0])
  rw [zeroH'] at d3
  set B3 := install (topS tT) B2 o3 with hB3
  have b3h : ∀ j, B3 (topS tT j) = o3 j := fun j => install_slot _ (topS_inj tT) _ _ _
  have b3 : ∀ t : Fin (1300 + tT), (t.val ≠ 6 ∧ t.val ≤ 1300) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [topS] at hv; split_ifs at hv <;> omega)
  -- 4: the suffix
  obtain ⟨o4, s4, w6⟩ := suf_step (accOf (WLv l) (P3v l) k) k topv tagv (by simp [accOf])
  have d4 := s4.dock (sufS tT aT bT haTb hbTb) (sufS_inj tT aT bT haT hbT haTb hbTb hab) (fun _ => 0) B3
    (fun _ => rfl) (by
    intro j
    show B3 (sufS tT aT bT haTb hbTb j) = sufIn ((accOf (WLv l) (P3v l) k).flatMap frame) (CompareMachine.word k)
      (sgl k.bits) (CompareMachine.word k.bits.length) (frame topv.bits) (frame tagv.bits) j
    have hj := j.isLt
    by_cases h0 : j.val = 0
    · rw [show sufS tT aT bT haTb hbTb j = loopS tT 2 from Fin.ext (by simp [sufS, loopS, h0]), b3 _ (by
        simp [loopS]), b2h, q2]; simp [sufIn, h0]
    · by_cases h1 : j.val = 1
      · rw [show sufS tT aT bT haTb hbTb j = topS tT ⟨0, by omega⟩ from Fin.ext (by simp [sufS, topS, h1]), b3h, t0]
        simp [sufIn, h1]
      · by_cases h2 : j.val = 2
        · rw [show sufS tT aT bT haTb hbTb j = loopS tT 3 from Fin.ext (by simp [sufS, loopS, h2]), b3 _ (by
            simp [loopS]), b2h, q3]; simp [sufIn, h2]
        · by_cases h3 : j.val = 3
          · rw [show sufS tT aT bT haTb hbTb j = loopS tT 4 from Fin.ext (by simp [sufS, loopS, h3]), b3 _ (by
              simp [loopS]), b2h, q4]; simp [sufIn, h3]
          · by_cases h4 : j.val = 4
            · rw [show sufS tT aT bT haTb hbTb j = topS tT ⟨aT, haTb⟩ from Fin.ext (by
                simp only [sufS, topS]; split_ifs <;> omega), b3h, tA]; simp [sufIn, h4]
            · by_cases h5 : j.val = 5
              · rw [show sufS tT aT bT haTb hbTb j = topS tT ⟨bT, hbTb⟩ from Fin.ext (by
                  simp only [sufS, topS]; split_ifs <;> omega), b3h, tB]; simp [sufIn, h5]
              · rw [b3 _ (by simp only [sufS]; split_ifs <;> omega), b2 _ (by simp only [sufS]; split_ifs <;> omega),
                  b1 _ (by simp only [sufS]; split_ifs <;> omega), f0 _ (by simp only [sufS]; split_ifs <;> omega)]
                simp [sufIn, h0, h1, h2, h3, h4, h5])
  rw [zeroH'] at d4
  set B4 := install (sufS tT aT bT haTb hbTb) B3 o4 with hB4
  have b4 : ∀ t : Fin (1300 + tT), t.val = 0 → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [sufS] at hv; split_ifs at hv <;> omega)
  have run := d1.seq (d2.seq (d3.seq d4))
  have run' : Step (parCoreM C topM aT bT haTb hbTb) _ (fun _ => 0) B0 (fun _ => 0) B4 := run
  refine ⟨B4, run'.enlarge (le_refl _), ?_, ?_⟩
  · rw [b4 _ rfl, b3 _ (by simp), b2 _ (by simp), show (⟨0, _⟩ : Fin (1300 + tT)) = preS tT 0 from
      Fin.ext (by simp [preS]), b1h, p0]
  · rw [show (⟨1, _⟩ : Fin (1300 + tT)) = sufS tT aT bT haTb hbTb 6 from Fin.ext (by simp [sufS])]
    exact (install_slot _ (sufS_inj tT aT bT haT hbT haTb hbTb hab) B3 o4 6).trans w6

end NearCubicWires.WireExponent3_5.UnionMachine.CWParCore
