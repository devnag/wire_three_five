import Proof.SourceAssembly.SourceFactorSelMetaKit
import Proof.Packets.PacketsClog
import Proof.Packets.PacketsGlueMetaMul
import Proof.MachineModel.OrdinaryMatrixBucketDivide

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceFactorSel.MetaPipe
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceStart.Regs
noncomputable section

/-! ## 1. `⌈log₂(x+1)⌉` -/

/-- The masked `Clog` machine. -/
def clogM := MaskedReset.machine NearCubicWires.PacketsGlue.Clog.machine (fun _ => true)

/-- `Clog` at `x`, masked, from the empty-log entry. -/
theorem clog_masked (x : ℕ) : ∃ tout : Fin (4 + 1) → List Bool,
    Step clogM (2 * (30 * (x + 1)) + 2) (fun _ => 0)
      (Fin.addCases (![List.replicate x true, [], [], []] : Fin 4 → List Bool) (fun _ : Fin 1 => ([] : List Bool)))
      (fun _ => 0) tout ∧ tout 1 = List.replicate (Nat.clog 2 x) true := by
  obtain ⟨n, H1, A1, hs, hv, hn⟩ := NearCubicWires.PacketsGlue.Clog.run x
  obtain ⟨k, hm⟩ := NearCubicWires.SourceStart.Stages.mask0 (hs.enlarge hn)
  refine ⟨_, hm, ?_⟩
  rw [← hv]
  rfl

/-- Local naming of the two clog stages. -/
def cA (j : Fin (2 + 1)) : Option (Fin 11) := if j.val = 0 then some 0 else if j.val = 1 then some 2 else none
def cB (j : Fin (4 + 1)) : Option (Fin 11) := if j.val = 0 then some 2 else if j.val = 1 then some 1 else none

theorem cA_hs : 3 + (plusOp 1).n ≤ 11 := by
  show 3 + (2 + 1) ≤ 11
  decide

theorem cB_hs : 6 + (4 + 1) ≤ 11 := by decide

theorem cA_ne1 : ∀ j : Fin (2 + 1), cA j ≠ some 1 := by
  intro j
  fin_cases j <;> simp [cA]

theorem cB_ne0 : ∀ j : Fin (4 + 1), cB j ≠ some 0 := by
  intro j
  fin_cases j <;> simp [cB]

/-- **The `clog₂(x+1)` operation.** -/
def clog1Op : UOp (fun x => Nat.clog 2 (x + 1)) where
  n := 11
  st := _
  M := Composition.machine (RecoveryFocus.machine (nslot cA 3 cA_hs) (plusOp 1).M)
    (RecoveryFocus.machine (nslot cB 6 cB_hs) clogM)
  i := 0
  o := 1
  hio := by decide
  cost := fun x => (plusOp 1).cost x + 1 + (2 * (30 * (x + 1 + 1)) + 2)
  run := fun x => by
    obtain ⟨tA, hA, hA0, hA1⟩ := (plusOp 1).run x
    obtain ⟨E1, s1, n1, o1, b1⟩ := nstage (R := 0) hA cA 3 cA_hs
      (by intro i j r hi hj; fin_cases i <;> fin_cases j <;> simp [cA] at hi hj ⊢ <;> subst hi <;> simp at hj)
      (by intro j r h; fin_cases j <;> simp [cA] at h <;> subst h <;> decide)
      (in1 11 0 x)
      (by intro j r h; fin_cases j <;> simp [cA] at h <;> subst h <;> (rw [ZeroPadding.pad_zero]; rfl))
      (by intro j h; fin_cases j <;> simp [cA] at h; rfl)
      (by
        intro y hy
        have hy0 : y ≠ 0 := fun e => by rw [e] at hy; exact absurd hy (by decide)
        unfold in1
        rw [if_neg hy0]
        rfl)
    have e10 : E1 0 = List.replicate x true := by
      rw [n1 (plusOp 1).i 0 rfl, ZeroPadding.pad_zero]
      exact hA0
    have e12 : E1 2 = List.replicate (x + 1) true := by
      rw [n1 (plusOp 1).o 2 rfl, ZeroPadding.pad_zero]
      exact hA1
    have e11 : E1 1 = [] := by
      rw [o1 1 (by decide) cA_ne1]
      rfl
    obtain ⟨tB, hB, hB1⟩ := clog_masked (x + 1)
    obtain ⟨E2, s2, n2, o2, _⟩ := nstage (R := 0) hB cB 6 cB_hs
      (by intro i j r hi hj; fin_cases i <;> fin_cases j <;> simp [cB] at hi hj ⊢ <;> subst hi <;> simp at hj)
      (by intro j r h; fin_cases j <;> simp [cB] at h <;> subst h <;> decide)
      E1
      (by
        intro j r h
        fin_cases j <;> simp [cB] at h <;> subst h
        · rw [e12, ZeroPadding.pad_zero]
          rfl
        · rw [e11, ZeroPadding.pad_zero]
          rfl)
      (by intro j h; fin_cases j <;> simp [cB] at h <;> rfl)
      (fun y hy => b1 y (by show 3 + (2 + 1) ≤ y.val; omega))
    refine ⟨E2, s1.seq s2, ?_, ?_⟩
    · rw [o2 0 (by decide) cB_ne0, e10]
    · rw [n2 1 1 rfl, ZeroPadding.pad_zero]
      exact hB1

/-! ## 2. `⌊x/d⌋` -/

theorem divide_step (x d : ℕ) (hd : 0 < d) : ∃ tout : Fin (3 + 1) → List Bool,
    Step MatrixBucketDivide.machine (8 * x + 6) (fun _ => 0) (MatrixBucketDivide.resetInput x d) (fun _ => 0) tout ∧
    tout 0 = List.replicate x true ∧ tout 1 = UnaryTemplate.tape d ∧ tout 2 = List.replicate (x / d) true := by
  obtain ⟨actual, hr, h0, h1, h2, hh, _⟩ := MatrixBucketDivide.divide_run x d hd
  refine ⟨actual.final.tapes, Step.of_run (r := actual) hr (funext hh) rfl, h0, h1, h2⟩

/-- Local naming of the two division stages. -/
def dA (j : Fin 3) : Option (Fin 11) := if j.val = 0 then some 1 else if j.val = 1 then some 3 else none
def dB (j : Fin (3 + 1)) : Option (Fin 11) :=
  if j.val = 0 then some 0 else if j.val = 1 then some 3 else if j.val = 2 then some 2 else none

theorem dA_hs : 4 + 3 ≤ 11 := by decide
theorem dB_hs : 7 + (3 + 1) ≤ 11 := by decide

/-- **The division operation** (positive divisor). -/
def divOp : BOp (fun x d => x / d) (fun _ d => 0 < d) where
  n := 11
  st := _
  M := Composition.machine
    (RecoveryFocus.machine (nslot dA 4 dA_hs) (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
    (RecoveryFocus.machine (nslot dB 7 dB_hs) MatrixBucketDivide.machine)
  i1 := 0
  i2 := 1
  o := 2
  h12 := by decide
  h1o := by decide
  h2o := by decide
  cost := fun x d => (2 * d + 8) + 1 + (8 * x + 6)
  run := fun x d hd => by
    have hA := NearCubicWires.PacketsGlue.RequestMeta.tpl_step d
    obtain ⟨E1, s1, n1, o1, b1⟩ := nstage (R := 0) hA dA 4 dA_hs
      (by intro i j r hi hj; fin_cases i <;> fin_cases j <;> simp [dA] at hi hj ⊢ <;> subst hi <;> simp at hj)
      (by intro j r h; fin_cases j <;> simp [dA] at h <;> subst h <;> decide)
      (in2 11 0 1 x d)
      (by intro j r h; fin_cases j <;> simp [dA] at h <;> subst h <;> (rw [ZeroPadding.pad_zero]; rfl))
      (by intro j h; fin_cases j <;> simp [dA] at h; rfl)
      (by
        intro y hy
        have hy0 : y ≠ 0 := fun e => by rw [e] at hy; exact absurd hy (by decide)
        have hy1 : y ≠ 1 := fun e => by rw [e] at hy; exact absurd hy (by decide)
        unfold in2
        rw [if_neg hy0, if_neg hy1]
        rfl)
    have e10 : E1 0 = List.replicate x true := by
      rw [o1 0 (by decide) (by intro j; fin_cases j <;> simp [dA])]
      rfl
    have e11 : E1 1 = List.replicate d true := by
      rw [n1 0 1 rfl, ZeroPadding.pad_zero]
      rfl
    have e12 : E1 2 = [] := by
      rw [o1 2 (by decide) (by intro j; fin_cases j <;> simp [dA])]
      rfl
    have e13 : E1 3 = UnaryTemplate.tape d := by
      rw [n1 1 3 rfl, ZeroPadding.pad_zero]
      rfl
    obtain ⟨tB, hB, hB0, _, hB2⟩ := divide_step x d hd
    obtain ⟨E2, s2, n2, o2, _⟩ := nstage (R := 0) hB dB 7 dB_hs
      (by intro i j r hi hj; fin_cases i <;> fin_cases j <;> simp [dB] at hi hj ⊢ <;> subst hi <;> simp at hj)
      (by intro j r h; fin_cases j <;> simp [dB] at h <;> subst h <;> decide)
      E1
      (by
        intro j r h
        fin_cases j <;> simp [dB] at h <;> subst h
        · rw [e10, ZeroPadding.pad_zero]
          rfl
        · rw [e13, ZeroPadding.pad_zero]
          rfl
        · rw [e12, ZeroPadding.pad_zero]
          rfl)
      (by intro j h; fin_cases j <;> simp [dB] at h; rfl)
      (fun y hy => b1 y (by omega))
    refine ⟨E2, s1.seq s2, ?_, ?_, ?_⟩
    · rw [n2 0 0 rfl, ZeroPadding.pad_zero]
      exact hB0
    · rw [o2 1 (by decide) (by intro j; fin_cases j <;> simp [dB]), e11]
    · rw [n2 2 2 rfl, ZeroPadding.pad_zero]
      exact hB2

end
end NearCubicWires.SourceFactorSel.MetaPipe

