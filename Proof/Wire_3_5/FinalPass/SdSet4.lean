import Proof.Wire_3_5.FinalPass.SdSet3

/-! # S4 (the seeds phase), part 31: the evaluator's numbers and the teardown, on the body (P3:3170-3178)

**`ldMode`**: the mode bit (word `13`'s first bit: THR's primes list starts with `1`, SYM's word `13` is blank)
selects the evaluator's numbers: THR's (word `15`, into registers `1 … 4`, **`ldMode_thr`**) or SYM's (word
`16 + nw`, into `220 + i`, **`ldMode_sym`**). **`tdW`**: the seeds phase's nonzero registers cleared (the star
parameters, the digits, the flags, the tables' position, both evaluators' numbers; **`tdW_spec`**).

Paper quantity of the main type: the evaluator's numbers `thrNums`/`E.nums` in its registers (the per-point sums'
parameters, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.PrimAsm

section Body
variable {nw nn nsc nrs : ℕ}

/-- THR's number registers `1 … 4`. -/
def thrRegs : List (Fin (bnr nn nrs)) := [brg 1 (by omega), brg 2 (by omega), brg 3 (by omega), brg 4 (by omega)]

/-- SYM's number registers `220 + i`. -/
def symRegs : List (Fin (bnr nn nrs)) := List.ofFn fun i : Fin nn => (⟨220 + i.val, by unfold bnr; omega⟩ : Fin (bnr nn nrs))

theorem symReg_eq (i : Fin nn) : (⟨220 + i.val, by unfold bnr; omega⟩ : Fin (bnr nn nrs)) = RSe (.inr (.inl i)) := rfl

def tNumsT : Fin (bns nw nsc + 1) := bst 45 (by omega)
def tNumsS : Fin (bns nw nsc + 1) := ⟨46 + nw, by unfold bns; omega⟩
def tMode : Fin (bns nw nsc + 1) := bst 43 (by omega)

theorem thrRegs_nodup : (thrRegs : List (Fin (bnr nn nrs))).Nodup := by simp [thrRegs, brg_iff]

theorem symRegs_nodup : (symRegs : List (Fin (bnr nn nrs))).Nodup := by
  rw [symRegs, List.nodup_ofFn]
  intro a b h
  exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)

theorem symRegs_mem (q : Fin (bnr nn nrs)) (hq : q ∈ (symRegs : List (Fin (bnr nn nrs)))) : 220 ≤ q.val := by
  rw [symRegs, List.mem_ofFn] at hq
  obtain ⟨i, rfl⟩ := hq
  exact Nat.le_add_right _ _

/-- The evaluator's numbers, by mode. -/
def ldMode : BP nw nn nsc nrs := .ifs tMode (ldNums tNumsT sC thrRegs) (ldNums tNumsS sC symRegs)

theorem ldMode_thr (cap : ℕ) (σ : BS nw nn nsc nrs) (vs : List ℕ) (hl : vs.length = 4)
    (hb : readTapeBit (σ.st tMode) (σ.sh tMode) = true) (hst : σ.st tNumsT = Data.unaryList vs)
    (hsh : σ.sh tNumsT = 0) (hz : ∀ r ∈ (thrRegs : List (Fin (bnr nn nrs))), σ.val r = 0) (hc0 : σ.val sC = 0)
    (hc : (Data.unaryList vs).length ≤ cap) :
    ∃ σ2 : BS nw nn nsc nrs, ∃ m, WExec cap ldMode σ σ2 m ∧ m ≤ 16 * (Data.unaryList vs).length + 3 ∧
      σ2.st = σ.st ∧ σ2.sh = σ.sh ∧ (∀ k : Fin 4, σ2.val (brg (1 + k.val) (by omega)) = vs.getD k.val 0) ∧
      (∀ q, q ∉ (thrRegs : List (Fin (bnr nn nrs))) → σ2.val q = σ.val q) ∧ σ2.cell = σ.cell := by
  obtain ⟨σ2, e, s2, h2, v2, o2, l2⟩ := ldNums_spec cap tNumsT sC thrRegs vs σ (by rw [hl]; rfl)
    (by simp [thrRegs, sC, brg_iff]) thrRegs_nodup hz hst hsh hc0 hc
  refine ⟨σ2, _, WExec.ifsT hb e, by omega, s2, h2, fun k => ?_, o2, l2⟩
  have := v2 ⟨k.val, by simp [thrRegs]⟩
  fin_cases k <;> exact this

theorem ldMode_sym (cap : ℕ) (σ : BS nw nn nsc nrs) (vs : List ℕ) (hl : vs.length = nn)
    (hb : readTapeBit (σ.st tMode) (σ.sh tMode) = false) (hst : σ.st tNumsS = Data.unaryList vs)
    (hsh : σ.sh tNumsS = 0) (hz : ∀ r ∈ (symRegs : List (Fin (bnr nn nrs))), σ.val r = 0) (hc0 : σ.val sC = 0)
    (hc : (Data.unaryList vs).length ≤ cap) :
    ∃ σ2 : BS nw nn nsc nrs, ∃ m, WExec cap ldMode σ σ2 m ∧ m ≤ 16 * (Data.unaryList vs).length + 3 ∧
      σ2.st = σ.st ∧ σ2.sh = σ.sh ∧ (∀ i : Fin nn, σ2.val (RSe (.inr (.inl i))) = vs.getD i.val 0) ∧
      (∀ q, q ∉ (symRegs : List (Fin (bnr nn nrs))) → σ2.val q = σ.val q) ∧ σ2.cell = σ.cell := by
  obtain ⟨σ2, e, s2, h2, v2, o2, l2⟩ := ldNums_spec cap tNumsS sC symRegs vs σ (by rw [symRegs, List.length_ofFn, hl])
    (fun r hr => by
      have := symRegs_mem r hr
      intro h
      rw [h] at this
      simp [sC, brg] at this)
    symRegs_nodup hz hst hsh hc0 hc
  refine ⟨σ2, _, WExec.ifsF hb e, by omega, s2, h2, fun i => ?_, o2, l2⟩
  have := v2 ⟨i.val, by simp [symRegs]⟩
  simp only [symRegs, List.get_eq_getElem, List.getElem_ofFn] at this
  rw [← symReg_eq]
  exact this

/-- The phase's fixed nonzero registers at the loops' end. -/
def tdFix : List (Fin (bnr nn nrs)) :=
  [ctrR 0, ctrR 1, ctrR 2, ctrR 3, ctrR 4, frD 0, frD 1, frD 2, frD 3, rP 0, rP 1, rgP]

theorem tdFix_nodup : (tdFix : List (Fin (bnr nn nrs))).Nodup := by
  simp [tdFix, ctrR_b, frD_b, rP_b, rgP, brg_iff]

/-- **The teardown**: the fixed registers, THR's numbers, SYM's numbers cleared. -/
def tdW : BP nw nn nsc nrs := .seq (clJobs tdFix) (.seq (clJobs thrRegs) (clJobs symRegs))

theorem tdW_spec (cap : ℕ) (σ : BS nw nn nsc nrs) (hc : ∀ q, σ.val q ≤ cap) :
    ∃ m, WExec cap tdW σ (clApply (clApply (clApply σ tdFix) thrRegs) symRegs) m ∧
      m ≤ (tdFix.map fun r => 3 * σ.val r + 2).sum + (thrRegs.map fun r => 3 * σ.val r + 2).sum +
        (symRegs.map fun r => 3 * σ.val r + 2).sum + 2 := by
  have e1 := clJobs_spec cap tdFix σ tdFix_nodup (fun q _ => hc q)
  have h1 : ∀ q, (clApply σ tdFix).val q ≤ σ.val q := fun q => by
    rw [clApply_val]; dsimp only; split_ifs <;> omega
  have e2 := clJobs_spec cap thrRegs (clApply σ tdFix) thrRegs_nodup (fun q _ => le_trans (h1 q) (hc q))
  have h2 : ∀ q, (clApply (clApply σ tdFix) thrRegs).val q ≤ σ.val q := fun q => by
    rw [clApply_val]; dsimp only; split_ifs <;> [omega; exact h1 q]
  have e3 := clJobs_spec cap symRegs (clApply (clApply σ tdFix) thrRegs) symRegs_nodup
    (fun q _ => le_trans (h2 q) (hc q))
  refine ⟨_, WExec.seq e1 (WExec.seq e2 e3), ?_⟩
  have m2 : (thrRegs.map fun r => 3 * (clApply σ tdFix).val r + 2).sum ≤ (thrRegs.map fun r => 3 * σ.val r + 2).sum :=
    List.sum_le_sum (fun r _ => by have := h1 r; omega)
  have m3 : (symRegs.map fun r => 3 * (clApply (clApply σ tdFix) thrRegs).val r + 2).sum ≤
      (symRegs.map fun r => 3 * σ.val r + 2).sum :=
    List.sum_le_sum (fun r _ => by have := h2 r; omega)
  omega

end Body

end NearCubicWires.WireExponent3_5.FinalPass.Sd
