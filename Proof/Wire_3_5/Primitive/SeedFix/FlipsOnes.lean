import Proof.Wire_3_5.Primitive.SeedFix.FlipsDec
import Proof.Wire_3_5.Selection.ScanW

/-! # FLIPS, part 3: the last-index test (P3:1188-1193)

The flips writer walks the cells' indices `L, R < 2^{kh}` as binary counters (`frame (binary kh ·)`, C1's `incCNT`).
A counter is at its last value exactly when every bit is `1` (`binary_all`); **`onesChk`** scans a framed word and sets
a flag register iff some bit is `0`, then rewinds (`onesChk_spec`).

Paper quantity of the main type: the index test `v + 1 = 2^{kh}` (the last cell of a half). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- **A counter is at its last value iff every bit is `1`.** -/
theorem binary_all (w : ℕ) : ∀ v, v < 2 ^ w → ((binary w v).all id = true ↔ v + 1 = 2 ^ w) := by
  induction w with
  | zero => intro v hv; simp [binary] at hv ⊢; omega
  | succ w ih =>
    intro v hv
    have hp : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    have hv2 : v / 2 < 2 ^ w := by omega
    have e : (binary (w + 1) v).all id = ((v % 2 == 1) && (binary w (v / 2)).all id) := by
      simp [binary]
    rw [e, Bool.and_eq_true, ih (v / 2) hv2]
    constructor
    · rintro ⟨h1, h2⟩
      have : v % 2 = 1 := by simpa using h1
      omega
    · intro h
      refine ⟨by simp; omega, by omega⟩

section Ones
variable {ns nr : ℕ} (cap : ℕ)

/-- Set a `0/1` flag. -/
def setOne (nz : Fin nr) : WM ns nr := .ifr nz .skip (.inc nz)

/-- One pair of the scan: the flag set when the bit is `0`. -/
def onesStep (X : Fin (ns + 1)) (nz scn : Fin nr) : WM ns nr :=
  .seq (.fwd X) (.seq (.ifs X .skip (setOne nz)) (.seq (.fwd X) (.seq (.inc scn) (.inc scn))))

/-- **The last-index test**: `nz := [some bit of the framed word is 0]`, the stream rewound. -/
def onesChk (X : Fin (ns + 1)) (nz scn : Fin nr) : WM ns nr := .seq (.whs X (onesStep X nz scn)) (rew1 X scn)

/-- The flag's value on a prefix. -/
def flagOf (l : List Bool) : ℕ := if l.all id then 0 else 1

theorem flagOf_snoc (l : List Bool) (x : Bool) : flagOf (l ++ [x]) = if x then flagOf l else 1 := by
  unfold flagOf
  cases x <;> simp [List.all_append]

theorem onesLoop_spec (X : Fin (ns + 1)) (nz scn : Fin nr) (hns : nz ≠ scn) (bs rest : List Bool)
    (hcap : 2 * bs.length + 2 ≤ cap) (m : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), k + m = bs.length → σ.st X = frameP bs ++ false :: rest → σ.sh X = 2 * k →
      σ.val nz = flagOf (bs.take k) → σ.val scn = 2 * k →
      ∃ τ, WExec cap (.whs X (onesStep X nz scn)) σ τ (m * 20 + 1) ∧ τ.sh X = 2 * bs.length ∧
        τ.val nz = flagOf bs ∧ τ.val scn = 2 * bs.length ∧ τ.st = σ.st ∧ (∀ i, i ≠ X → τ.sh i = σ.sh i) ∧
        (∀ r, r ≠ nz → r ≠ scn → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have hsn : scn ≠ nz := Ne.symm hns
  induction m with
  | zero =>
    intro k σ hkm hst hsh hnz hsc
    have hk : k = bs.length := by omega
    subst hk
    have hb : wbit σ X = false := by unfold wbit; rw [hst, hsh]; exact rd_end bs rest
    rw [List.take_of_length_le (le_refl _)] at hnz
    exact ⟨σ, WExec.mono (WExec.whsF hb) (by omega), hsh, hnz, hsc, rfl, fun _ _ => rfl, fun _ _ _ => rfl, rfl⟩
  | succ m ih =>
    intro k σ hkm hst hsh hnz hsc
    have hk : k < bs.length := by omega
    have hb : wbit σ X = true := by unfold wbit; rw [hst, hsh]; exact readTapeBit_frameP_marker bs _ k hk
    have s1 := WExec.fwd (cap := cap) X σ
    obtain ⟨σ1, hσ1⟩ : ∃ x, x = σ.seth X (σ.sh X + 1) := ⟨_, rfl⟩
    rw [← hσ1] at s1
    have b1 : wbit σ1 X = bs.getD k false := by
      have e : wbit σ1 X = readTapeBit (σ.st X) (2 * k + 1) := by
        unfold wbit; rw [hσ1]; simp [WState.seth, hsh]
      rw [e, hst]; exact readTapeBit_frameP bs _ k hk
    have hflag : flagOf (bs.take (k + 1)) = if bs.getD k false then flagOf (bs.take k) else 1 := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      simp only [Option.toList_some]
      rw [flagOf_snoc, ← List.getD_eq_getElem _ false hk]
    -- the flag
    obtain ⟨σ2, s2, f2⟩ : ∃ σ2, WExec cap (.ifs X .skip (setOne nz)) σ1 σ2 5 ∧
        σ2 = σ1.setv nz (flagOf (bs.take (k + 1))) := by
      rw [hflag]
      cases hbit : bs.getD k false
      · refine ⟨σ1.setv nz 1, ?_, rfl⟩
        have hv1 : σ1.val nz = flagOf (bs.take k) := by rw [hσ1]; exact hnz
        rcases Nat.lt_or_ge (σ1.val nz) 1 with h0 | h1
        · have h0' : σ1.val nz = 0 := by omega
          have t := WExec.inc (cap := cap) nz σ1 (by omega)
          rw [h0'] at t
          exact WExec.mono (WExec.ifsF (by rw [b1, hbit]) (WExec.ifrF h0' t)) (by omega)
        · have hle : flagOf (bs.take k) ≤ 1 := by unfold flagOf; split_ifs <;> omega
          have h1' : σ1.val nz = 1 := by omega
          have e : σ1.setv nz 1 = σ1 := by rw [← h1', setv_self]
          rw [e]
          exact WExec.mono (WExec.ifsF (by rw [b1, hbit]) (WExec.ifrT (by omega) (WExec.skip σ1))) (by omega)
      · refine ⟨σ1, ?_, ?_⟩
        · exact WExec.mono (WExec.ifsT (by rw [b1, hbit]) (WExec.skip σ1)) (by omega)
        · rw [if_pos rfl]
          have hv1 : σ1.val nz = flagOf (bs.take k) := by rw [hσ1]; exact hnz
          rw [← hv1]
          exact (setv_self σ1 nz).symm
    have s3 := WExec.fwd (cap := cap) X σ2
    have v2 : σ2.val scn = 2 * k := by rw [f2, hσ1]; simp [WState.setv, WState.seth, Function.update_apply, hsn, hsc]
    have s4 := WExec.inc (cap := cap) scn (σ2.seth X (σ2.sh X + 1)) (by show σ2.val scn < cap; omega)
    have s5 := WExec.inc (cap := cap) scn ((σ2.seth X (σ2.sh X + 1)).setv scn ((σ2.seth X (σ2.sh X + 1)).val scn + 1))
      (by simp [WState.setv, WState.seth, v2]; omega)
    obtain ⟨σ5, hσ5⟩ : ∃ x, x = ((σ2.seth X (σ2.sh X + 1)).setv scn ((σ2.seth X (σ2.sh X + 1)).val scn + 1)).setv scn
        (((σ2.seth X (σ2.sh X + 1)).setv scn ((σ2.seth X (σ2.sh X + 1)).val scn + 1)).val scn + 1) := ⟨_, rfl⟩
    rw [← hσ5] at s5
    have f5 : σ5.st = σ.st ∧ σ5.sh X = 2 * (k + 1) ∧ σ5.val nz = flagOf (bs.take (k + 1)) ∧
        σ5.val scn = 2 * (k + 1) ∧ (∀ i, i ≠ X → σ5.sh i = σ.sh i) ∧ (∀ r, r ≠ nz → r ≠ scn → σ5.val r = σ.val r) ∧
        σ5.cell = σ.cell := by
      rw [hσ5, f2, hσ1]
      refine ⟨rfl, by simp [WState.setv, WState.seth, hsh]; ring, by simp [WState.setv, WState.seth,
        Function.update_apply, hns], by simp [WState.setv, WState.seth, Function.update_apply, hsn, hsc]; ring,
        fun i hi => by simp [WState.setv, WState.seth, Function.update_apply, hi],
        fun r h1 h2 => by simp [WState.setv, WState.seth, Function.update_apply, h1, h2], rfl⟩
    obtain ⟨τ, e, t1, t2, t3, t4, t5, t6, t7⟩ := ih (k + 1) σ5 (by omega) (by rw [f5.1, hst]) f5.2.1 f5.2.2.1
      f5.2.2.2.1
    exact ⟨τ, WExec.mono (WExec.whsT hb (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) e)
      (by omega), t1, t2, t3, t4.trans f5.1, fun i hi => (t5 i hi).trans (f5.2.2.2.2.1 i hi),
      fun r h1 h2 => (t6 r h1 h2).trans (f5.2.2.2.2.2.1 r h1 h2), t7.trans f5.2.2.2.2.2.2⟩

/-- The test's cost. -/
def onesCost (w : ℕ) : ℕ := w * 20 + 1 + 1 + (2 * w * 5 + 1)

theorem onesChk_spec (X : Fin (ns + 1)) (nz scn : Fin nr) (hns : nz ≠ scn) (bs rest : List Bool) (σ : WState ns nr)
    (hst : σ.st X = frameP bs ++ false :: rest) (hsh : σ.sh X = 0) (hnz : σ.val nz = 0) (hsc : σ.val scn = 0)
    (hcap : 2 * bs.length + 2 ≤ cap) :
    ∃ τ, WExec cap (onesChk X nz scn) σ τ (onesCost bs.length) ∧ τ.sh X = 0 ∧ τ.val nz = flagOf bs ∧
      τ.val scn = 0 ∧ τ.st = σ.st ∧ (∀ i, i ≠ X → τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ nz → r ≠ scn → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, e1, a1, a2, a3, a4, a5, a6, a7⟩ := onesLoop_spec cap X nz scn hns bs rest hcap bs.length 0 σ
    (by omega) hst (by rw [hsh]) (by rw [hnz]; simp [flagOf]) (by rw [hsc])
  obtain ⟨τ, e2, b1, b2, b3, b4, b5, b6⟩ := rew1_spec cap X scn (2 * bs.length) τ1 a3 a1 (by omega)
  refine ⟨τ, WExec.seq e1 e2, b1, by rw [b5 nz hns, a2], b2, b3.trans a4, fun i hi => (b4 i hi).trans (a5 i hi),
    fun r h1 h2 => (b5 r h2).trans (a6 r h1 h2), b6.trans a7⟩

end Ones

end NearCubicWires.WireExponent3_5.PrimT.Flips
