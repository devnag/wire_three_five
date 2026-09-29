import Proof.Wire_3_5.FinalPass.ThrArith2

/-! # The THR digit program's output: appending the digit word (W17)

`DigsW` writes `digsWord` on its output stream `Dg` by appending one bit at a time at the head (`writeTapeBit` at the
end appends), counting the written length in `Lw` so that the stream can be rewound exactly. `outAt σ Dg Lw l` is the
state with content `l`, head and counter at `|l|`. `emitBitW` appends one bit, `onesW` appends `1^X`, and `encW`
appends one pool index's word `enc (oOff + o) = true :: 1^{oOff+o} 0`. Main declarations: `enc`, `outAt`,
`emitBit_spec`, `ones_spec`, **`enc_spec`**. Paper quantity: the digit population's pool indices `oOff + i`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

/-- One pool index's word in `digsWord`. -/
def enc (x : ℕ) : List Bool := true :: (List.replicate x true ++ [false])

variable {ns nr : ℕ} (cap : ℕ)

/-- Output content `l` on `Dg`, the head and the counter `Lw` at `|l|`. -/
def outAt (σ : WState ns nr) (Dg : Fin (ns + 1)) (Lw : Fin nr) (l : List Bool) : WState ns nr :=
  ((σ.sets Dg l).seth Dg l.length).setv Lw l.length

section Out
variable (σ : WState ns nr) (Dg : Fin (ns + 1)) (Lw : Fin nr) (l : List Bool)

theorem outAt_self (hst : σ.st Dg = l) (hsh : σ.sh Dg = l.length) (hlw : σ.val Lw = l.length) :
    outAt σ Dg Lw l = σ := by
  apply WState.eq
  · funext i; by_cases hi : i = Dg
    · rw [hi]; simp [outAt, hsh]
    · simp [outAt, Function.update_apply, hi]
  · funext i; by_cases hi : i = Dg
    · rw [hi]; simp [outAt, hst]
    · simp [outAt, Function.update_apply, hi]
  · funext r; by_cases hr : r = Lw
    · rw [hr]; simp [outAt, hlw]
    · simp [outAt, Function.update_apply, hr]
  · rfl

theorem outAt_outAt (l' : List Bool) : outAt (outAt σ Dg Lw l) Dg Lw l' = outAt σ Dg Lw l' := by
  apply WState.eq
  · funext i; by_cases hi : i = Dg
    · rw [hi]; simp [outAt]
    · simp [outAt, Function.update_apply, hi]
  · funext i; by_cases hi : i = Dg
    · rw [hi]; simp [outAt]
    · simp [outAt, Function.update_apply, hi]
  · funext r; by_cases hr : r = Lw
    · rw [hr]; simp [outAt]
    · simp [outAt, Function.update_apply, hr]
  · rfl

theorem outAt_setv (r : Fin nr) (h : r ≠ Lw) (v : ℕ) : outAt (σ.setv r v) Dg Lw l = (outAt σ Dg Lw l).setv r v := by
  apply WState.eq
  · rfl
  · rfl
  · funext q; by_cases h1 : q = Lw
    · rw [h1]; simp [outAt, Function.update_apply, Ne.symm h]
    · by_cases h2 : q = r
      · rw [h2]; simp [outAt, Function.update_apply, h]
      · simp [outAt, Function.update_apply, h1, h2]
  · rfl

@[simp] theorem outAt_val_Lw : (outAt σ Dg Lw l).val Lw = l.length := by simp [outAt]
theorem outAt_val_ne (r : Fin nr) (h : r ≠ Lw) : (outAt σ Dg Lw l).val r = σ.val r := by
  simp [outAt, Function.update_apply, h]
@[simp] theorem outAt_st_Dg : (outAt σ Dg Lw l).st Dg = l := by simp [outAt]
@[simp] theorem outAt_sh_Dg : (outAt σ Dg Lw l).sh Dg = l.length := by simp [outAt]
@[simp] theorem outAt_cell : (outAt σ Dg Lw l).cell = σ.cell := rfl

end Out

/-- Append one bit. -/
def emitBitW (Dg : Fin (ns + 1)) (Lw : Fin nr) (b : Bool) : WM ns nr := .seq (.wr Dg b) (.seq (.fwd Dg) (.inc Lw))

theorem emitBit_spec (Dg : Fin (ns + 1)) (Lw : Fin nr) (b : Bool) (σ : WState ns nr) (l : List Bool)
    (hst : σ.st Dg = l) (hsh : σ.sh Dg = l.length) (hlw : σ.val Lw = l.length) (hc : l.length < cap) :
    WExec cap (emitBitW Dg Lw b) σ (outAt σ Dg Lw (l ++ [b])) 7 := by
  have d1 := WExec.wr (cap := cap) Dg b σ
  rw [hst, hsh, Hash4.writeTapeBit_end] at d1
  have d2 := WExec.fwd (cap := cap) Dg (σ.sets Dg (l ++ [b]))
  have d3 := WExec.inc (cap := cap) Lw ((σ.sets Dg (l ++ [b])).seth Dg ((σ.sets Dg (l ++ [b])).sh Dg + 1))
    (by simp [hlw]; exact hc)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3)) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = Dg
    · rw [hi]; simp [outAt, hsh]
    · simp [outAt, Function.update_apply, hi]
  · rfl
  · funext r; by_cases hr : r = Lw
    · rw [hr]; simp [outAt, hlw]
    · simp [outAt, Function.update_apply, hr]
  · rfl

/-- Append `1^X`, `X` counted down. -/
def onesW (Dg : Fin (ns + 1)) (Lw X : Fin nr) : WM ns nr := .whr X (.seq (.dec X) (emitBitW Dg Lw true))

theorem ones_spec (Dg : Fin (ns + 1)) (Lw X : Fin nr) (hXL : X ≠ Lw) :
    ∀ (k : ℕ) (σ : WState ns nr) (l : List Bool), σ.val X = k → k ≤ cap → σ.st Dg = l → σ.sh Dg = l.length →
      σ.val Lw = l.length → l.length + k < cap + 1 →
      WExec cap (onesW Dg Lw X) σ (outAt (σ.setv X 0) Dg Lw (l ++ List.replicate k true)) (11 * k + 1)
  | 0, σ, l, hk, _, hst, hsh, hlw, _ => by
    refine WExec.cast cap (WExec.whrF hk) ?_ (by omega)
    rw [List.replicate_zero, List.append_nil, ThrRead.setv_eq_self σ X 0 hk, outAt_self σ Dg Lw l hst hsh hlw]
  | k + 1, σ, l, hk, hkc, hst, hsh, hlw, hc => by
    have d1 := WExec.dec (cap := cap) X σ (by omega)
    have d2 := emitBit_spec cap Dg Lw true (σ.setv X (σ.val X - 1)) l (by simpa using hst) (by simpa using hsh)
      (by simp [Function.update_apply, Ne.symm hXL, hlw]) (by omega)
    have ih := ones_spec Dg Lw X hXL k (outAt (σ.setv X (σ.val X - 1)) Dg Lw (l ++ [true])) (l ++ [true])
      (by rw [outAt_val_ne _ _ _ _ _ hXL]; simp [hk]) (by omega) (outAt_st_Dg _ _ _ _) (outAt_sh_Dg _ _ _ _)
      (outAt_val_Lw _ _ _ _) (by simp; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 d2) ih) ?_ (by omega)
    rw [← outAt_setv _ _ _ _ _ hXL, outAt_outAt, List.append_assoc, List.singleton_append, ← List.replicate_succ]
    congr 1
    refine WState.eq rfl rfl ?_ rfl
    funext r; by_cases hr : r = X
    · rw [hr]; simp
    · simp [Function.update_apply, hr]

/-- Append `enc (Off + Oc)`: `Q 0 = Off`, `Q 1 = Oc` (kept), `Q 2 = X`, `Q 3 = T`, `Q 4 = U` (scratch, zero),
`Q 5 = Lw`. -/
def encW (Dg : Fin (ns + 1)) (Q : Fin 6 ↪ Fin nr) : WM ns nr :=
  .seq (Hash4.wcopyR (Q 0) (Q 2) (Q 3)) (.seq (Hash4.wcopyR (Q 1) (Q 3) (Q 4)) (.seq (WM.move (Q 3) (Q 2))
    (.seq (emitBitW Dg (Q 5) true) (.seq (onesW Dg (Q 5) (Q 2)) (emitBitW Dg (Q 5) false)))))

/-- `encW`'s step bound. -/
def encCost (x o : ℕ) : ℕ := 29 * x + 25 * o + 60

theorem enc_spec (Dg : Fin (ns + 1)) (Q : Fin 6 ↪ Fin nr) (σ : WState ns nr) (off o : ℕ) (l : List Bool)
    (h0 : σ.val (Q 0) = off) (h1 : σ.val (Q 1) = o) (h2 : σ.val (Q 2) = 0) (h3 : σ.val (Q 3) = 0)
    (h4 : σ.val (Q 4) = 0) (hst : σ.st Dg = l) (hsh : σ.sh Dg = l.length) (hlw : σ.val (Q 5) = l.length)
    (hc : l.length + off + o + 2 ≤ cap) :
    WExec cap (encW Dg Q) σ (outAt σ Dg (Q 5) (l ++ enc (off + o))) (encCost (off + o) o) := by
  have v : ∀ i j : Fin 6, i ≠ j → Q i ≠ Q j := fun i j h => Q.injective.ne h
  have d1 := Hash4.wcopyR_spec cap (Q 0) (Q 2) (Q 3) (v 0 2 (by decide)) (v 0 3 (by decide)) (v 2 3 (by decide))
    σ h2 h3 (by omega)
  rw [h0] at d1
  have d2 := Hash4.wcopyR_spec cap (Q 1) (Q 3) (Q 4) (v 1 3 (by decide)) (v 1 4 (by decide)) (v 3 4 (by decide))
    (σ.setv (Q 2) off) (by simp [Function.update_apply, v 3 2 (by decide), h3])
    (by simp [Function.update_apply, v 4 2 (by decide), h4])
    (by simp [Function.update_apply, v 1 2 (by decide), h1]; omega)
  rw [show (σ.setv (Q 2) off).val (Q 1) = o by simp [Function.update_apply, v 1 2 (by decide), h1]] at d2
  have d3 := wmove_spec cap (Q 3) (Q 2) (v 3 2 (by decide)) o ((σ.setv (Q 2) off).setv (Q 3) o) (by simp)
    (by simp; omega) (by simp [Function.update_apply, v 2 3 (by decide)]; omega)
  rw [show ((σ.setv (Q 2) off).setv (Q 3) o).val (Q 2) = off by simp [Function.update_apply, v 2 3 (by decide)],
    show ((σ.setv (Q 2) off).setv (Q 3) o).val (Q 3) = o by simp] at d3
  obtain ⟨σ3, e3⟩ : ∃ τ, τ = (((σ.setv (Q 2) off).setv (Q 3) o).setv (Q 3) 0).setv (Q 2) (off + o) := ⟨_, rfl⟩
  rw [← e3] at d3
  have s3 : σ3.st Dg = l ∧ σ3.sh Dg = l.length ∧ σ3.val (Q 5) = l.length ∧ σ3.val (Q 2) = off + o := by
    rw [e3]; refine ⟨by simp [hst], by simp [hsh], ?_, by simp⟩
    simp [Function.update_apply, v 5 2 (by decide), v 5 3 (by decide), hlw]
  have d4 := emitBit_spec cap Dg (Q 5) true σ3 l s3.1 s3.2.1 s3.2.2.1 (by omega)
  have d5 := ones_spec cap Dg (Q 5) (Q 2) (v 2 5 (by decide)) (off + o) (outAt σ3 Dg (Q 5) (l ++ [true]))
    (l ++ [true]) (by rw [outAt_val_ne _ _ _ _ _ (v 2 5 (by decide)), s3.2.2.2]) (by omega) (outAt_st_Dg _ _ _ _)
    (outAt_sh_Dg _ _ _ _) (outAt_val_Lw _ _ _ _) (by simp; omega)
  have d6 := emitBit_spec cap Dg (Q 5) false
    (outAt ((outAt σ3 Dg (Q 5) (l ++ [true])).setv (Q 2) 0) Dg (Q 5) (l ++ [true] ++ List.replicate (off + o) true))
    (l ++ [true] ++ List.replicate (off + o) true) (outAt_st_Dg _ _ _ _) (outAt_sh_Dg _ _ _ _) (outAt_val_Lw _ _ _ _)
    (by simp; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 d6))))) ?_
    (by unfold encCost; omega)
  rw [outAt_outAt, ← outAt_setv _ _ _ _ _ (v 2 5 (by decide)), outAt_outAt]
  have hw : l ++ [true] ++ List.replicate (off + o) true ++ [false] = l ++ enc (off + o) := by simp [enc]
  rw [hw]
  congr 1
  rw [e3]
  refine WState.eq rfl rfl ?_ rfl
  funext r
  by_cases r2 : r = Q 2
  · rw [r2]; simp [h2]
  · by_cases r3 : r = Q 3
    · rw [r3]; simp [Function.update_apply, v 3 2 (by decide), h3]
    · simp [Function.update_apply, r2, r3]

end NearCubicWires.WireExponent3_5.FinalPass.ThrArith
