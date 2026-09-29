import Proof.Wire_3_5.UnionMachine.FrontFoldCat

/-! # C6 front, U5, the source formats (d): the witness's entries as the table writer reads them

The guess's rest holds the grid entries (P3:3672-3674: the signs and the atoms' codes), which the oracle stage leaves
framed (`frame r`); the table writer reads them raw (`FrontTW.TWData.Holds.es`: `src sW = entsW es ++ r`).
**`unmarkW`** copies the payload of a framed word raw (**`unmarkStage`**: `frame r ++ rest` ↦ `r`).

Paper quantity of the main type: the grid entries (signs and atoms' codes) of the parsed guess. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW wm_step wenc_H_zero)
open NearCubicWires.WireExponent3_5.PrimT.CarWM (rd_at rd_at1)

/-- One marked cell copied raw from stream `0` to the end of stream `1`. -/
def unBody : WM 1 0 := .seq (.fwd 0) (.seq (.ifs 0 (emitW 1 true) (emitW 1 false)) (.fwd 0))

/-- **Copy a framed word's payload raw.** -/
def unmarkW : WM 1 0 := .whs 0 unBody

theorem unLoop_spec (rest : List Bool) :
    ∀ (y pre : List Bool) (σ : WState 1 0), σ.st 0 = pre ++ (frame y ++ rest) → σ.sh 0 = pre.length →
      σ.sh 1 = (σ.st 1).length →
      ∃ τ, WExec 0 unmarkW σ τ (10 * y.length + 1) ∧ τ.st 1 = σ.st 1 ++ y ∧ τ.st 0 = σ.st 0 ∧ τ.cell = σ.cell
  | [], pre, σ, h0, h0h, h1 => by
    have hz : wbit σ 0 = false := by simp only [wbit, h0, h0h, rd_at]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, rfl, rfl⟩
  | b :: bs, pre, σ, h0, h0h, h1 => by
    have hw : wbit σ 0 = true := by simp only [wbit, h0, h0h, rd_at]; rfl
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts 0 (0 : Fin 2) σ
    have O1 := o1 1 (by decide)
    have hb : wbit σ1 0 = b := by simp only [wbit, n1, n1h, h0, h0h, rd_at1]; rfl
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts 0 (1 : Fin 2) b σ1 (by rw [O1.1, O1.2, h1])
    have s2' : WExec 0 (.ifs 0 (emitW 1 true) (emitW 1 false)) σ1 σ2 4 := by
      cases b
      · exact WExec.ifsF hb s2
      · exact WExec.ifsT hb s2
    have N2 := o2 0 (by decide)
    obtain ⟨σ3, s3, n3, n3h, o3, v3, c3⟩ := fwd_facts 0 (0 : Fin 2) σ2
    have O3 := o3 1 (by decide)
    obtain ⟨τ, s4, e4, n4, c4⟩ := unLoop_spec rest bs (pre ++ [true, b]) σ3
      (by rw [n3, N2.1, n1, h0]; simp [frame]) (by rw [n3h, N2.2, n1h, h0h]; simp)
      (by rw [O3.1, O3.2, e2h])
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2' s3)) s4) (by simp; omega), ?_, ?_, ?_⟩
    · rw [e4, O3.1, e2, O1.1]; simp
    · rw [n4, n3, N2.1, n1]
    · rw [c4, c3, c2, c1]

def σU (S : List Bool) : WState 1 0 := ⟨fun _ => 0, ![S, []], fun r => r.elim0, false⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtW
