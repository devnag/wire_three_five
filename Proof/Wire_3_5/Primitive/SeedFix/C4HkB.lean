import Proof.Wire_3_5.Primitive.SeedFix.C4HkA

/-! # The HASH stage, part 2: the finisher (`HashFinSpec`)

C4H's (iii): from the request's `frame w` on its input `iW` and the loop's `frame bits` on its input `iP` (every other
tape blank), `frame (w ++ frame bits)` on its output `o` (the THR writer's input). **`finW`** (streams:
`0` the output, `1` the request, `2` the decisions): `plW 1 0 [true]`, `plW 2 0 [true, true, true]`, then
`[true, false, false]`; **`finM`** its compiled program under base's masked reset; **`fin_spec`**: `HashFinSpec finM`
within `2·(15|w| + 23|bits| + 16) + 2` steps.

Paper quantity of the main type: the THR writer's input word `frame (w ++ frame bits)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch

theorem frame_fin (w bits : List Bool) :
    frame (w ++ frame bits) = w.flatMap (fun b => [true] ++ [b]) ++
      (bits.flatMap (fun b => [true, true, true] ++ [b]) ++ [true, false, false]) := by
  rw [C4Hf.frame_append_pairs]
  congr 1
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    show true :: true :: true :: b :: frame (frame bits) = _
    rw [ih]; rfl

/-- **The finisher's program** (streams: `0` the output, `1` the request, `2` the decisions). -/
def finW : WM 2 0 := .seq (plW 1 0 [true]) (.seq (plW 2 0 [true, true, true]) (wlist 0 [true, false, false]))

/-- The finisher's entry state. -/
def finSt (w bits : List Bool) : WState 2 0 := ⟨fun _ => 0, ![[], frame w, frame bits], Fin.elim0, false⟩

theorem finW_spec (w bits : List Bool) :
    ∃ τ : WState 2 0, WExec 0 finW (finSt w bits) τ (15 * w.length + 23 * bits.length + 16) ∧
      τ.st 0 = frame (w ++ frame bits) := by
  have h01 : (1 : Fin 3) ≠ 0 := by decide
  have h02 : (2 : Fin 3) ≠ 0 := by decide
  have t1 := pl_spec 0 (finSt w bits) 1 0 h01 [true] w rfl rfl rfl
  set σA := pSt (finSt w bits) 1 0 [true] 0 w with hσA
  have a2 : σA.st 2 = frame bits := by
    rw [hσA]; simp only [pSt, WState.seth_st]; rw [apd_st_ne _ 0 2 h02]; rfl
  have a2h : σA.sh 2 = 0 := by
    rw [hσA]; simp only [pSt, WState.seth_sh]
    rw [Function.update_of_ne (by decide), apd_sh_ne _ 0 2 h02]; rfl
  have a0 : σA.sh 0 = (σA.st 0).length := by
    rw [hσA]; simp only [pSt, WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (by decide), apd_sh_d, apd_st_d, List.length_append]
  have t2 := pl_spec 0 σA 2 0 h02 [true, true, true] bits a2 a2h a0
  set σB := pSt σA 2 0 [true, true, true] 0 bits with hσB
  have b0 : σB.sh 0 = (σB.st 0).length := by
    rw [hσB]; simp only [pSt, WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (by decide), apd_sh_d, apd_st_d, List.length_append]
  have t3 := wlist_spec 0 0 [true, false, false] σB b0
  refine ⟨_, WExec.cast 0 (WExec.seq t1 (WExec.seq t2 t3)) rfl (by simp; omega), ?_⟩
  rw [apd_st_d, hσB]
  simp only [pSt, WState.seth_st]
  rw [apd_st_d, hσA]
  simp only [pSt, WState.seth_st]
  rw [apd_st_d, frame_fin]
  simp [finSt]

/-- **The finisher's machine**: the compiled program under base's masked reset (`5` tapes). -/
noncomputable def finM := MaskedReset.machine (finW.toProg.compile) (fun _ => true)

def fiW : Fin (2 + 2 + 0 + 1) := ⟨2, by omega⟩
def fiP : Fin (2 + 2 + 0 + 1) := ⟨3, by omega⟩
def fiO : Fin (2 + 2 + 0 + 1) := ⟨0, by omega⟩

/-- The finisher's steps. -/
def finCost (w bits : List Bool) : ℕ := 2 * (15 * w.length + 23 * bits.length + 16) + 2

theorem fin_entry (w bits : List Bool) :
    (fun i : Fin (2 + 2 + 0 + 1) => if i = fiW then frame w else if i = fiP then frame bits else []) =
      Fin.addCases (C4Pipe.wblank (finSt w bits)) (fun _ : Fin 1 => []) := by
  funext i
  fin_cases i <;> rfl

/-- **The HASH finisher** (C4H's `HashFinSpec`). -/
theorem fin_spec : C4H.HashFinSpec finM fiW fiP fiO finCost := by
  refine ⟨by decide, fun w bits => ?_⟩
  obtain ⟨τ, hw, h0⟩ := finW_spec w bits
  obtain ⟨A', st, hA⟩ := C4Pipe.wm_blank 0 (15 * w.length + 23 * bits.length + 16) finW (finSt w bits) τ _ hw
    (fun _ => rfl) (fun r => Fin.elim0 r) rfl le_rfl
  refine ⟨A', ?_, ?_⟩
  · rw [fin_entry]
    exact st
  · have := hA 0
    rw [h0] at this
    exact this

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
