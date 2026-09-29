import Proof.Wire_3_5.UnionMachine.FrontFmtW
import Proof.Wire_3_5.Primitive.Writers.WriteNat

/-! # C6 front, U5, the source formats (d): the request's head

Every call's request word begins with `natWord q ++ [mode] ++ natWord 4` (the union request, P3:3685-3691; the table
writer's `FrontTW.TWRel.hd`). **`hdW mb`** writes it framed from `1^q`: it counts `q` into a register, then PA's
`writeNatM` (q), the mode bit, the constant `4` and PA's `writeNatM` (4), then the end mark (**`hdStage`**).

Paper quantity of the main type: the request head of the union's calls. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtHd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (wm_step wenc_H_zero)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (writeNatM writeNatM_spec appendO appendO_st appendO_cell
  emitPair emitPair_spec)
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- The value registers: `0` for `q`, `8` for `4`; the writer's scratch `1..7` shared (`7` the output count). -/
def Rq : Fin 8 ↪ Fin 9 := ⟨fun i => ⟨i.val, by omega⟩, fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simpa using this)⟩
def R4 : Fin 8 ↪ Fin 9 := ⟨fun i => ⟨if i.val = 0 then 8 else i.val, by split_ifs <;> omega⟩, fun a b h => Fin.ext (by
  have hv := congrArg Fin.val h; simp only at hv; split_ifs at hv <;> omega)⟩

/-- Count `1^q` into register `0`. -/
def loadQ : WM 1 9 := .whs 0 (.seq (.inc 0) (.fwd 0))

/-- Register `8` := `4`. -/
def four : WM 1 9 := .seq (.inc 8) (.seq (.inc 8) (.seq (.inc 8) (.inc 8)))

/-- **The request head**, framed. -/
def hdW (mb : Bool) : WM 1 9 :=
  .seq loadQ (.seq (writeNatM 1 Rq) (.seq (emitPair 1 7 mb) (.seq four (.seq (writeNatM 1 R4) (emitC 1 7 false)))))

theorem frame_marks (w : List Bool) : frame w = marks w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, ih, marks]

theorem marks_app (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := by
  simp [marks, List.flatMap_append]

section Load
variable (cap : ℕ)

theorem rd_rep (q i : ℕ) (hi : i < q) : readTapeBit (List.replicate q true) i = true := by
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_replicate, hi]

theorem rd_rep_end (q : ℕ) : readTapeBit (List.replicate q true) q = false := by
  simp [readTapeBit, List.getD_eq_getElem?_getD]

theorem loadQ_spec (q : ℕ) (hq : q ≤ cap) (n : ℕ) : ∀ (σ : WState 1 9), n ≤ q → σ.st 0 = List.replicate q true →
    σ.sh 0 = q - n → σ.val 0 = q - n →
    WExec cap loadQ σ ((σ.seth 0 q).setv 0 q) (7 * n + 1) := by
  induction n with
  | zero =>
    intro σ _ h0 hh hv
    have hz : wbit σ 0 = false := by
      simp only [wbit, h0, hh, Nat.sub_zero]; exact rd_rep_end q
    have e : (σ.seth 0 q).setv 0 q = σ := by
      apply WState.eq
      · funext j; by_cases hj : j = 0
        · subst hj; simp [hh]
        · simp [hj]
      · simp
      · funext j; by_cases hj : j = 0
        · subst hj; simp [hv]
        · simp [hj]
      · simp
    rw [e]; exact WExec.mono (WExec.whsF hz) (by omega)
  | succ n ih =>
    intro σ hn h0 hh hv
    have hw : wbit σ 0 = true := by
      simp only [wbit, h0, hh]; exact rd_rep q _ (by omega)
    have hlt : σ.val 0 < cap := by rw [hv]; omega
    have s1 := WExec.inc (cap := cap) (0 : Fin 9) σ hlt
    have s2 := WExec.fwd (cap := cap) (0 : Fin 2) (σ.setv 0 (σ.val 0 + 1))
    have ih' := ih ((σ.setv 0 (σ.val 0 + 1)).seth 0 ((σ.setv 0 (σ.val 0 + 1)).sh 0 + 1)) (by omega)
      (by simp [h0]) (by simp [hh]; omega) (by simp [hv]; omega)
    have e : ((((σ.setv 0 (σ.val 0 + 1)).seth 0 ((σ.setv 0 (σ.val 0 + 1)).sh 0 + 1)).seth 0 q).setv 0 q) =
        (σ.seth 0 q).setv 0 q := by
      apply WState.eq
      · funext j; by_cases hj : j = 0
        · subst hj; simp
        · simp [hj]
      · simp
      · funext j; by_cases hj : j = 0
        · subst hj; simp
        · simp [hj]
      · simp
    rw [e] at ih'
    exact WExec.mono (WExec.whsT hw (WExec.seq s1 s2) ih') (by omega)

theorem four_spec (σ : WState 1 9) (h8 : σ.val 8 = 0) (hc : 4 ≤ cap) : WExec cap four σ (σ.setv 8 4) 15 := by
  have s1 := WExec.inc (cap := cap) (8 : Fin 9) σ (by omega)
  have s2 := WExec.inc (cap := cap) (8 : Fin 9) (σ.setv 8 (σ.val 8 + 1)) (by simp; omega)
  have s3 := WExec.inc (cap := cap) (8 : Fin 9) ((σ.setv 8 (σ.val 8 + 1)).setv 8 ((σ.setv 8 (σ.val 8 + 1)).val 8 + 1))
    (by simp; omega)
  have s4 := WExec.inc (cap := cap) (8 : Fin 9)
    (((σ.setv 8 (σ.val 8 + 1)).setv 8 ((σ.setv 8 (σ.val 8 + 1)).val 8 + 1)).setv 8
      (((σ.setv 8 (σ.val 8 + 1)).setv 8 ((σ.setv 8 (σ.val 8 + 1)).val 8 + 1)).val 8 + 1)) (by simp; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (by omega)
  apply WState.eq
  · simp
  · simp
  · funext j; by_cases hj : j = 8
    · subst hj; simp [h8]
    · simp [Function.update_apply, hj]
  · simp

theorem marks_len (w : List Bool) : (marks w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [marks] at ih ⊢; omega

/-- The head program's fuel. -/
def hdCost (q : ℕ) : ℕ :=
  7 * q + 1 + 1 + ((natBitLength q + 10) * (100 * q + 200) + 1 + (15 + 1 + (15 + 1 +
    ((natBitLength 4 + 10) * (100 * 4 + 200) + 1 + 7))))

/-- **The request head's program**: from `1^q` (stream `0`) and a blank output (stream `1`), the output holds
`frame (natWord q ++ [mb] ++ natWord 4)`. -/
theorem hdW_spec (q : ℕ) (mb : Bool) (hcap : 8 * q + 48 ≤ cap) (σ : WState 1 9) (h0 : σ.st 0 = List.replicate q true)
    (h1 : σ.st 1 = []) (hsh : ∀ j, σ.sh j = 0) (hv : ∀ r, σ.val r = 0) :
    ∃ τ, WExec cap (hdW mb) σ τ (hdCost q) ∧
      τ.st 1 = frame (natWord q ++ [mb] ++ natWord 4) ∧ τ.st 0 = List.replicate q true ∧ τ.cell = σ.cell := by
  have hnq : natBitLength q ≤ q + 1 := by
    have e := NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.natBitLength_eq_halvings q
    have h2 := NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.halvings_le (q / 2)
    omega
  have hn4 : natBitLength 4 = 3 := by decide
  have hlq : (marks (natWord q)).length = 2 * (2 * natBitLength q + 1) := by
    rw [marks_len, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
  have hl4 : (marks (natWord 4)).length = 14 := by
    rw [marks_len, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length, hn4]
  -- 1: q into register 0
  have s1 := loadQ_spec cap q (by omega) q σ le_rfl h0 (by rw [hsh]; omega) (by rw [hv]; omega)
  set σ1 := (σ.seth 0 q).setv 0 q with hσ1
  -- 2: natWord q
  have s2 := writeNatM_spec cap 1 Rq σ1 (by simp [σ1, Rq, hv]) (by simp [σ1, Rq, hv]) (by simp [σ1, Rq, hv])
    (by simp [σ1, Rq, hv]) (by simp [σ1, Rq, hv]) (by simp [σ1, Rq, hv]) (by simp [σ1, hsh, h1])
    (by simp [σ1, Rq, hv]; omega)
  have eq0 : σ1.val (Rq 0) = q := by simp [σ1, Rq]
  rw [eq0] at s2
  set σ2 := appendO σ1 1 (Rq 7) (marks (natWord q)) with hσ2
  have v27 : σ2.val 7 = 2 * (2 * natBitLength q + 1) := by
    simp [σ2, σ1, Rq, hv, hlq]
  -- 3: the mode bit
  have s3 := emitPair_spec cap 1 7 mb σ2 (by simp [σ2, σ1, hsh, h1, hlq]) (by rw [v27]; omega)
  set σ3 := appendO σ2 1 7 [true, mb] with hσ3
  -- 4: register 8 := 4
  have s4 := four_spec cap σ3 (by simp [σ3, σ2, σ1, Rq, hv]) (by omega)
  set σ4 := σ3.setv 8 4 with hσ4
  -- 5: natWord 4
  have s5 := writeNatM_spec cap 1 R4 σ4 (by simp [σ4, σ3, σ2, σ1, R4, Rq, hv]) (by simp [σ4, σ3, σ2, σ1, R4, Rq, hv])
    (by simp [σ4, σ3, σ2, σ1, R4, Rq, hv]) (by simp [σ4, σ3, σ2, σ1, R4, Rq, hv])
    (by simp [σ4, σ3, σ2, σ1, R4, Rq, hv]) (by simp [σ4, σ3, σ2, σ1, R4, Rq, hv])
    (by simp [σ4, σ3, σ2, σ1, hsh, h1])
    (by simp [σ4, σ3, σ2, σ1, R4, Rq, hv, hlq, hn4]; omega)
  have eq8 : σ4.val (R4 0) = 4 := by simp [σ4, R4]
  rw [eq8] at s5
  set σ5 := appendO σ4 1 (R4 7) (marks (natWord 4)) with hσ5
  -- 6: the end mark
  have s6 := emitC_spec cap (1 : Fin 2) (7 : Fin 9) false σ5 (by simp [σ5, σ4, σ3, σ2, σ1, hsh, h1]; omega)
    (by simp [σ5, σ4, σ3, σ2, σ1, R4, Rq, hv, hlq, hl4]; omega)
  have t1 : σ1.st 1 = [] := by rw [hσ1]; simp [h1]
  have t2 : σ2.st 1 = marks (natWord q) := by rw [hσ2, appendO_st, Function.update_self, t1, List.nil_append]
  have t3 : σ3.st 1 = marks (natWord q) ++ [true, mb] := by rw [hσ3, appendO_st, Function.update_self, t2]
  have t4 : σ4.st 1 = marks (natWord q) ++ [true, mb] := by rw [hσ4]; exact t3
  have t5 : σ5.st 1 = marks (natWord q) ++ [true, mb] ++ marks (natWord 4) := by
    rw [hσ5, appendO_st, Function.update_self, t4]
  have z1 : σ1.st 0 = List.replicate q true := by rw [hσ1]; simp [h0]
  have z5 : σ5.st 0 = List.replicate q true := by
    rw [hσ5, appendO_st, Function.update_of_ne (by decide), hσ4]
    show σ3.st 0 = _
    rw [hσ3, appendO_st, Function.update_of_ne (by decide), hσ2, appendO_st, Function.update_of_ne (by decide), z1]
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) (by
    unfold hdCost; exact le_refl _), ?_, ?_, ?_⟩
  · show (Function.update σ5.st 1 (σ5.st 1 ++ [false])) 1 = _
    rw [Function.update_self, t5, frame_marks, marks_app, marks_app]
    simp [marks]
  · show (Function.update σ5.st 1 (σ5.st 1 ++ [false])) 0 = _
    rw [Function.update_of_ne (by decide), z5]
  · show σ5.cell = σ.cell
    rw [hσ5, appendO_cell, hσ4]
    show σ3.cell = σ.cell
    rw [hσ3, appendO_cell, hσ2, appendO_cell, hσ1]; rfl
end Load

/-! ## As a Step -/

def σH (q : ℕ) : WState 1 9 := ⟨fun _ => 0, ![List.replicate q true, []], fun _ => 0, false⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtHd
