import Proof.Wire_3_5.UnionMachine.FrontFmtBM
import Proof.Wire_3_5.UnionMachine.FrontTWBase

/-! # C6 front, U5, the source formats (d): the atoms' codes for the carrier writers

"The carrier of a variable: the charged gates of its atoms" (P3:3409-3410): the carrier writer of variable `X` reads
the codes of its `s` grid atoms (`FrontFoldLoop.FoldIn.as`), which the guess's entries hold in order (entry `X·s + a`
= the sign word and the code of `C_{X,a}`, `FrontTW.TWRel.esc`). **`caW`** writes, per variable, the framed
concatenation of its entries' code fields, from the framed rest (`FrontFold.carLoop_spec` per variable, an end mark,
PA's counted loops; **`caW_spec`**, **`caStage`**).

Paper quantity of the main type: the codes of each variable's grid atoms (the carrier writer's inputs). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtCA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (wm_step wenc_H_zero)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_append appendO_setv)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtBM (ld ld_spec appendO_seth flat_frame_le)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW (entW entsW)

/-! ## The entries' positions -/

/-- The start of entry `e` in the raw entries. -/
def posE (es : List (Bool × Bool × ℕ)) (e : ℕ) : ℕ := (entsW (es.take e)).length

/-- Entry `e`'s code. -/
def codeE (es : List (Bool × Bool × ℕ)) (e : ℕ) : ℕ := (es.getD e (false, false, 0)).2.2

theorem entsW_append (A B : List (Bool × Bool × ℕ)) : entsW (A ++ B) = entsW A ++ entsW B := by
  simp [entsW]

theorem entsW_take_succ (es : List (Bool × Bool × ℕ)) (e : ℕ) (he : e < es.length) :
    entsW (es.take (e + 1)) = entsW (es.take e) ++ entW es[e] := by
  rw [List.take_add_one, List.getElem?_eq_getElem he, Option.toList_some, entsW_append]
  simp [entsW]

theorem codeE_eq (es : List (Bool × Bool × ℕ)) (e : ℕ) (he : e < es.length) : codeE es e = es[e].2.2 := by
  simp [codeE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he]

theorem posE_succ (es : List (Bool × Bool × ℕ)) (e : ℕ) (he : e < es.length) :
    posE es (e + 1) = posE es e + 4 + (natWord (codeE es e)).length := by
  unfold posE; rw [entsW_take_succ es e he, List.length_append, codeE_eq es e he]
  simp [entW]; ring

theorem marks_app (u v : List Bool) : marks (u ++ v) = marks u ++ marks v := FrontFmtHd.marks_app u v

theorem entsW_split (es : List (Bool × Bool × ℕ)) (e : ℕ) (he : e < es.length) :
    entsW es = entsW (es.take e) ++ entW es[e] ++ entsW (es.drop (e + 1)) := by
  conv_lhs => rw [← List.take_append_drop (e + 1) es]
  rw [entsW_append, entsW_take_succ es e he]

theorem marks_len (w : List Bool) : (marks w).length = 2 * w.length := FrontFmtHd.marks_len w

/-- The stream at entry `e`: marked entries, entry `e`'s grid word and code field, the rest. -/
theorem at_entry (es : List (Bool × Bool × ℕ)) (tail rest : List Bool) (e : ℕ) (he : e < es.length) :
    ∃ pre rst, frame (entsW es ++ tail) ++ rest =
      pre ++ marks (FrontEntriesRef.gridWord es[e].1 es[e].2.1) ++ marks (natWord (codeE es e)) ++ rst ∧
      pre.length = 2 * posE es e := by
  refine ⟨marks (entsW (es.take e)), marks (entsW (es.drop (e + 1))) ++ marks tail ++ [false] ++ rest, ?_, ?_⟩
  · rw [FrontFmtHd.frame_marks, marks_app, entsW_split es e he, codeE_eq es e he]
    simp [marks_app, entW, FrontEntriesRef.gridWord, marks]
  · rw [marks_len]; rfl

/-! ## The program -/

/-- One variable: its `s` entries' code fields, then the end mark (streams `0` the framed rest, `3` the output;
registers `2` `s`, `3` the entry counter, `4`, `5` the copier's, `6` the output count). -/
def caBody : WM 3 7 := .seq (FrontTWKit.cloop 2 3 (FrontFold.entBody 0 3 4 5 6)) (emitC 3 6 false)

/-- **The atoms' codes' program** (streams `0` the framed rest, `1` `1^nv`, `2` `1^s`, `3` the output; registers
`0` `nv`, `1` the variable counter). -/
def caW : WM 3 7 := .seq (ld 1 0) (.seq (ld 2 2) (FrontTWKit.cloop 0 1 caBody))

/-- Variable `x`'s codes. -/
def codesX (es : List (Bool × Bool × ℕ)) (s x : ℕ) : List Bool := FrontFold.codesOf (fun a => codeE es (x * s + a)) s

/-- The first `X` variables' framed codes. -/
def itemsOf (es : List (Bool × Bool × ℕ)) (s X : ℕ) : List Bool := ((List.range X).map (codesX es s)).flatMap frame

theorem itemsOf_succ (es : List (Bool × Bool × ℕ)) (s X : ℕ) :
    itemsOf es s (X + 1) = itemsOf es s X ++ frame (codesX es s X) := by
  unfold itemsOf; rw [List.range_succ, List.map_append, List.flatMap_append]; simp

/-- The variables' family. -/
def Fc (σ : WState 3 7) (es : List (Bool × Bool × ℕ)) (s X : ℕ) : WState 3 7 :=
  (appendO σ 3 6 (itemsOf es s X)).seth 0 (2 * posE es (X * s))

theorem codesX_len (es : List (Bool × Bool × ℕ)) (s Wn x : ℕ) (hW : ∀ e < es.length, (natWord (codeE es e)).length ≤ Wn)
    (hx : x * s + s ≤ es.length) : (codesX es s x).length ≤ s * Wn :=
  FrontFold.codesOf_length _ s Wn (fun k hk => hW _ (by omega))

theorem itemsOf_len (es : List (Bool × Bool × ℕ)) (s Wn X : ℕ)
    (hW : ∀ e < es.length, (natWord (codeE es e)).length ≤ Wn) (hX : X * s ≤ es.length) :
    (itemsOf es s X).length ≤ X * (2 * (s * Wn) + 1) := by
  have := flat_frame_le (s * Wn) ((List.range X).map (codesX es s)) (by
    intro w hw; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hx
    exact codesX_len es s Wn x hW (by nlinarith))
  simpa [itemsOf] using this

section Body
variable (cap : ℕ)

/-- **One variable's codes.** -/
theorem caBody_spec (es : List (Bool × Bool × ℕ)) (tail rest : List Bool) (s Wn nv : ℕ) (hes : nv * s ≤ es.length)
    (hW : ∀ e < es.length, (natWord (codeE es e)).length ≤ Wn) (σ : WState 3 7)
    (h0 : σ.st 0 = frame (entsW es ++ tail) ++ rest) (h3 : σ.st 3 = []) (h3h : σ.sh 3 = 0) (hS : σ.val 2 = s)
    (hT : σ.val 3 = 0) (hf : σ.val 4 = 0) (hc : σ.val 5 = 0) (hOP : σ.val 6 = 0)
    (hcap : (nv + 1) * (2 * (s * Wn) + 2 * Wn + 3) ≤ cap) (hs : s ≤ cap) (X : ℕ) (hX : X < nv) :
    WExec cap caBody (((Fc σ es s X).setv 0 (nv - X - 1)).setv 1 (X + 1))
      (((Fc σ es s (X + 1)).setv 0 (nv - X - 1)).setv 1 (X + 1))
      ((s * ((15 + 1 + (60 * Wn + 60)) + 8) + 1 + 1 + (7 * s + 1)) + 1 + 7) := by
  have hXs : X * s + s ≤ es.length := by nlinarith
  have hlenI := itemsOf_len es s Wn X hW (by nlinarith)
  have hXW : X * (2 * (s * Wn) + 1) + 2 * (s * Wn) + 2 * Wn + 2 ≤ cap := by
    have : X * (2 * (s * Wn) + 1) ≤ nv * (2 * (s * Wn) + 1) := Nat.mul_le_mul_right _ hX.le
    nlinarith
  set σX := ((Fc σ es s X).setv 0 (nv - X - 1)).setv 1 (X + 1) with hσX
  have v6 : σX.val 6 = (itemsOf es s X).length := by simp [σX, Fc, hOP]
  have e1 := FrontFold.carLoop_spec cap (0 : Fin 4) (3 : Fin 4) (by decide) (2 : Fin 7) 3 4 5 6 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) σX s Wn
    (fun a => codeE es (X * s + a)) (fun a => posE es (X * s + a))
    (fun a => (es.getD (X * s + a) (false, false, 0)).1) (fun a => (es.getD (X * s + a) (false, false, 0)).2.1)
    (fun a ha => by
      obtain ⟨pre, rst, h, hl⟩ := at_entry es tail rest (X * s + a) (by omega)
      refine ⟨pre, rst, ?_, hl⟩
      simp only [σX, Fc, WState.setv_st, WState.seth_st, appendO_st]
      rw [Function.update_of_ne (by decide), h0, h]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show X * s + a < es.length by omega)])
    (fun a ha => by rw [show X * s + (a + 1) = X * s + a + 1 by ring]; exact posE_succ es _ (by omega))
    (fun a ha => hW _ (by omega))
    (by simp [σX, Fc])
    (by simp [σX, Fc, h3, h3h])
    (by simp [σX, Fc, hS]) (by simp [σX, Fc, hT]) (by simp [σX, Fc, hf]) (by simp [σX, Fc, hc])
    (by rw [v6]; omega) hs
  set σC := FrontFold.carFam σX 0 3 6 (fun a => codeE es (X * s + a)) (fun a => posE es (X * s + a)) s with hσC
  have hC3 : σC.sh 3 = (σC.st 3).length := by simp [σC, FrontFold.carFam, σX, Fc, h3, h3h]
  have hC6 : σC.val 6 < cap := by
    have := FrontFold.codesOf_length (fun a => codeE es (X * s + a)) s Wn (fun k hk => hW _ (by omega))
    simp [σC, FrontFold.carFam, σX, Fc, hOP, marks_len]
    nlinarith
  have e2 := emitC_spec cap (3 : Fin 4) (6 : Fin 7) false σC hC3 hC6
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq
  · funext x; by_cases hx0 : x = 0
    · subst hx0; simp [σC, FrontFold.carFam, σX, Fc]; ring
    · by_cases hx3 : x = 3
      · subst hx3
        simp [σC, FrontFold.carFam, σX, Fc, itemsOf_succ, FrontFmtHd.frame_marks, marks_len, codesX]; ring
      · simp [σC, FrontFold.carFam, σX, Fc, hx0, hx3]
  · funext x; by_cases hx3 : x = 3
    · subst hx3; simp [σC, FrontFold.carFam, σX, Fc, itemsOf_succ, FrontFmtHd.frame_marks, codesX]
    · by_cases hx0 : x = 0
      · subst hx0; simp [σC, FrontFold.carFam, σX, Fc]
      · simp [σC, FrontFold.carFam, σX, Fc, hx3, hx0]
  · funext x; by_cases hx6 : x = 6
    · subst hx6; simp [σC, FrontFold.carFam, σX, Fc, itemsOf_succ, FrontFmtHd.frame_marks, marks_len, codesX]; ring
    · simp [σC, FrontFold.carFam, σX, Fc, Function.update_apply, hx6]
  · simp [σC, FrontFold.carFam, σX, Fc]

end Body

/-! ## The whole program -/

/-- The atoms' codes' fuel. -/
def caCost (s Wn nv : ℕ) : ℕ :=
  (7 * nv + 1) + 1 + ((7 * s + 1) + 1 + (nv * (((s * ((15 + 1 + (60 * Wn + 60)) + 8) + 1 + 1 + (7 * s + 1)) + 1 + 7) + 8)
    + 1 + 1 + (7 * nv + 1)))

section Spec
variable (cap : ℕ)

/-- **The atoms' codes' program**: every variable's framed code fields. -/
theorem caW_spec (es : List (Bool × Bool × ℕ)) (tail rest : List Bool) (s Wn nv : ℕ) (hes : nv * s ≤ es.length)
    (hW : ∀ e < es.length, (natWord (codeE es e)).length ≤ Wn)
    (hcap : (nv + 1) * (2 * (s * Wn) + 2 * Wn + 3) + s + nv ≤ cap) (σ : WState 3 7)
    (h0 : σ.st 0 = frame (entsW es ++ tail) ++ rest) (h1 : σ.st 1 = List.replicate nv true)
    (h2 : σ.st 2 = List.replicate s true) (h3 : σ.st 3 = []) (hsh : ∀ j, σ.sh j = 0) (hv : ∀ r, σ.val r = 0) :
    ∃ τ, WExec cap caW σ τ (caCost s Wn nv) ∧ τ.st 3 = itemsOf es s nv ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = σ.st 1 ∧
      τ.st 2 = σ.st 2 ∧ τ.cell = σ.cell := by
  have s1 := ld_spec cap (1 : Fin 4) (0 : Fin 7) nv (by omega) nv σ le_rfl h1 (by rw [hsh]; omega) (by rw [hv]; omega)
  set σ1 := (σ.seth 1 nv).setv 0 nv with hσ1
  have s2 := ld_spec cap (2 : Fin 4) (2 : Fin 7) s (by omega) s σ1 le_rfl (by simp [σ1, h2]) (by simp [σ1, hsh])
    (by simp [σ1, hv])
  set σ2 := (σ1.seth 2 s).setv 2 s with hσ2
  have hloop := FrontTWKit.cloop_spec cap (0 : Fin 7) (1 : Fin 7) (by decide) caBody nv
    ((s * ((15 + 1 + (60 * Wn + 60)) + 8) + 1 + 1 + (7 * s + 1)) + 1 + 7) (Fc σ2 es s) (by omega)
    (fun X hX => caBody_spec cap es tail rest s Wn nv hes hW σ2 (by simp [σ2, σ1, h0]) (by simp [σ2, σ1, h3])
      (by simp [σ2, σ1, hsh]) (by simp [σ2]) (by simp [σ2, σ1, hv]) (by simp [σ2, σ1, hv]) (by simp [σ2, σ1, hv])
      (by simp [σ2, σ1, hv]) (by nlinarith) (by omega) X hX)
  have e0 : ((Fc σ2 es s 0).setv 0 nv).setv 1 0 = σ2 := by
    apply WState.eq
    · funext x; by_cases hx : x = 0
      · subst hx; simp [Fc, itemsOf, posE, σ2, σ1, hsh, entsW]
      · simp [Fc, itemsOf, hx]
    · simp [Fc, itemsOf]
    · funext x; by_cases hx0 : x = 0
      · subst hx0; simp [Fc, itemsOf, σ2, σ1]
      · by_cases hx1 : x = 1
        · subst hx1; simp [Fc, itemsOf, σ2, σ1, hv]
        · simp [Fc, itemsOf, Function.update_apply, hx0, hx1]; intro h; subst h; rfl
    · simp [Fc]
  rw [e0] at hloop
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 hloop)) (by unfold caCost; exact le_refl _), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Fc, σ2, σ1, h3]
  · simp [Fc, σ2, σ1]
  · simp [Fc, σ2, σ1]
  · simp [Fc, σ2, σ1]
  · simp [Fc, σ2, σ1]

end Spec

/-! ## As a Step -/

def σC (R NV S : List Bool) : WState 3 7 := ⟨fun _ => 0, ![R, NV, S, []], fun _ => 0, false⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFmtCA
