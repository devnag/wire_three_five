import Proof.CaseAnalysis.FinalLengthGate
import Proof.Wire_3_5.FinalPass.FiltTabCopy
import Proof.Wire_3_5.UnionMachine.RoundBits

/-! # C6 front, U2: `⌈log₂ T(N)⌉` from the binary clock (P3:3637-3640)

Realizes the first term of the native width "`q(N)=⌈log₂T(N)⌉+A_pad⌈log₂(log₂T(N)+2)⌉+A_pad`" (P3:3637-3640) at
`T(N) = N^{C_clk}`: from the fixed-width binary word of `x + 1` (base's `HierarchyFromInput` writes
`binary W (N^{C_clk}+1)`), the program leaves `1^{⌈log₂ x⌉}` on its output stream. In C5's register language:
`B := 1` (the one-pass), `A := A − B` (the borrow subtractor), then while `2^e < A`: `B := 2B` (the shift pass),
`e := e + 1`, recompare (the borrow comparator); then `e` marks are emitted and the output head returns to `0`.
The loop stops at the least `e` with `x ≤ 2^e`, i.e. `⌈log₂ x⌉` (**`clog_of_loop`**). All passes are C5's
`mapPass` with the arithmetic (`mapS_one`, `mapS_sub`, `mapS_ge`, `mapS_shl`, `mapS_keepA`).

Main statement: **`clogP_spec`**. Paper quantity: `⌈log₂ T(N)⌉` (`Nat.clog 2 x`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontClog
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.Round

/-! ## The arithmetic -/

/-! ## The program: streams `A = 0`, `B = 1`, `Y = 2`; registers `F G X R E OP` -/

abbrev CS := WState 2 6

local notation "sA" => (0 : Fin 3)
local notation "sB" => (1 : Fin 3)
local notation "sY" => (2 : Fin 3)
local notation "rF" => (0 : Fin 6)
local notation "rG" => (1 : Fin 6)
local notation "rX" => (2 : Fin 6)
local notation "rR" => (3 : Fin 6)
local notation "rE" => (4 : Fin 6)
local notation "rOP" => (5 : Fin 6)

/-- Preparation: `B := 1`, `A := A − 1`, `F := [2^0 < A]`. -/
def prepP : WM 2 6 :=
  .seq (.inc rX) (.seq (mapPass oneOut oneNxt sB sA rX rR) (.seq (WM.clear rX) (.seq (.inc rX)
    (.seq (mapPass subO geN sA sB rX rR) (mapPass keepA geN sA sB rF rR)))))

/-- One round: `B := 2B`, `e := e + 1`, `F := [2^e < A]`. -/
def stepP : WM 2 6 :=
  .seq (WM.clear rG) (.seq (mapPass shOut shNxt sB sA rG rR) (.seq (.inc rE)
    (.seq (WM.clear rF) (mapPass keepA geN sA sB rF rR))))

/-- Emit `e` marks on `Y`, then return `Y`'s head. -/
def emitP : WM 2 6 := .whr rE (.seq (.dec rE) (emitC sY rOP true))
def rewP : WM 2 6 := .whr rOP (.seq (.dec rOP) (.bwd sY))

/-- A framed zero word on `B`, as long as `A`'s: one `[true, false]` per marker of `A`, the terminator, both heads
returned (counters `E` for `A`, `OP` for `B`). -/
def mkLoop : WM 2 6 :=
  .whs sA (.seq (emitC sB rOP true) (.seq (emitC sB rOP false) (.seq (WM.fwdC sA rE) (WM.fwdC sA rE))))
def mkB : WM 2 6 := .seq mkLoop (.seq (emitC sB rOP false) (.seq (WM.rewind sB rOP) (WM.rewind sA rE)))

/-- **The program**: the zero word on `B`, the preparation, the loop, the emission, the carries cleared (every
register and head back at `0`). -/
def clogP : WM 2 6 :=
  .seq mkB (.seq prepP (.seq (.whr rF stepP) (.seq emitP (.seq rewP (.seq (WM.clear rG) (WM.clear rX))))))

/-! ## The loop -/

variable (cap : ℕ)

/-- The loop invariant after `e` rounds, at value `x` and width `W`. -/
def Inv (W x e : ℕ) (σ : CS) : Prop :=
  σ.st sA = frame (binary W x) ∧ σ.sh sA = 0 ∧ σ.st sB = frame (binary W (2 ^ e)) ∧ σ.sh sB = 0 ∧
  σ.val rF = (decide (2 ^ e < x)).toNat ∧ σ.val rG ≤ 1 ∧ σ.val rR = 0 ∧ σ.val rE = e ∧ σ.val rOP = 0 ∧
  σ.st sY = [] ∧ σ.sh sY = 0 ∧ σ.val rX ≤ 1

theorem mod_self_lt {a W : ℕ} (h : a < 2 ^ W) : a % 2 ^ W = a := Nat.mod_eq_of_lt h

/-- One round. -/
theorem step_spec (W x e : ℕ) (σ : CS) (hI : Inv W x e σ) (hlt : 2 ^ e < x) (hx : 2 * x ≤ 2 ^ W)
    (hcap : 2 * W + 2 ≤ cap) (he : e + 1 ≤ W) :
    ∃ τ : CS, WExec cap stepP σ τ (82 * W + 22) ∧ Inv W x (e + 1) τ := by
  obtain ⟨hA, hhA, hB, hhB, hF, hG, hR, hE, hOP, hY, hhY, hX⟩ := hI
  have hW1 : 1 ≤ cap := by omega
  have hpe : 2 ^ (e + 1) < 2 ^ W := by rw [pow_succ]; omega
  have hxW : x < 2 ^ W := by
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow; omega
  -- clear G
  have c1 := wclear_spec cap rG (σ.val rG) σ rfl (by omega)
  set σ1 := σ.setv rG 0 with hσ1
  -- the shift pass on B (reading A as the second word)
  have c2 := mapPass_spec cap shOut shNxt sB sA rG rR (by decide) (by decide) hW1 (binary W (2 ^ e)) (binary W x)
    [] [false] false σ1 (by simp) (by simp [σ1, hB, frame_eq_frameP]) (by simp [σ1, hhB])
    (by simp [σ1, hA, frame_eq_frameP]) (by simp [σ1, hhA]) (by simp [σ1]) (by simp [σ1, Function.update_apply, hR])
    (by simp; omega)
  rw [mapS_shl W (2 ^ e) (binary W x) false (by simp)] at c2
  set σ2 := (σ1.sets sB (frameP (binary W (2 * 2 ^ e + false.toNat)) ++ false :: [])).setv rG
    (mapS shOut shNxt (binary W (2 ^ e)) (binary W x) false).2.toNat with hσ2
  -- inc E
  have hE2 : σ2.val rE = e := by simp [σ2, σ1, Function.update_apply, hE]
  have c3 := WExec.inc (cap := cap) rE σ2 (by rw [hE2]; omega)
  set σ3 := σ2.setv rE (σ2.val rE + 1) with hσ3
  -- clear F
  have hF3 : σ3.val rF = 1 := by simp [σ3, σ2, σ1, Function.update_apply, hF, hlt]
  have c4 := wclear_spec cap rF 1 σ3 hF3 (by omega)
  set σ4 := σ3.setv rF 0 with hσ4
  -- the comparator
  have hB4 : σ4.st sB = frameP (binary W (2 ^ (e + 1))) ++ [false] := by
    simp [σ4, σ3, σ2, pow_succ, mul_comm]
  have c5 := mapPass_spec cap keepA geN sA sB rF rR (by decide) (by decide) hW1 (binary W x)
    (binary W (2 ^ (e + 1))) [] [false] false σ4 (by simp)
    (by simp [σ4, σ3, σ2, σ1, hA, frame_eq_frameP]) (by simp [σ4, σ3, σ2, σ1, hhA]) hB4
    (by simp [σ4, σ3, σ2, σ1, hhB]) (by simp [σ4]) (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hR])
    (by simp; omega)
  rw [mapS_keepA geN (binary W x) (binary W (2 ^ (e + 1))) false (by simp), mapS_ge W x (2 ^ (e + 1)) false,
    mod_self_lt hxW, mod_self_lt hpe] at c5
  refine ⟨_, WExec.mono (c1.seq (c2.seq (c3.seq (c4.seq c5)))) ?_, ?_⟩
  · have : σ.val rG ≤ 1 := hG
    simp only [binary_length]
    omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ4, σ3, σ2, σ1, frame_eq_frameP]
    · simp [σ4, σ3, σ2, σ1, hhA]
    · simp [σ4, σ3, σ2, σ1, pow_succ, mul_comm, frame_eq_frameP]
    · simp [σ4, σ3, σ2, σ1, hhB]
    · simp only [WState.setv_val, Function.update_apply, if_true, Bool.not_false, Bool.toNat_true]
      congr 1
    · simp only [WState.setv_val, Function.update_apply, show rG ≠ rF by decide, show rG ≠ rE by decide,
        if_false, if_true]
      exact Bool.toNat_le _
    · simp [σ4, σ3, σ2, σ1, Function.update_apply, hR]
    · simp [σ4, σ3, σ2, σ1, Function.update_apply, hE]
    · simp [σ4, σ3, σ2, σ1, Function.update_apply, hOP]
    · simp [σ4, σ3, σ2, σ1, hY]
    · simp [σ4, σ3, σ2, σ1, hhY]
    · simp [σ4, σ3, σ2, σ1, Function.update_apply, hX]

/-- **The loop** runs exactly `⌈log₂ x⌉ − e` rounds and stops with `e = ⌈log₂ x⌉`. -/
theorem loop_spec (W x : ℕ) (hx : 2 * x ≤ 2 ^ W) (hcap : 2 * W + 2 ≤ cap) (hcW : Nat.clog 2 x ≤ W) :
    ∀ k e (σ : CS), Inv W x e σ → Nat.clog 2 x = e + k →
      ∃ τ : CS, WExec cap (.whr rF stepP) σ τ (k * (82 * W + 24) + 1) ∧ Inv W x (Nat.clog 2 x) τ
  | 0, e, σ, hI, hk => by
    have he : e = Nat.clog 2 x := by omega
    subst he
    have hF : σ.val rF = 0 := by
      rw [hI.2.2.2.2.1]
      have : ¬ 2 ^ Nat.clog 2 x < x := by have := Nat.le_pow_clog (by norm_num : 1 < 2) x; omega
      simp [this]
    exact ⟨σ, by simpa using WExec.whrF hF, hI⟩
  | k + 1, e, σ, hI, hk => by
    have hlt : 2 ^ e < x := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 (by omega)
    have hF : σ.val rF ≠ 0 := by rw [hI.2.2.2.2.1]; simp [hlt]
    obtain ⟨τ1, e1, hI1⟩ := step_spec cap W x e σ hI hlt hx hcap (by omega)
    obtain ⟨τ, e2, hI2⟩ := loop_spec W x hx hcap hcW k (e + 1) τ1 hI1 (by omega)
    have hm : (k + 1) * (82 * W + 24) = k * (82 * W + 24) + (82 * W + 24) := by ring
    exact ⟨τ, WExec.mono (WExec.whrT hF e1 e2) (by rw [hm]; omega), hI2⟩

/-- **The preparation**: from the framed `binary W v` on `A`, any framed `W`-bit word on `B`, a blank output and
cleared registers, the loop invariant at `x = v − 1`, `e = 0`. -/
theorem prep_spec (W v v' : ℕ) (σ : CS) (hW : 1 ≤ W) (hv : 1 ≤ v) (hvW : v < 2 ^ W) (hcap : 2 * W + 2 ≤ cap)
    (hA : σ.st sA = frame (binary W v)) (hhA : σ.sh sA = 0) (hB : σ.st sB = frame (binary W v'))
    (hhB : σ.sh sB = 0) (hY : σ.st sY = []) (hhY : σ.sh sY = 0) (hval : ∀ r, σ.val r = 0) :
    ∃ τ : CS, WExec cap prepP σ τ (123 * W + 22) ∧ Inv W (v - 1) 0 τ := by
  have hW1 : 1 ≤ cap := by omega
  have c1 := WExec.inc (cap := cap) rX σ (by rw [hval]; omega)
  set σ1 := σ.setv rX (σ.val rX + 1) with hσ1
  have hX1 : σ1.val rX = 1 := by simp [σ1, hval]
  have c2 := mapPass_spec cap oneOut oneNxt sB sA rX rR (by decide) (by decide) hW1 (binary W v') (binary W v)
    [] [false] true σ1 (by simp) (by simp [σ1, hB, frame_eq_frameP]) (by simp [σ1, hhB])
    (by simp [σ1, hA, frame_eq_frameP]) (by simp [σ1, hhA]) (by simp [hX1])
    (by simp [σ1, Function.update_apply, hval]) (by simp; omega)
  rw [mapS_one (binary W v') (binary W v) (by simp) (by simp; omega),
    FinalPass.Filt.mapS_one_state (binary W v') (binary W v) (by simp) (by simp; omega)] at c2
  set σ2 := (σ1.sets sB (frameP (binary (binary W v').length 1) ++ false :: [])).setv rX false.toNat with hσ2
  have hX2 : σ2.val rX = 0 := by simp [σ2]
  have c3 := wclear_spec cap rX 0 σ2 hX2 (by omega)
  have e3 : σ2.setv rX 0 = σ2 := by rw [← hX2, wsetv_same]
  rw [e3] at c3
  have c4 := WExec.inc (cap := cap) rX σ2 (by rw [hX2]; omega)
  set σ4 := σ2.setv rX (σ2.val rX + 1) with hσ4
  have c5 := mapPass_spec cap subO geN sA sB rX rR (by decide) (by decide) hW1 (binary W v) (binary W 1)
    [] [false] true σ4 (by simp) (by simp [σ4, σ2, σ1, hA, frame_eq_frameP]) (by simp [σ4, σ2, σ1, hhA])
    (by simp [σ4, σ2, frame_eq_frameP]) (by simp [σ4, σ2, σ1, hhB]) (by simp [σ4, hX2])
    (by simp [σ4, σ2, σ1, Function.update_apply, hval]) (by simp; omega)
  rw [mapS_sub W v 1 hv hvW] at c5
  set σ5 := (σ4.sets sA (frameP (binary W (v - 1)) ++ false :: [])).setv rX
    (mapS subO geN (binary W v) (binary W 1) true).2.toNat with hσ5
  have hvW' : v - 1 < 2 ^ W := by omega
  have h1W : 1 < 2 ^ W := by
    calc 1 < 2 := by norm_num
      _ = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have c6 := mapPass_spec cap keepA geN sA sB rF rR (by decide) (by decide) hW1 (binary W (v - 1)) (binary W 1)
    [] [false] false σ5 (by simp) (by simp [σ5]) (by simp [σ5, σ4, σ2, σ1, hhA])
    (by simp [σ5, σ4, σ2, frame_eq_frameP]) (by simp [σ5, σ4, σ2, σ1, hhB])
    (by simp [σ5, σ4, σ2, σ1, Function.update_apply, hval])
    (by simp [σ5, σ4, σ2, σ1, Function.update_apply, hval]) (by simp; omega)
  rw [mapS_keepA geN (binary W (v - 1)) (binary W 1) false (by simp), mapS_ge W (v - 1) 1 false,
    mod_self_lt hvW', mod_self_lt h1W] at c6
  refine ⟨_, WExec.mono (c1.seq (c2.seq (c3.seq (c4.seq (c5.seq c6))))) ?_, ?_⟩
  · simp only [binary_length]; omega
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ5, frame_eq_frameP]
    · simp [σ5, σ4, σ2, σ1, hhA]
    · simp [σ5, σ4, σ2, frame_eq_frameP]
    · simp [σ5, σ4, σ2, σ1, hhB]
    · simp only [WState.setv_val, Function.update_apply, if_true, Bool.not_false, Bool.toNat_true, pow_zero]
      congr 1
    · simp [σ5, σ4, σ2, σ1, Function.update_apply, hval]
    · simp [σ5, σ4, σ2, σ1, Function.update_apply, hval]
    · simp [σ5, σ4, σ2, σ1, Function.update_apply, hval]
    · simp [σ5, σ4, σ2, σ1, Function.update_apply, hval]
    · simp [σ5, σ4, σ2, σ1, hY]
    · simp [σ5, σ4, σ2, σ1, hhY]
    · simp only [WState.setv_val, Function.update_apply, show rX ≠ rF by decide, if_false, if_true]
      exact Bool.toNat_le _

/-- **The emission**: `n` more marks on `Y` (at its end), `E` counted down, `OP` up; nothing else changes. -/
theorem emit_spec (m : ℕ) : ∀ (n : ℕ) (σ : CS), σ.val rE = n → σ.st sY = List.replicate m true → σ.sh sY = m →
    σ.val rOP = m → m + n < cap → n ≤ cap →
    ∃ τ : CS, WExec cap emitP σ τ (11 * n + 1) ∧ τ.st sY = List.replicate (m + n) true ∧ τ.sh sY = m + n ∧
      τ.val rOP = m + n ∧ τ.val rE = 0 ∧ τ.sh sA = σ.sh sA ∧ τ.sh sB = σ.sh sB ∧
      (∀ r, r ≠ rE → r ≠ rOP → τ.val r = σ.val r)
  | 0, σ, hE, hY, hhY, hOP, _, _ => ⟨σ, WExec.mono (WExec.whrF hE) (by omega), by simpa using hY,
      by simpa using hhY, by simpa using hOP, hE, rfl, rfl, fun _ _ _ => rfl⟩
  | n + 1, σ, hE, hY, hhY, hOP, hc, hn => by
    have c1 := WExec.dec (cap := cap) rE σ (by omega)
    set σ1 := σ.setv rE (σ.val rE - 1) with hσ1
    have c2 := emitC_spec cap sY rOP true σ1 (by simp [σ1, hY, hhY]) (by simp [σ1, Function.update_apply, hOP]; omega)
    obtain ⟨τ, e3, h1, h2, h3, h4, h5, h6, h7⟩ := emit_spec (m + 1) n
      (((σ1.sets sY ((σ1.st sY) ++ [true])).seth sY (σ1.sh sY + 1)).setv rOP (σ1.val rOP + 1))
      (by simp [σ1, Function.update_apply, hE])
      (by simp [σ1, hY, List.replicate_succ'])
      (by simp [σ1, hhY])
      (by simp [σ1, Function.update_apply, hOP]) (by omega) (by omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by omega) (c1.seq c2) e3) (by omega), ?_, ?_, ?_, h4, ?_, ?_, ?_⟩
    · rw [h1]; congr 1; omega
    · rw [h2]; omega
    · rw [h3]; omega
    · rw [h5]; simp [σ1, Function.update_apply]
    · rw [h6]; simp [σ1, Function.update_apply]
    · intro r h1' h2'; rw [h7 r h1' h2']; simp [σ1, Function.update_apply, h1', h2']

/-- **The rewind**: `Y`'s head back to `0`, `OP` counted down; nothing else changes. -/
theorem rew_spec : ∀ (n : ℕ) (σ : CS), σ.val rOP = n → σ.sh sY = n → n ≤ cap →
    ∃ τ : CS, WExec cap rewP σ τ (5 * n + 1) ∧ τ.st = σ.st ∧ τ.sh sY = 0 ∧ τ.val rOP = 0 ∧
      τ.sh sA = σ.sh sA ∧ τ.sh sB = σ.sh sB ∧ (∀ r, r ≠ rOP → τ.val r = σ.val r)
  | 0, σ, hOP, hY, _ => ⟨σ, WExec.mono (WExec.whrF hOP) (by omega), rfl, hY, hOP, rfl, rfl, fun _ _ => rfl⟩
  | n + 1, σ, hOP, hY, hn => by
    have c1 := WExec.dec (cap := cap) rOP σ (by omega)
    set σ1 := σ.setv rOP (σ.val rOP - 1) with hσ1
    have c2 := WExec.bwd (cap := cap) sY σ1
    obtain ⟨τ, e3, h1, h2, h3, h4, h5, h6⟩ := rew_spec n (σ1.seth sY (σ1.sh sY - 1))
      (by simp [σ1, Function.update_apply, hOP]) (by simp [σ1, hY]) (by omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by omega) (c1.seq c2) e3) (by omega), by rw [h1]; rfl, h2, h3, ?_, ?_, ?_⟩
    · rw [h4]; simp [σ1, Function.update_apply]
    · rw [h5]; simp [σ1, Function.update_apply]
    · intro r hr; rw [h6 r hr]; simp [σ1, Function.update_apply, hr]

/-! ## The zero word on `B` -/

theorem binary_zero : ∀ W : ℕ, binary W 0 = List.replicate W false
  | 0 => rfl
  | W + 1 => by rw [binary_succ, binary_zero W]; rfl

theorem frameP_snoc (l : List Bool) (b : Bool) : frameP (l ++ [b]) = frameP l ++ [true, b] := by
  simp [frameP]

/-- The markers of a framed word: position `2i` reads `i < |w|`. -/
theorem frame_even' (bs : List Bool) (i : ℕ) : readTapeBit (frame bs) (2 * i) = decide (i < bs.length) := by
  induction bs generalizing i with
  | nil => cases i <;> rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      have hj : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
      rw [hj]
      show readTapeBit (frame bs) (2 * j) = _
      rw [ih j]
      simp

/-- The state after `j` rounds of `mkLoop`. -/
def stM (σ0 : CS) (j : ℕ) : CS :=
  ⟨fun i => if i = sA then 2 * j else if i = sB then 2 * j else σ0.sh i,
   fun i => if i = sB then frameP (List.replicate j false) else σ0.st i,
   fun r => if r = rE then 2 * j else if r = rOP then 2 * j else σ0.val r, σ0.cell⟩

theorem mk_round (σ0 : CS) (j : ℕ) (hj : 2 * j + 2 < cap) :
    WExec cap (.seq (emitC sB rOP true) (.seq (emitC sB rOP false) (.seq (WM.fwdC sA rE) (WM.fwdC sA rE))))
      (stM σ0 j) (stM σ0 (j + 1)) 27 := by
  have c1 := emitC_spec cap sB rOP true (stM σ0 j) (by simp [stM, frameP]; omega) (by simp [stM]; omega)
  set σ1 := (((stM σ0 j).sets sB ((stM σ0 j).st sB ++ [true])).seth sB ((stM σ0 j).sh sB + 1)).setv rOP
    ((stM σ0 j).val rOP + 1) with hσ1
  have c2 := emitC_spec cap sB rOP false σ1 (by simp [σ1, stM, frameP]; omega) (by simp [σ1, stM]; omega)
  set σ2 := ((σ1.sets sB (σ1.st sB ++ [false])).seth sB (σ1.sh sB + 1)).setv rOP (σ1.val rOP + 1) with hσ2
  have c3 := wfwdC_spec cap sA rE σ2 (by simp [σ2, σ1, stM]; omega)
  set σ3 := (σ2.seth sA (σ2.sh sA + 1)).setv rE (σ2.val rE + 1) with hσ3
  have c4 := wfwdC_spec cap sA rE σ3 (by simp [σ3, σ2, σ1, stM]; omega)
  have heq : (σ3.seth sA (σ3.sh sA + 1)).setv rE (σ3.val rE + 1) = stM σ0 (j + 1) := by
    apply WState.eq
    · funext i
      simp only [σ3, σ2, σ1, stM, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      fin_cases i <;> simp <;> omega
    · funext i
      simp only [σ3, σ2, σ1, stM, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      fin_cases i <;> simp [List.replicate_succ', frameP_snoc]
    · funext r
      simp only [σ3, σ2, σ1, stM, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      fin_cases r <;> simp <;> omega
    · rfl
  rw [heq] at c4
  exact WExec.mono (c1.seq (c2.seq (c3.seq c4))) (by omega)

theorem mk_loop (σ0 : CS) (W v : ℕ) (hA : σ0.st sA = frame (binary W v)) (hcap : 2 * W + 2 ≤ cap) :
    ∀ m j, j + m = W → WExec cap mkLoop (stM σ0 j) (stM σ0 W) (29 * m + 1) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    have hjW : j = W := by omega
    subst hjW
    refine WExec.mono (WExec.whsF ?_) (by omega)
    simp only [wbit, stM, if_true, show (sA : Fin 3) ≠ sB by decide, if_false, hA]
    rw [frame_even' (binary j v) j]
    simp
  | succ m ih =>
    intro j hj
    have hb : wbit (stM σ0 j) sA = true := by
      simp only [wbit, stM, if_true, show (sA : Fin 3) ≠ sB by decide, if_false, hA]
      rw [frame_even' (binary W v) j]
      simp [binary_length]; omega
    have := WExec.whsT hb (mk_round cap σ0 j (by omega)) (ih (j + 1) (by omega))
    exact WExec.mono this (by omega)

/-- The zero word's cost bound. -/
def mkCost (W : ℕ) : ℕ := 29 * W + 1 + 1 + (7 + 1 + (5 * (2 * W + 1) + 1 + 1 + (5 * (2 * W) + 1)))

/-- **The zero word on `B`**: from a blank `B`, `A`'s head, `E` and `OP` at `0`, the machine leaves
`frame (binary W 0)` on `B` and every head and register as it found them. -/
theorem mk_spec (W v : ℕ) (σ : CS) (hcap : 2 * W + 2 ≤ cap) (hA : σ.st sA = frame (binary W v)) (hhA : σ.sh sA = 0)
    (hB : σ.st sB = []) (hhB : σ.sh sB = 0) (hE : σ.val rE = 0) (hOP : σ.val rOP = 0) :
    ∃ τ : CS, WExec cap mkB σ τ (mkCost W) ∧ τ.st sA = σ.st sA ∧ τ.st sB = frame (binary W 0) ∧
      τ.st sY = σ.st sY ∧ (∀ i, τ.sh i = σ.sh i) ∧ (∀ r, τ.val r = σ.val r) := by
  have h0 : stM σ 0 = σ := by
    apply WState.eq
    · funext i; simp only [stM]; fin_cases i <;> simp [hhA, hhB]
    · funext i; simp only [stM]; fin_cases i <;> simp [hB, frameP]
    · funext r; simp only [stM]; fin_cases r <;> simp [hE, hOP]
    · rfl
  have l1 := mk_loop cap σ W v hA hcap W 0 (by omega)
  rw [h0] at l1
  have c2 := emitC_spec cap sB rOP false (stM σ W) (by simp [stM, frameP]; omega) (by simp [stM]; omega)
  set σ2 := (((stM σ W).sets sB ((stM σ W).st sB ++ [false])).seth sB ((stM σ W).sh sB + 1)).setv rOP
    ((stM σ W).val rOP + 1) with hσ2
  have c3 := wrewind_spec cap sB rOP (2 * W + 1) σ2 (by simp [σ2, stM]) (by simp [σ2, stM]; omega)
  set σ3 := (σ2.setv rOP 0).seth sB (σ2.sh sB - (2 * W + 1)) with hσ3
  have c4 := wrewind_spec cap sA rE (2 * W) σ3 (by simp [σ3, σ2, stM]) (by simp [σ3, σ2, stM]; omega)
  refine ⟨_, WExec.mono (l1.seq (c2.seq (c3.seq c4))) (by unfold mkCost; omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp [σ3, σ2, stM]
  · simp [σ3, σ2, stM, frame_eq_frameP, binary_zero]
  · simp [σ3, σ2, stM]
  · intro i
    simp only [σ3, σ2, stM, WState.seth_sh, WState.setv_sh, WState.sets_sh, Function.update_apply]
    fin_cases i <;> simp [hhA, hhB] <;> omega
  · intro r
    simp only [σ3, σ2, stM, WState.seth_val, WState.setv_val, WState.sets_val, Function.update_apply]
    fin_cases r <;> simp [hE, hOP]

/-- The program's cost bound at width `W`. -/
def clogCost (W : ℕ) : ℕ :=
  mkCost W + 1 + (123 * W + 22 + 1 + (W * (82 * W + 24) + 1 + 1 + (11 * W + 1 + 1 + (5 * W + 1 + 1 + (4 + 1 + 4)))))

/-- **`⌈log₂ x⌉` in unary**: from `binary W (x+1)` framed on `A`, a blank `B` and output, and cleared registers
(capacity `≥ 2W + 2`), the program leaves `1^{⌈log₂ x⌉}` on `Y`; every head and register is back at `0`. -/
theorem clogP_spec (W x : ℕ) (σ0 : CS) (hW : 1 ≤ W) (hx : 2 * x + 2 ≤ 2 ^ W) (hcap : 2 * W + 2 ≤ cap)
    (hA0 : σ0.st sA = frame (binary W (x + 1))) (hhA0 : σ0.sh sA = 0) (hB0 : σ0.st sB = [])
    (hhB0 : σ0.sh sB = 0) (hY0 : σ0.st sY = []) (hhY0 : σ0.sh sY = 0) (hval0 : ∀ r, σ0.val r = 0) :
    ∃ τ : CS, WExec cap clogP σ0 τ (clogCost W) ∧ τ.st sY = List.replicate (Nat.clog 2 x) true ∧
      (∀ i, τ.sh i = 0) ∧ (∀ r, τ.val r = 0) := by
  obtain ⟨σ, e0, hA, hB, hY, hsh, hval⟩ := mk_spec cap W (x + 1) σ0 hcap hA0 hhA0 hB0 hhB0 (hval0 _) (hval0 _)
  rw [hA0] at hA
  rw [hY0] at hY
  have hhA : σ.sh sA = 0 := by rw [hsh, hhA0]
  have hhB : σ.sh sB = 0 := by rw [hsh, hhB0]
  have hhY : σ.sh sY = 0 := by rw [hsh, hhY0]
  have hval : ∀ r, σ.val r = 0 := fun r => by rw [hval r, hval0]
  have hx1 : x + 1 < 2 ^ W := by omega
  have hcW : Nat.clog 2 x ≤ W :=
    (Nat.clog_le_iff_le_pow (by norm_num)).2 (by omega)
  obtain ⟨τ1, e1, hI1⟩ := prep_spec cap W (x + 1) 0 σ hW (by omega) hx1 hcap hA hhA hB hhB hY hhY hval
  rw [Nat.add_sub_cancel] at hI1
  obtain ⟨τ2, e2, hI2⟩ := loop_spec cap W x (by omega) hcap hcW (Nat.clog 2 x) 0 τ1 hI1 (by omega)
  obtain ⟨-, hhA2, -, hhB2, hF2, hG2, hR2, hE2, hOP2, hY2, hhY2, hX2⟩ := hI2
  obtain ⟨τ3, e3, h1, h2, h3, h4, h5a, h5b, h5⟩ := emit_spec cap 0 (Nat.clog 2 x) τ2 hE2 (by simpa using hY2)
    (by simpa using hhY2) (by simpa using hOP2) (by omega) (by omega)
  obtain ⟨τ4, e4, h6, h7, h8, h8a, h8b, h8r⟩ := rew_spec cap (Nat.clog 2 x) τ3 (by rw [h3]; omega)
    (by rw [h2]; omega) (by omega)
  have hG4 : τ4.val rG ≤ 1 := by rw [h8r rG (by decide), h5 rG (by decide) (by decide)]; exact hG2
  have c5 := wclear_spec cap rG (τ4.val rG) τ4 rfl (by omega)
  set τ5 := τ4.setv rG 0 with hτ5
  have hX5 : τ5.val rX ≤ 1 := by
    simp only [τ5, WState.setv_val, Function.update_apply, show rX ≠ rG by decide, if_false]
    rw [h8r rX (by decide), h5 rX (by decide) (by decide)]; exact hX2
  have c6 := wclear_spec cap rX (τ5.val rX) τ5 rfl (by omega)
  refine ⟨_, WExec.mono (e0.seq (e1.seq (e2.seq (e3.seq (e4.seq (c5.seq c6)))))) ?_, ?_, ?_, ?_⟩
  · unfold clogCost
    have : Nat.clog 2 x * (82 * W + 24) ≤ W * (82 * W + 24) := Nat.mul_le_mul_right _ hcW
    omega
  · simp only [τ5, WState.setv_st]; rw [h6, h1]; simp
  · intro i
    simp only [τ5, WState.setv_sh]
    fin_cases i
    · show τ4.sh sA = 0; rw [h8a, h5a, hhA2]
    · show τ4.sh sB = 0; rw [h8b, h5b, hhB2]
    · exact h7
  · intro r
    simp only [τ5, WState.setv_val, Function.update_apply]
    by_cases hrX : r = rX
    · rw [if_pos hrX]
    · rw [if_neg hrX]
      by_cases hrG : r = rG
      · rw [if_pos hrG]
      · rw [if_neg hrG]
        by_cases hrOP : r = rOP
        · subst hrOP; exact h8
        · rw [h8r r hrOP]
          by_cases hrE : r = rE
          · subst hrE; exact h4
          · rw [h5 r hrE hrOP]
            have hr : r = rF ∨ r = rR := by
              revert hrX hrG hrOP hrE; fin_cases r <;> decide
            rcases hr with rfl | rfl
            · rw [hF2]
              have : ¬ 2 ^ Nat.clog 2 x < x := by have := Nat.le_pow_clog (by norm_num : 1 < 2) x; omega
              simp [this]
            · exact hR2

end NearCubicWires.WireExponent3_5.UnionMachine.FrontClog
