import Proof.Wire_3_5.Primitive.Writers.HashCellD
import Proof.Wire_3_5.Primitive.Writers.HashPops9
import Proof.Wire_3_5.FinalPass.FreeGen2

/-! # HASH setup (C), P2b part 3: the populations loop's registers and layout on the cell

P3:2253-2293 (the populations `T_d^±` of the HASH call's printed objective, one per selection `g`, prime `p ≤ cut`,
digit `d` and sign) and P3:2596-2604 (`τ₀` digits per prime): after the docks the cell holds the call's numbers in unary
(`|𝒢|` on `139`, `τ₀` on `144`, `B_*` on `147`) and the aux filter's cap and length in `G 0`, `G 1`. Part B loads the
populations loop's inputs: `GR := |𝒢|`, `R 3 := τ₀`, `R 4 := 2Σ|X_j|` (the occurrences' pool offset), and
`R 0 := a' = B_* / (4096·cap_aux)` (`B_* = a'·4096·cap_aux`, UnaryArith's `divW`, `4096 = 2^{12}` by `pow2W`, the product
by FreeGen's `mulW`). The loop runs on `hPL`: payloads `133 … 136`, digits `137`, primes `130`, output `138`, the digit
program's registers `0 … 47`, the loop's `48 … 54`.

* `hR`, **`hPL`**, **`hPL_ok`**; `rB`, `rM`, `mS`, `dR`, `incN`, `incN_spec`; `cBW`, `cBCost`, **`cB_run`**.

Paper quantities of the main type: the populations loop's inputs `|𝒢|`, `τ₀`, `oOff`, `a'` (P3:2253-2293). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.SymDec

/-- The digit program's registers `0 … 47`. -/
def hR : Fin FinalPass.Digs.digsK ↪ Fin LNR :=
  ⟨fun j => ⟨j.val, by have := j.isLt; simp only [FinalPass.Digs.digsK] at this; unfold LNR; omega⟩,
    fun a b h => Fin.ext (by have := congrArg Fin.val h; simpa using this)⟩

/-- **The populations loop's layout on the cell.** -/
def hPL (x : ℕ) : HashPops.PL (LNS x) LNR where
  Pay := fun i => sk x ⟨133 + i.val, by omega⟩
  Dg := sk x 137
  PR := sk x 130
  O := sk x 138
  R := hR
  OP := ⟨48, by decide⟩
  K := ⟨49, by decide⟩
  DL := ⟨50, by decide⟩
  DC := ⟨51, by decide⟩
  T := ⟨52, by decide⟩
  GR := ⟨53, by decide⟩
  PH := ⟨54, by decide⟩

/-- The loop's registers in `PL.regs` order. -/
def hRegs : Fin 9 → Fin LNR :=
  ![⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, hR 1, hR 2, ⟨54, by decide⟩,
    ⟨52, by decide⟩]

theorem hRegs_inj : Function.Injective hRegs := by decide

theorem hRegs_out : ∀ j : Fin FinalPass.Digs.digsK, j.val ≠ 1 → j.val ≠ 2 → ∀ k : Fin 9, hR j ≠ hRegs k := by decide

theorem nG1_3 : G 1 ≠ ⟨3, by decide⟩ := by decide
theorem nG1_53 : G 1 ≠ ⟨53, by decide⟩ := by decide

theorem hPL_ok (x : ℕ) : (hPL x).Ok where
  sInj := by
    intro a b h
    have e := congrArg Fin.val h
    fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp [hPL, sk_val] at e)
  payInj := by
    intro a b h
    have e := congrArg Fin.val h
    simp only [hPL, sk_val] at e
    exact Fin.ext (by omega)
  payNe := by
    intro i
    have hi := i.isLt
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> (have e := congrArg Fin.val h; simp only [hPL, sk_val] at e; omega)
  rInj := hRegs_inj
  rOut := hRegs_out

/-! ## Part B: the loop's inputs -/

def rB : Fin LNR := ⟨80, by decide⟩
def rM : Fin LNR := ⟨81, by decide⟩

/-- `mulW`'s registers: `4096` (in `rP`), `cap_aux` (`G 0`), the product `rM`, three temporaries. -/
def mS : Fin 6 ↪ Fin LNR := ⟨![rP, G 0, rM, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩], by decide⟩

/-- `divW`'s registers: `B_*` (`rB`), the divisor `rM`, the quotient `R 0`, six temporaries. -/
def dR : Fin 9 ↪ Fin LNR :=
  ⟨![rB, rM, ⟨0, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩,
    ⟨90, by decide⟩], by decide⟩

section Gen
variable {ns nr : ℕ} (cap : ℕ)

/-- `k` increments of `r`. -/
def incN (r : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (.inc r) (incN r k)

theorem incN_spec (r : Fin nr) : ∀ (k : ℕ) (σ : WState ns nr), σ.val r + k ≤ cap →
    WExec cap (incN r k) σ (σ.setv r (σ.val r + k)) (4 * k)
  | 0, σ, _ => by
    have e : σ.setv r (σ.val r + 0) = σ := by rw [Nat.add_zero]; exact WState.eq rfl rfl (by simp) rfl
    rw [e]; exact WExec.skip σ
  | k + 1, σ, hc => by
    have h1 := WExec.inc (cap := cap) r σ (by omega)
    have h2 := incN_spec r k (σ.setv r (σ.val r + 1)) (by simp; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext q
    by_cases hq : q = r
    · subst hq; simp; omega
    · simp [Function.update_apply, hq]

end Gen

section B
variable (cap : ℕ) (x : ℕ)

/-- **Part B**: `GR := |𝒢|`, `R 3 := τ₀`, `R 4 := G 1`, `R 0 := B_* / (4096·G 0)`. -/
def cBW : WM (LNS x) LNR :=
  .seq (readUW (sk x 139) ⟨53, by decide⟩) (.seq (readUW (sk x 144) ⟨3, by decide⟩)
    (.seq (FinalPass.Hash4.wcopyR (G 1) ⟨4, by decide⟩ rT) (.seq (readUW (sk x 147) rB)
      (.seq (incN rS 12) (.seq (UnaryArith.pow2W pR) (.seq (FinalPass.FreeGen.mulW mS) (UnaryArith.divW dR)))))))

/-- Part B's steps. -/
def cBCost : ℕ := 8 * UnaryPow.sq cap + 1000000

/-- **Part B, run.** -/
theorem cB_run (σ : WState (LNS x) LNR) (nG τ0 oOff G0 a' Bs : ℕ)
    (s139 : σ.st (sk x 139) = List.replicate nG true) (h139 : σ.sh (sk x 139) = 0)
    (s144 : σ.st (sk x 144) = List.replicate τ0 true) (h144 : σ.sh (sk x 144) = 0)
    (s147 : σ.st (sk x 147) = List.replicate Bs true) (h147 : σ.sh (sk x 147) = 0)
    (g1 : σ.val (G 1) = oOff) (g0 : σ.val (G 0) = G0) (hz : ∀ r : Fin LNR, r.val < 250 → σ.val r = 0)
    (hbd : ∀ r, σ.val r ≤ cap) (hBs : Bs = a' * (4096 * G0)) (hG0 : 1 ≤ G0)
    (hc : nG + τ0 + oOff + Bs + 4096 * G0 + 2 ^ 13 ≤ cap) :
    ∃ τ c, WExec cap (cBW x) σ τ c ∧ c ≤ cBCost cap ∧ τ.st = σ.st ∧
      (∀ s, s ≠ sk x 139 → s ≠ sk x 144 → s ≠ sk x 147 → τ.sh s = σ.sh s) ∧ τ.cell = σ.cell ∧
      τ.val ⟨53, by decide⟩ = nG ∧ τ.val ⟨3, by decide⟩ = τ0 ∧ τ.val ⟨4, by decide⟩ = oOff ∧
      τ.val ⟨0, by decide⟩ = a' ∧
      (∀ r : Fin LNR, r.val < 60 → r.val ≠ 0 → r.val ≠ 3 → r.val ≠ 4 → r.val ≠ 53 → τ.val r = 0) ∧
      (∀ r, τ.val r ≤ cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hl := UnaryPow.lin_le_sq cap
  have p13 : (2 : ℕ) ^ 13 = 8192 := by norm_num
  have p12 : (2 : ℕ) ^ 12 = 4096 := by norm_num
  have hdiv : Bs / (4096 * G0) = a' := by rw [hBs, Nat.mul_div_cancel _ (by omega)]
  have hmod : Bs % (4096 * G0) = 0 := by rw [hBs, Nat.mul_mod_left]
  -- GR
  have e1 := readU_spec cap (sk x 139) ⟨53, by decide⟩ nG 0 σ s139 h139 (hz _ (by decide)) (by omega)
  set σ1 := (σ.seth (sk x 139) nG).setv ⟨53, by decide⟩ (0 + nG) with hσ1
  -- R 3
  have e2 := readU_spec cap (sk x 144) ⟨3, by decide⟩ τ0 0 σ1 (by simp [σ1, s144]) (by
      simp [σ1, Function.update_apply, skne x 144 139 (by decide), h144])
    (by simp [σ1, Function.update_apply]; exact hz _ (by decide)) (by omega)
  set σ2 := (σ1.seth (sk x 144) τ0).setv ⟨3, by decide⟩ (0 + τ0) with hσ2
  -- R 4
  have e3 := FinalPass.Hash4.wcopyR_spec cap (G 1) ⟨4, by decide⟩ rT (by decide) (by decide) (by decide) σ2
    (by simp [σ2, σ1, Function.update_apply]; exact hz _ (by decide))
    (by simp [σ2, σ1, Function.update_apply, rT]; exact hz _ (by decide))
    (by simp [σ2, σ1, Function.update_apply]; exact hbd _)
  have v3 : σ2.val (G 1) = oOff := by simp [σ2, σ1, Function.update_apply, g1, nG1_3, nG1_53]
  rw [v3] at e3
  set σ3 := σ2.setv ⟨4, by decide⟩ oOff with hσ3
  -- B_*
  have e4 := readU_spec cap (sk x 147) rB Bs 0 σ3 (by simp [σ3, σ2, σ1, s147])
    (by simp [σ3, σ2, σ1, Function.update_apply, skne x 147 139 (by decide), skne x 147 144 (by decide), h147])
    (by simp [σ3, σ2, σ1, Function.update_apply, rB]; exact hz _ (by decide)) (by omega)
  set σ4 := (σ3.seth (sk x 147) Bs).setv rB (0 + Bs) with hσ4
  -- 12 in rS
  have zS4 : σ4.val rS = 0 := by simp [σ4, σ3, σ2, σ1, Function.update_apply, rS, rB]; exact hz _ (by decide)
  have e5 := incN_spec cap rS 12 σ4 (by omega)
  rw [zS4] at e5
  set σ5 := σ4.setv rS (0 + 12) with hσ5
  -- 4096 in rP
  have zP5 : σ5.val rP = 0 := by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, rS, rP, rB]; exact hz _ (by decide)
  have zQ5 : σ5.val rQ = 0 := by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, rS, rQ, rB]; exact hz _ (by decide)
  have zW5 : σ5.val rW = 0 := by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, rS, rW, rB]; exact hz _ (by decide)
  have e6 := UnaryArith.pow2W_spec cap pR σ5 (by simpa [pR] using zP5) (by simpa [pR] using zQ5)
    (by simpa [pR] using zW5) (by simp [pR, σ5]; omega)
  have v6 : σ5.val (pR 0) = 12 := by simp [pR, σ5]
  have p6 : pR 1 = rP := by simp [pR]
  rw [v6, p6, p12] at e6
  set σ6 := σ5.setv rP 4096 with hσ6
  -- 4096 · G0 in rM
  have e7 := FinalPass.FreeGen.mulW_spec cap mS σ6 4096 G0 (by simp [mS, σ6]) (by
      simp [mS, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rP, rS, rB]; exact g0)
    (by
      intro i hi
      fin_cases i
      · exact absurd hi (by decide)
      · exact absurd hi (by decide)
      · simp [mS, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rM, rP, rS, rB]; exact hz _ (by decide)
      · simp [mS, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rM, rP, rS, rB]; exact hz _ (by decide)
      · simp [mS, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rM, rP, rS, rB]; exact hz _ (by decide)
      · simp [mS, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rM, rP, rS, rB]; exact hz _ (by decide))
    (by omega) (by omega) (by omega)
  have p7 : mS 2 = rM := by simp [mS]
  rw [p7] at e7
  set σ7 := σ6.setv rM (4096 * G0) with hσ7
  -- a' in R 0
  have hv : ∀ r : Fin LNR, r.val = 0 ∨ (85 ≤ r.val ∧ r.val ≤ 89) → σ7.val r = 0 := by
    intro r hr
    have n53 : r ≠ ⟨53, by decide⟩ := fun e => by rw [e] at hr; simp at hr
    have n3 : r ≠ ⟨3, by decide⟩ := fun e => by rw [e] at hr; simp at hr
    have n4 : r ≠ ⟨4, by decide⟩ := fun e => by rw [e] at hr; simp at hr
    have nB : r ≠ rB := fun e => by rw [e] at hr; simp [rB] at hr
    have nS : r ≠ rS := fun e => by rw [e] at hr; simp [rS] at hr
    have nP : r ≠ rP := fun e => by rw [e] at hr; simp [rP] at hr
    have nM : r ≠ rM := fun e => by rw [e] at hr; simp [rM] at hr
    simp only [σ7, σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply, n53, n3, n4, nB,
      nS, nP, nM, if_false]
    exact hz r (by omega)
  have e8 := UnaryArith.divW_spec cap dR σ7 (by simp [dR, σ7]; omega) (hv _ (by simp [dR]))
    (hv _ (by simp [dR])) (hv _ (by simp [dR])) (hv _ (by simp [dR])) (hv _ (by simp [dR]))
    (by simp [dR, σ7, σ6, σ5, σ4, Function.update_apply, rB, rM, rP, rS]; omega)
    (by simp [dR, σ7]; omega)
    (by simp [dR, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rB, rM, rP, rS]; rw [hz _ (by decide)]; omega)
    (by omega)
  have v8a : σ7.val (dR 0) = Bs := by simp [dR, σ7, σ6, σ5, σ4, Function.update_apply, rB, rM, rP, rS]
  have v8b : σ7.val (dR 1) = 4096 * G0 := by simp [dR, σ7]
  have v8q : σ7.val (dR 2) = 0 := hv _ (by simp [dR])
  rw [v8a, v8b, v8q, hdiv, hmod, Nat.zero_add] at e8
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8)))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : nG ≤ cap := by omega
    have c2 : τ0 ≤ cap := by omega
    have c3 : oOff ≤ cap := by omega
    have c4 : Bs ≤ cap := by omega
    have m1 : (Bs + 2) * (90 * Bs + 90 * (4096 * G0) + 60) ≤ (cap + 2) * (180 * cap + 60) :=
      Nat.mul_le_mul (by omega) (by omega)
    have m2 : (cap + 2) * (180 * cap + 60) ≤ UnaryPow.sq cap := by unfold UnaryPow.sq; nlinarith
    unfold cBCost
    omega
  · rfl
  · intro s a b c
    simp only [σ7, σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_sh, WState.seth_sh, Function.update_apply, a, b, c, if_false]
  · rfl
  · simp [dR, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rB, rM, rP, rS]
  · simp [dR, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rB, rM, rP, rS]
  · simp [dR, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, rB, rM, rP, rS]
  · simp [dR]
  · intro r h60 h0 h3 h4 h53
    have n53 : r ≠ ⟨53, by decide⟩ := fun e => h53 (by rw [e])
    have n3 : r ≠ ⟨3, by decide⟩ := fun e => h3 (by rw [e])
    have n4 : r ≠ ⟨4, by decide⟩ := fun e => h4 (by rw [e])
    have n0 : r ≠ ⟨0, by decide⟩ := fun e => h0 (by rw [e])
    have nB : r ≠ rB := fun e => by rw [e] at h60; simp [rB] at h60
    have nS : r ≠ rS := fun e => by rw [e] at h60; simp [rS] at h60
    have nP : r ≠ rP := fun e => by rw [e] at h60; simp [rP] at h60
    have nM : r ≠ rM := fun e => by rw [e] at h60; simp [rM] at h60
    have hd0 : dR 0 = rB := by simp [dR]
    have hd2 : dR 2 = ⟨0, by decide⟩ := by simp [dR]
    simp only [hd0, hd2, σ7, σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, Function.update_apply, n53, n3,
      n4, n0, nB, nS, nP, nM, if_false]
    exact hz r (by omega)
  · exact wexec_le cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
      (WExec.seq e7 e8))))))) hbd

end B

end NearCubicWires.WireExponent3_5.PrimAsm.HashCell
