import Proof.Wire_3_5.Primitive.Writers.ThrN1

/-! # c4 THR block, the hash bits of a THR call: read off its input word

The THR stage's input is `frame (req.word ++ frame hb)`, the request's word followed by the framed bits of the fixed
hash, and its output must end with `frame hb` (`Plan.seedWord` at a THR call). The request's word is the data stage's
`reqW n true codes cc (natListWord translation)`. The register program `hbXW` parses it on stream `0` and copies the
logical bits that follow onto stream `121`. It skips `n`, reads the mode bit, reads `|codes|` and skips the codes, reads
`|cc|` and skips the carriers' codes (PA's `skipNatM`, `readNatM`, `skipCodesW`). Then it copies the translation list
to a scratch stream (`CopyNat.copyNatListM`) and the remaining bits `hbF = frame hb`, marked, to stream `121`
(`CopyNat.copyBit` in a loop).

* `hQ`, `hOP` (registers), `sD`, `sZ` (streams), **`hbXW`**; `seth_appendO`, `seth_seth`, `cpl_spec` (the copy loop);
  **`hbX_spec`**: from the cell's entry, stream `121` holds `marks hbF` and stream `0` is kept.

Paper quantity of the main type: the framed hash bits `frame hb` of the THR input word (P3:2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrHB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable (cap : ℕ)

/-- The list copy's registers `420 … 428`. -/
def hQ : Fin 9 ↪ Fin LNR := ⟨fun i => ⟨420 + i.val, by have := i.isLt; unfold LNR; omega⟩,
  fun a b h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩

theorem hQ_val (i : Fin 9) : (hQ i).val = 420 + i.val := rfl

/-- The bit copy's length register. -/
def hOP : Fin LNR := ⟨440, by decide⟩

/-- The scratch stream of the translation list. -/
abbrev sD : Fin (LNS 0 + 1) := sk 0 120
/-- **The hash bits' stream.** -/
abbrev sZ : Fin (LNS 0 + 1) := sk 0 121

/-- **The hash bits' program.** -/
def hbXW : WM (LNS 0) LNR :=
  .seq (skipNatM true (sk 0 0) dF dC) (.seq (.fwd (sk 0 0)) (.seq (.fwd (sk 0 0))
  (.seq (readNatM true (sk 0 0) dF dC dK dP dT) (.seq (skipCodesW 0)
  (.seq (readNatM true (sk 0 0) dF dC dK dP dT) (.seq (skipCodesW 0)
  (.seq (CopyNat.copyNatListM true (sk 0 0) sD hQ)
  (.whs (sk 0 0) (CopyNat.copyBit true (sk 0 0) sZ hOP)))))))))

theorem seth_appendO (σ : WState (LNS 0) LNR) (i o : Fin (LNS 0 + 1)) (hio : i ≠ o) (OP : Fin LNR) (k : ℕ)
    (u : List Bool) : appendO (σ.seth i k) o OP u = (appendO σ o OP u).seth i k := by
  apply WState.eq
  · funext j
    simp only [appendO_sh, WState.seth_sh, Function.update_apply]
    by_cases h1 : j = o <;> by_cases h2 : j = i <;> simp_all
  · simp
  · simp
  · simp

theorem seth_seth (σ : WState (LNS 0) LNR) (i : Fin (LNS 0 + 1)) (k k' : ℕ) :
    (σ.seth i k).seth i k' = σ.seth i k' := by
  apply WState.eq
  · funext j
    simp only [WState.seth_sh, Function.update_apply]
    by_cases h : j = i <;> simp [h]
  · simp
  · simp
  · simp

theorem seth_self (σ : WState (LNS 0) LNR) (i : Fin (LNS 0 + 1)) (k : ℕ) (h : σ.sh i = k) : σ.seth i k = σ := by
  apply WState.eq
  · funext j
    simp only [WState.seth_sh, Function.update_apply]
    by_cases hj : j = i
    · subst hj; simp [h]
    · simp [hj]
  · simp
  · simp
  · simp

theorem s0Z : (sk 0 0 : Fin (LNS 0 + 1)) ≠ sZ := fun e => absurd (sk_inj 0 e) (by decide)

/-- **The bit copy's loop**: the marked bits `enc true u` then the terminator on stream `0` go to the end of `sZ`. -/
theorem cpl_spec (u : List Bool) : ∀ (σ : WState (LNS 0) LNR) (pre : List Bool),
    σ.st (sk 0 0) = pre ++ enc true u ++ [false] → σ.sh (sk 0 0) = pre.length →
    σ.sh sZ = (σ.st sZ).length → σ.val hOP + 2 * u.length + 2 ≤ cap →
    WExec cap (.whs (sk 0 0) (CopyNat.copyBit true (sk 0 0) sZ hOP)) σ
      ((appendO σ sZ hOP (marks u)).seth (sk 0 0) (pre.length + 2 * u.length)) (22 * u.length + 1) := by
  induction u with
  | nil =>
    intro σ pre hst hsh hZ hc
    have hb : wbit σ (sk 0 0) = false := by
      simp only [wbit, hst, hsh]
      simp [ParseNat.enc, marks, readTapeBit]
    have e : (appendO σ sZ hOP (marks [])).seth (sk 0 0) (pre.length + 2 * ([] : List Bool).length) = σ := by
      have hm : marks ([] : List Bool) = [] := by simp [marks]
      rw [hm, appendO_nil]
      exact seth_self σ _ _ (by rw [hsh]; simp)
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by omega)
  | cons b u ih =>
    intro σ pre hst hsh hZ hc
    have hencb : enc true (b :: u) = true :: b :: enc true u := by simp [ParseNat.enc, marks]
    have hb : wbit σ (sk 0 0) = true := by
      simp only [wbit, hst, hsh, hencb]
      simp [readTapeBit]
    have h1 := CopyNat.copyBit_spec cap true (sk 0 0) sZ s0Z hOP σ hZ (by simp at hc; omega)
    have hrb : readTapeBit (σ.st (sk 0 0)) (σ.sh (sk 0 0) + off true) = b := by
      rw [hst, hsh, hencb]
      simp [off, readTapeBit, List.getD_append_right]
    rw [hrb] at h1
    set σ1 := (appendO σ sZ hOP [true, b]).seth (sk 0 0) (σ.sh (sk 0 0) + stp true) with hσ1
    have st1 : σ1.st (sk 0 0) = (pre ++ [true, b]) ++ enc true u ++ [false] := by
      rw [hσ1]; simp [appendO_st, Function.update_apply, s0Z, hst, hencb]
    have sh1 : σ1.sh (sk 0 0) = (pre ++ [true, b]).length := by
      rw [hσ1]; simp [hsh, stp]
    have hZ1 : σ1.sh sZ = (σ1.st sZ).length := by
      rw [hσ1]; simp [Function.update_apply, Ne.symm s0Z, hZ]
    have hc1 : σ1.val hOP + 2 * u.length + 2 ≤ cap := by
      rw [hσ1]; simp at hc ⊢; omega
    have h2 := ih σ1 (pre ++ [true, b]) st1 sh1 hZ1 hc1
    refine WExec.cast cap (WExec.whsT hb h1 h2) ?_ (by simp; omega)
    rw [hσ1, seth_appendO _ _ _ s0Z, seth_seth, appendO_append]
    have hm : marks (b :: u) = [true, b] ++ marks u := by simp [marks]
    rw [hm]
    congr 1
    simp
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.ThrHB
