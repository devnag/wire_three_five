import Proof.Wire_3_5.FinalPass.DigsDig1

/-! # `DigsW`'s body, part 5: one circuit's weights at digit `d` (P3:2596-2599)

The selected child's `S = |supp_i|` weights are read in order (`weightsW`: `R 20` counted down, one `wBodyW` each),
appending `emitList oOff d B p o ws` (occurrences `o, …, o + S − 1`). `dSt` is the loop's state (reading position,
output, `R 20`, `R 37`), with its algebra `dSt_setv20`, `dSt_step`. Main declarations: `dSt`, **`weights_spec`**.
Paper quantity: digit `d` of the reduced coefficients `a_{i,k}`, `k < |supp_i|`, of circuit `i`'s block of `L_g`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires.RepairRepresentation (natWord intWord)

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- The weights loop's state: reading position `j`, occurrence `o`, output `l`, countdown `k`. -/
def dSt (τ : WState ns nr) (E Dg : Fin (ns + 1)) (j o : ℕ) (l : List Bool) (k : ℕ) : WState ns nr :=
  at2 (outAt ((τ.setv (R 20) k).setv (R 37) o) Dg (R 34) l) E (R 14) j

theorem dSt_setv20 (τ : WState ns nr) (E Dg : Fin (ns + 1)) (j o : ℕ) (l : List Bool) (k v : ℕ) :
    (dSt R τ E Dg j o l k).setv (R 20) v = dSt R τ E Dg j o l v := by
  unfold dSt; wst_eq

theorem dSt_step (τ : WState ns nr) (E Dg : Fin (ns + 1)) (_hED : E ≠ Dg) (j o : ℕ) (l : List Bool) (k : ℕ)
    (j' o' : ℕ) (l' : List Bool) :
    at2 (outAt ((dSt R τ E Dg j o l k).setv (R 37) o') Dg (R 34) l') E (R 14) j' = dSt R τ E Dg j' o' l' k := by
  unfold dSt; wst_eq

theorem wCost_mono (L L' p d off o o' : ℕ) (hL : L ≤ L') (ho : o ≤ o') : wCost L p d off o ≤ wCost L' p d off o' := by
  unfold wCost modCost2 coreCost encCost
  have : L * (bitCost2 p + 2) ≤ L' * (bitCost2 p + 2) := Nat.mul_le_mul_right _ hL
  omega

/-- The weights: `R 20` counted down, one weight's digit each. -/
def weightsW (E Dg : Fin (ns + 1)) : WM ns nr := countW (R 20) (wBodyW R E Dg)

theorem weights_spec (E Dg : Fin (ns + 1)) (hED : E ≠ Dg) (ws : List ℤ) (Lm : ℕ)
    (hLm : ∀ w ∈ ws, natBitLength w.natAbs ≤ Lm) (c rest : List Bool) (j0 p B d off o : ℕ) (l : List Bool)
    (hp : 1 ≤ p) (hpc : p ≤ cap) (hB : B < p) (τ : WState ns nr) (hst : τ.st E = frame c)
    (hd : c.drop j0 = ws.flatMap intWord ++ rest) (hP : τ.val (R 2) = p) (hBv : τ.val (R 25) = B)
    (hdv : τ.val (R 36) = d) (hov : τ.val (R 4) = off) (hz : Zs R τ wL)
    (hjc : j0 + (ws.flatMap intWord).length ≤ cap) (hdc : d ≤ cap) (hn : ws.length ≤ cap)
    (hlc : (l ++ emitList off d B p o ws).length + off + o + ws.length + 2 ≤ cap) :
    WExec cap (weightsW R E Dg) (dSt R τ E Dg j0 o l ws.length)
      (dSt R τ E Dg (j0 + (ws.flatMap intWord).length) (o + ws.length) (l ++ emitList off d B p o ws) 0)
      (ws.length * (wCost Lm p d off (o + ws.length) + 4) + 1) := by
  have hF := count_spec cap (R 20) (wBodyW R E Dg) ws.length (wCost Lm p d off (o + ws.length)) hn
    (fun k => dSt R τ E Dg (j0 + ((ws.take k).flatMap intWord).length) (o + k)
      (l ++ emitList off d B p o (ws.take k)) (ws.length - k))
    (fun k _ => by simp [dSt, at2, outAt])
    (fun k hk => by
      have hsplit := fm_split ws k
      have hdk := fm_drop ws k hk
      have htk := fm_take ws k hk
      have hlen : ((ws.take k).flatMap intWord).length + (intWord ws[k]).length ≤ (ws.flatMap intWord).length := by
        rw [hsplit, hdk]; simp
      have hel := emitList_take off d B p o ws k hk
      have hpre : (l ++ emitList off d B p o (ws.take (k + 1))).length ≤ (l ++ emitList off d B p o ws).length := by
        have e := emitList_append off d B p o (ws.take (k + 1)) (ws.drop (k + 1))
        rw [List.take_append_drop] at e
        rw [e]; simp only [List.length_append]; omega
      rw [dSt_setv20]
      have dw := wBody_spec cap R E Dg hED ws[k] c ((ws.drop (k + 1)).flatMap intWord ++ rest)
        (j0 + ((ws.take k).flatMap intWord).length) p B d off (o + k) (l ++ emitList off d B p o (ws.take k))
        hp hpc hB (dSt R τ E Dg (j0 + ((ws.take k).flatMap intWord).length) (o + k)
          (l ++ emitList off d B p o (ws.take k)) (ws.length - k - 1)) (by simp [dSt, at2, outAt, hst, Function.update_apply, hED]) (by simp [dSt, at2])
        (by simp [dSt, at2]) (by rw [← List.drop_drop, hd, hsplit, List.append_assoc, List.drop_left, hdk,
          List.append_assoc])
        (by simp [dSt, at2, outAt, hP]) (by simp [dSt, at2, outAt, hBv]) (by simp [dSt, at2, outAt, hdv])
        (by simp [dSt, at2, outAt, hov]) (by simp [dSt, at2, outAt])
        (by simp [dSt, at2, outAt, Function.update_apply, hED.symm]) (by simp [dSt, at2, outAt, Function.update_apply, hED.symm])
        (by simp [dSt, at2, outAt])
        (fun r hr => by
          have h20 : r ≠ 20 := by rintro rfl; revert hr; decide
          have h37 : r ≠ 37 := by rintro rfl; revert hr; decide
          have h34 : r ≠ 34 := by rintro rfl; revert hr; decide
          have h14 : r ≠ 14 := by rintro rfl; revert hr; decide
          have := hz r hr
          simp [dSt, at2, outAt, Function.update_apply, R.injective.ne h20, R.injective.ne h37, R.injective.ne h34,
            R.injective.ne h14, this])
        (by omega) hdc (by rw [hel] at hpre; simp at hpre hlc ⊢; omega)
      refine WExec.cast cap dw ?_ (wCost_mono _ _ _ _ _ _ _ (hLm ws[k] (List.getElem_mem hk)) (by omega))
      rw [dSt_step R τ E Dg hED, List.append_assoc, ← hel, htk, show ws.length - (k + 1) = ws.length - k - 1 by omega,
        show o + k + 1 = o + (k + 1) by ring, Nat.add_assoc])
  have e0 : dSt R τ E Dg (j0 + ((ws.take 0).flatMap intWord).length) (o + 0) (l ++ emitList off d B p o (ws.take 0))
      (ws.length - 0) = dSt R τ E Dg j0 o l ws.length := by simp [emitList]
  rw [e0, Nat.sub_self, List.take_length] at hF
  exact hF

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
