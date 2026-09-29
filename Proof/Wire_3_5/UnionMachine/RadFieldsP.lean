import Proof.Wire_3_5.UnionMachine.RadFields2

/-! # RADIX, stage 4 (3): the record's setup fields, written (P3:2585-2623)

**`fieldsP`** appends the Route-B record's setup fields at marks level 2 on the record stream:
`fieldE 1^R`, `fieldE 0^{Lg}`, then `radEv`'s fields `frame (encT M 0^{2τ})`, `zW M (2τ(M+1))`,
`fieldsU (consFrom M p 2 0 τ)`, `patT p s (2τp+1)`, `[true]`, `[]`, `0^{cap}` (**`fieldsWordB`**, **`fieldsWordB_eq`**,
**`fieldsP_spec`**). Its registers are one block `Fr` (`R`, `Lg`, `cap`, `M`, `τ`, `p`, `s` in `0 … 6`, scratch `7 …`).

Paper quantity of the main type: the RADIX row record's setup fields at Route B's capacities (C2's `radRowRec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadFieldsP
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.UnionMachine.RadFields NearCubicWires.WireExponent3_5.UnionMachine.RadFields2

/-- **The setup fields' word** at `R`, `Lg`, `M`, `τ`, `p`, `s`, `cap`. -/
def fieldsWordB (R Lg M τ p s cap : ℕ) : List Bool :=
  (setupFieldsG (19 + 1) R Lg (radEv M (2 * τ) (consFrom M p 2 0 τ) (patT p s (2 * τ * p + 1)) cap)).flatMap fieldE

theorem fieldsWordB_eq (R Lg M τ p s cap : ℕ) : fieldsWordB R Lg M τ p s cap =
    fieldE (List.replicate R true) ++ (fieldE (List.replicate Lg false) ++
      (fieldE (frame (encT M (List.replicate (2 * τ) 0))) ++ (fieldE (zW M (2 * τ * (M + 1))) ++
        (fieldE (fieldsU (consFrom M p 2 0 τ)) ++ (fieldE (patT p s (2 * τ * p + 1)) ++
          (fieldE [true] ++ (fieldE [] ++ fieldE (List.replicate cap false)))))))) := by
  unfold fieldsWordB
  rw [setupFieldsG_eq]
  simp [radEv]

section W
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (OP : Fin nr) (Fr : Fin 48 ↪ Fin nr)

theorem fne {i j : Fin 48} (h : i ≠ j) : Fr i ≠ Fr j := Fr.injective.ne h

/-- `consW`'s block inside `Fr` (`11 … 34`). -/
def sh11 : Fin 24 ↪ Fin 48 := ⟨fun i => ⟨11 + i.val, by omega⟩, fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp at this; omega)⟩

/-- `C := 2τ` (register `7`, through `35`). -/
def twoTau : WM ns nr := .seq (addTo (Fr 4) (Fr 7) (Fr 35)) (addTo (Fr 4) (Fr 7) (Fr 35))

/-- The digit tuple field. -/
def segC : WM ns nr := .seq (twoTau Fr) (encFieldW O OP (Fr 7) (Fr 3) (Fr 8) (Fr 9))

/-- The mask field. -/
def segD : WM ns nr := .seq (twoTau Fr) (.seq (.dec (Fr 7)) (zFieldW O OP (Fr 7) (Fr 3) (Fr 8) (Fr 9)))

/-- The contribution field. -/
def segE : WM ns nr :=
  .seq (addTo (Fr 5) (Fr 11) (Fr 35)) (.seq (addTo (Fr 3) (Fr 12) (Fr 35)) (.seq (addTo (Fr 4) (Fr 13) (Fr 35))
    (.seq (consW O OP (sh11.trans Fr)) (.seq (WM.clear (Fr 11)) (.seq (WM.clear (Fr 12)) (emitW O OP [true, false]))))))

/-- The residue field's registers `Q := p − 1 − s`. -/
def sQ : Fin 4 ↪ Fin 48 := ⟨![10, 6, 36, 37], by decide⟩

/-- The residue field. -/
def segF : WM ns nr :=
  .seq (twoTau Fr) (.seq (addTo (Fr 5) (Fr 10) (Fr 35)) (.seq (subW (sQ.trans Fr)) (.seq (.dec (Fr 10))
    (.seq (pFieldW O OP (Fr 7) (Fr 6) (Fr 10) (Fr 8) (Fr 9)) (WM.clear (Fr 10))))))

/-- The flag fields and the loop capacity. -/
def segG : WM ns nr :=
  .seq (emitW O OP (m2 true ++ [true, false])) (.seq (emitW O OP [true, false]) (repFieldW O OP (Fr 2) (Fr 8) (Fr 9) false))

/-- **The setup fields.** -/
def fieldsP : WM ns nr :=
  .seq (repFieldW O OP (Fr 0) (Fr 8) (Fr 9) true) (.seq (repFieldW O OP (Fr 1) (Fr 8) (Fr 9) false)
    (.seq (segC O OP Fr) (.seq (segD O OP Fr) (.seq (segE O OP Fr) (.seq (segF O OP Fr) (segG O OP Fr))))))

/-- **The fields' entry**: the seven values in `Fr 0 … 6`, the scratch `Fr 7 …` zero, the output's head at its end. -/
structure Ready (σ : WState ns nr) (R Lg cp M τ p s : ℕ) : Prop where
  v0 : σ.val (Fr 0) = R
  v1 : σ.val (Fr 1) = Lg
  v2 : σ.val (Fr 2) = cp
  v3 : σ.val (Fr 3) = M
  v4 : σ.val (Fr 4) = τ
  v5 : σ.val (Fr 5) = p
  v6 : σ.val (Fr 6) = s
  z : ∀ i : Fin 48, 7 ≤ i.val → σ.val (Fr i) = 0
  ho : σ.sh O = (σ.st O).length

theorem Ready.ao {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s) (hOP : ∀ i, Fr i ≠ OP)
    (u : List Bool) : Ready O Fr (appendO σ O OP u) R Lg cp M τ p s where
  v0 := by rw [ao_val_ne O OP _ _ (hOP 0), h.v0]
  v1 := by rw [ao_val_ne O OP _ _ (hOP 1), h.v1]
  v2 := by rw [ao_val_ne O OP _ _ (hOP 2), h.v2]
  v3 := by rw [ao_val_ne O OP _ _ (hOP 3), h.v3]
  v4 := by rw [ao_val_ne O OP _ _ (hOP 4), h.v4]
  v5 := by rw [ao_val_ne O OP _ _ (hOP 5), h.v5]
  v6 := by rw [ao_val_ne O OP _ _ (hOP 6), h.v6]
  z := fun i hi => by rw [ao_val_ne O OP _ _ (hOP i), h.z i hi]
  ho := ao_ho O OP σ u h.ho

/-- `C := 2τ` on a ready state. -/
theorem twoTau_spec {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s) (hc : 2 * τ ≤ cap) :
    WExec cap (twoTau Fr) σ (σ.setv (Fr 7) (2 * τ)) (36 * τ + 7) := by
  have z35 := h.z 35 (by decide)
  have s1 := addTo_spec cap (Fr 4) (Fr 7) (Fr 35) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) σ z35
    (by rw [h.v4]; omega) (by rw [h.v4, h.z 7 (by decide)]; omega)
  rw [h.v4, h.z 7 (by decide), Nat.zero_add] at s1
  have s2 := addTo_spec cap (Fr 4) (Fr 7) (Fr 35) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide))
    (σ.setv (Fr 7) τ) (by simp [Function.update_apply, z35]) (by simp [Function.update_apply, h.v4]; omega)
    (by simp [Function.update_apply, h.v4]; omega)
  have e1 : (σ.setv (Fr 7) τ).val (Fr 7) = τ := by simp
  have e2 : (σ.setv (Fr 7) τ).val (Fr 4) = τ := by simp [Function.update_apply, h.v4]
  rw [e1, e2, wsetv_setv] at s2
  refine WExec.cast cap (WExec.seq s1 s2) (by rw [show τ + τ = 2 * τ by ring]) (by omega)

theorem setv_zero (σ : WState ns nr) (r : Fin nr) (h : σ.val r = 0) : σ.setv r 0 = σ := by rw [← h, wsetv_same]

theorem back7 {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s) (hOP : ∀ i, Fr i ≠ OP)
    (x : ℕ) (w : List Bool) : (appendO (σ.setv (Fr 7) x) O OP w).setv (Fr 7) 0 = appendO σ O OP w := by
  rw [appendO_setv _ _ _ _ (hOP 7), wsetv_setv, setv_zero _ _ (by rw [ao_val_ne O OP _ _ (hOP 7), h.z 7 (by decide)])]

/-- **The digit tuple field.** -/
theorem segC_spec (hOP : ∀ i, Fr i ≠ OP) {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s)
    (hM : M ≤ cap) (hτ : 2 * τ ≤ cap) (hc : σ.val OP + 2 * τ * (8 * M + 8) + 6 ≤ cap) :
    WExec cap (segC O OP Fr) σ (appendO σ O OP (fieldE (frame (encT M (List.replicate (2 * τ) 0)))))
      (2 * τ * (100 * M + 200) + 36 * τ + 108) := by
  have s1 := twoTau_spec cap O Fr h hτ
  have s2 := encFieldW_spec cap O OP (Fr 7) (Fr 3) (Fr 8) (Fr 9) (hOP 7) (hOP 3) (hOP 8) (hOP 9) (fne Fr (by decide))
    (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide))
    (σ.setv (Fr 7) (2 * τ)) (2 * τ) (by simp) (by simp [Function.update_apply, h.z 8 (by decide)])
    (by simp [Function.update_apply, h.z 9 (by decide)]) (by simp [h.ho]) (by simp [Function.update_apply, h.v3]; omega)
    hτ (by simp [Function.update_apply, h.v3, (hOP 7).symm]; omega)
  have e3 : (σ.setv (Fr 7) (2 * τ)).val (Fr 3) = M := by simp [Function.update_apply, h.v3]
  rw [e3, back7 O OP Fr h hOP] at s2
  exact WExec.mono (WExec.seq s1 s2) (by omega)

/-- **The mask field.** -/
theorem segD_spec (hOP : ∀ i, Fr i ≠ OP) {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s)
    (hτ1 : 1 ≤ τ) (hM : M ≤ cap) (hτ : 2 * τ ≤ cap) (hc : σ.val OP + 2 * τ * (8 * M + 8) + 2 ≤ cap) :
    WExec cap (segD O OP Fr) σ (appendO σ O OP (fieldE (zW M (2 * τ * (M + 1)))))
      (2 * τ * (100 * M + 200) + 36 * τ + 110) := by
  have s1 := twoTau_spec cap O Fr h hτ
  have s2 := WExec.dec (cap := cap) (Fr 7) (σ.setv (Fr 7) (2 * τ)) (by simp; omega)
  rw [wsetv_setv] at s2
  have e7 : (σ.setv (Fr 7) (2 * τ)).val (Fr 7) - 1 = 2 * τ - 1 := by simp
  rw [e7] at s2
  have s3 := zFieldW_spec cap O OP (Fr 7) (Fr 3) (Fr 8) (Fr 9) (hOP 7) (hOP 3) (hOP 8) (hOP 9) (fne Fr (by decide))
    (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide))
    (σ.setv (Fr 7) (2 * τ - 1)) (2 * τ) (by omega) (by simp) (by simp [Function.update_apply, h.z 8 (by decide)])
    (by simp [Function.update_apply, h.z 9 (by decide)]) (by simp [h.ho]) (by simp [Function.update_apply, h.v3]; omega)
    hτ (by simp [Function.update_apply, h.v3, (hOP 7).symm]; omega)
  have e3 : (σ.setv (Fr 7) (2 * τ - 1)).val (Fr 3) = M := by simp [Function.update_apply, h.v3]
  rw [e3, back7 O OP Fr h hOP] at s3
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega)

/-- **The contribution field.** -/
theorem segE_spec (hOP : ∀ i, Fr i ≠ OP) {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s)
    (hp2 : 2 ≤ p) (hM : M + 1 ≤ cap) (hτ : τ ≤ cap) (hp : p ≤ cap)
    (hc : σ.val OP + τ * (2 * ((M + 1) * (4 * p + 4)) + 5 * p + 2) + 2 ≤ cap) :
    WExec cap (segE O OP Fr) σ (appendO σ O OP (fieldE (fieldsU (consFrom M p 2 0 τ))))
      (τ * (digitCost cap M + 4) + 200 * cap + 200) := by
  have z35 := h.z 35 (by decide)
  have s1 := addTo_spec cap (Fr 5) (Fr 11) (Fr 35) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) σ z35
    (by rw [h.v5]; omega) (by rw [h.v5, h.z 11 (by decide)]; omega)
  rw [h.v5, h.z 11 (by decide), Nat.zero_add] at s1
  set σ1 := σ.setv (Fr 11) p with hσ1
  have s2 := addTo_spec cap (Fr 3) (Fr 12) (Fr 35) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) σ1
    (by simp [σ1, Function.update_apply, z35]) (by simp [σ1, Function.update_apply, h.v3]; omega)
    (by simp [σ1, Function.update_apply, h.v3, h.z 12 (by decide)]; omega)
  have f1 : σ1.val (Fr 12) = 0 := by simp [σ1, Function.update_apply, h.z 12 (by decide)]
  have f2 : σ1.val (Fr 3) = M := by simp [σ1, Function.update_apply, h.v3]
  rw [f1, f2, Nat.zero_add] at s2
  set σ2 := σ1.setv (Fr 12) M with hσ2
  have s3 := addTo_spec cap (Fr 4) (Fr 13) (Fr 35) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) σ2
    (by simp [σ2, σ1, Function.update_apply, z35]) (by simp [σ2, σ1, Function.update_apply, h.v4]; omega)
    (by simp [σ2, σ1, Function.update_apply, h.v4, h.z 13 (by decide)]; omega)
  have g1 : σ2.val (Fr 13) = 0 := by simp [σ2, σ1, Function.update_apply, h.z 13 (by decide)]
  have g2 : σ2.val (Fr 4) = τ := by simp [σ2, σ1, Function.update_apply, h.v4]
  rw [g1, g2, Nat.zero_add] at s3
  set σ3 := σ2.setv (Fr 13) τ with hσ3
  have hOPr : ∀ i, (sh11.trans Fr) i ≠ OP := fun i => hOP _
  have v3 : ∀ j : Fin 48, 14 ≤ j.val → σ3.val (Fr j) = σ.val (Fr j) := fun j hj => by
    have a : j ≠ 11 := by rintro rfl; simp at hj
    have b : j ≠ 12 := by rintro rfl; simp at hj
    have c : j ≠ 13 := by rintro rfl; simp at hj
    simp [σ3, σ2, σ1, Function.update_of_ne (fne Fr a), Function.update_of_ne (fne Fr b), Function.update_of_ne (fne Fr c)]
  have e0 : (sh11.trans Fr) 0 = Fr 11 := rfl
  have e1 : (sh11.trans Fr) 1 = Fr 12 := rfl
  have e2 : (sh11.trans Fr) 2 = Fr 13 := rfl
  have e4 : (sh11.trans Fr) 4 = Fr 15 := rfl
  have hOP3 : σ3.val OP = σ.val OP := by
    simp [σ3, σ2, σ1, Function.update_apply, Ne.symm (hOP 11), Ne.symm (hOP 12), Ne.symm (hOP 13)]
  have hcl := consWord_len p M τ (by omega)
  have hmono : τ * (2 * ((M + 1) * (4 * p + 4))) ≤ τ * (2 * ((M + 1) * (4 * p + 4)) + 5 * p + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have s4 := consW_spec cap O OP (sh11.trans Fr) hOPr σ3 p M τ (by rw [e0]; simp [σ3, σ2, σ1, Function.update_apply])
    hp2 (by rw [e1]; simp [σ3, σ2, σ1, Function.update_apply]) (by rw [e2]; simp [σ3])
    (by rw [e4, v3 _ (by decide)]; exact h.z _ (by decide))
    (fun i hi => by
      have hi2 : 3 ≤ i.val ∧ i.val ≤ 18 := by
        rcases hi with h' | h' | h' | h'
        · rw [h']; decide
        · rw [h']; decide
        · rw [h']; decide
        · omega
      have hv : (sh11 i).val = 11 + i.val := rfl
      show σ3.val (Fr (sh11 i)) = 0
      rw [v3 _ (by rw [hv]; omega)]
      exact h.z _ (by rw [hv]; omega))
    (by simp [σ3, σ2, σ1, h.ho]) hM hτ hp (by rw [hOP3]; omega)
  rw [e2] at s4
  set σ4 := (appendO σ3 O OP (consWord p M τ)).setv (Fr 13) 0 with hσ4
  have v4 : σ4.val (Fr 11) = p := by simp [σ4, σ3, σ2, σ1, Function.update_apply, hOP 11]
  have s5 := wclear_spec cap (Fr 11) (σ4.val (Fr 11)) σ4 rfl (by rw [v4]; exact hp)
  set σ5 := σ4.setv (Fr 11) 0 with hσ5
  have v5 : σ5.val (Fr 12) = M := by simp [σ5, σ4, σ3, σ2, σ1, Function.update_apply, hOP 12]
  have s6 := wclear_spec cap (Fr 12) (σ5.val (Fr 12)) σ5 rfl (by rw [v5]; omega)
  set σ6 := σ5.setv (Fr 12) 0 with hσ6
  have e6 : σ6 = appendO σ O OP (consWord p M τ) := by
    apply WState.eq
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
    · funext r
      simp only [σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, appendO_val, Function.update_apply]
      by_cases a11 : r = Fr 11
      · subst a11; simp [hOP 11, Ne.symm (hOP 11), h.z 11 (by decide)]
      · by_cases a12 : r = Fr 12
        · subst a12; simp [hOP 12, Ne.symm (hOP 12), h.z 12 (by decide)]
        · by_cases a13 : r = Fr 13
          · subst a13; simp [hOP 13, Ne.symm (hOP 13), h.z 13 (by decide)]
          · simp [a11, a12, a13, Ne.symm (hOP 11), Ne.symm (hOP 12), Ne.symm (hOP 13)]
    · simp [σ6, σ5, σ4, σ3, σ2, σ1]
  rw [e6] at s6
  have s7 := emitW_spec cap O OP [true, false] (appendO σ O OP (consWord p M τ)) (ao_ho O OP σ _ h.ho)
    (by rw [ao_val_op]; simp only [List.length_cons, List.length_nil]; omega)
  rw [appendO_append, ← fieldE_cons] at s7
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7)))))) ?_
  rw [v4, v5]
  simp only [List.length_cons, List.length_nil]
  omega

/-- **The residue field.** -/
theorem segF_spec (hOP : ∀ i, Fr i ≠ OP) {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s)
    (hsp : s < p) (hp : p ≤ cap) (hτ : 2 * τ ≤ cap) (hc : σ.val OP + 2 * τ * (4 * p) + 6 ≤ cap) :
    WExec cap (segF O OP Fr) σ (appendO σ O OP (fieldE (patT p s (2 * τ * p + 1))))
      (2 * τ * (60 * p + 64) + 100 * cap + 300) := by
  have s1 := twoTau_spec cap O Fr h hτ
  set σ1 := σ.setv (Fr 7) (2 * τ) with hσ1
  have s2 := addTo_spec cap (Fr 5) (Fr 10) (Fr 35) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) σ1
    (by simp [σ1, Function.update_apply, h.z 35 (by decide)]) (by simp [σ1, Function.update_apply, h.v5]; omega)
    (by simp [σ1, Function.update_apply, h.v5, h.z 10 (by decide)]; omega)
  have f10 : σ1.val (Fr 10) = 0 := by simp [σ1, Function.update_apply, h.z 10 (by decide)]
  have f5 : σ1.val (Fr 5) = p := by simp [σ1, Function.update_apply, h.v5]
  rw [f10, f5, Nat.zero_add] at s2
  set σ2 := σ1.setv (Fr 10) p with hσ2
  have s3 := subW_spec cap (sQ.trans Fr) σ2
    (by show σ2.val (Fr 36) = 0; simp [σ2, σ1, Function.update_apply, h.z 36 (by decide)])
    (by show σ2.val (Fr 37) = 0; simp [σ2, σ1, Function.update_apply, h.z 37 (by decide)])
    (by show σ2.val (Fr 10) ≤ cap; simp [σ2]; omega)
    (by show σ2.val (Fr 6) ≤ cap; simp [σ2, σ1, Function.update_apply, h.v6]; omega)
  have q0 : (sQ.trans Fr) 0 = Fr 10 := rfl
  have q1 : (sQ.trans Fr) 1 = Fr 6 := rfl
  have e10 : σ2.val (Fr 10) = p := by simp [σ2]
  have e6 : σ2.val (Fr 6) = s := by simp [σ2, σ1, Function.update_apply, h.v6]
  rw [q0, q1, e10, e6, wsetv_setv] at s3
  have s4 := WExec.dec (cap := cap) (Fr 10) (σ1.setv (Fr 10) (p - s)) (by simp; omega)
  rw [wsetv_setv] at s4
  have e10' : (σ1.setv (Fr 10) (p - s)).val (Fr 10) - 1 = p - 1 - s := by simp; omega
  rw [e10'] at s4
  set σ4 := σ1.setv (Fr 10) (p - 1 - s) with hσ4
  have s5 := pFieldW_spec cap O OP (Fr 7) (Fr 6) (Fr 10) (Fr 8) (Fr 9) (hOP 7) (hOP 6) (hOP 10) (hOP 8) (hOP 9)
    (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide))
    (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide)) σ4 p s (2 * τ) hsp
    (by simp [σ4, σ1, Function.update_apply]) (by simp [σ4, σ1, Function.update_apply, h.v6]) (by simp [σ4])
    (by simp [σ4, σ1, Function.update_apply, h.z 8 (by decide)]) (by simp [σ4, σ1, Function.update_apply, h.z 9 (by decide)])
    (by simp [σ4, σ1, h.ho]) hp hτ (by simp [σ4, σ1, Function.update_apply, (hOP 7).symm, (hOP 10).symm]; omega)
  set σ5 := (appendO σ4 O OP (fieldE (patT p s (2 * τ * p + 1)))).setv (Fr 7) 0 with hσ5
  have v5 : σ5.val (Fr 10) = p - 1 - s := by simp [σ5, σ4, Function.update_apply, hOP 10]
  have s6 := wclear_spec cap (Fr 10) (σ5.val (Fr 10)) σ5 rfl (by rw [v5]; omega)
  have e6' : σ5.setv (Fr 10) 0 = appendO σ O OP (fieldE (patT p s (2 * τ * p + 1))) := by
    apply WState.eq
    · simp [σ5, σ4, σ1]
    · simp [σ5, σ4, σ1]
    · funext r
      simp only [σ5, σ4, σ1, WState.setv_val, appendO_val, Function.update_apply]
      by_cases a10 : r = Fr 10
      · subst a10; simp [hOP 10, Ne.symm (hOP 10), h.z 10 (by decide)]
      · by_cases a7 : r = Fr 7
        · subst a7; simp [hOP 7, Ne.symm (hOP 7), h.z 7 (by decide)]
        · simp [a10, a7, Ne.symm (hOP 10), Ne.symm (hOP 7)]
    · simp [σ5, σ4, σ1]
  rw [e6'] at s6
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) ?_
  rw [v5]
  omega

/-- **The flag fields and the loop capacity.** -/
theorem segG_spec (hOP : ∀ i, Fr i ≠ OP) {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s)
    (hcp : cp ≤ cap) (hc : σ.val OP + 4 * cp + 10 ≤ cap) :
    WExec cap (segG O OP Fr) σ (appendO σ O OP (fieldE [true] ++ (fieldE [] ++ fieldE (List.replicate cp false))))
      (60 * cp + 120) := by
  have s1 := emitW_spec cap O OP (m2 true ++ [true, false]) σ h.ho (by simp; omega)
  have h1 := h.ao O OP Fr hOP (m2 true ++ [true, false])
  have s2 := emitW_spec cap O OP [true, false] (appendO σ O OP (m2 true ++ [true, false])) h1.ho
    (by rw [ao_val_op]; simp; omega)
  rw [appendO_append] at s2
  have h2 := h.ao O OP Fr hOP (m2 true ++ [true, false] ++ [true, false])
  have s3 := repFieldW_spec cap O OP (Fr 2) (Fr 8) (Fr 9) (fne Fr (by decide)) (fne Fr (by decide)) (fne Fr (by decide))
    (hOP 8) false (appendO σ O OP (m2 true ++ [true, false] ++ [true, false])) (h2.z 8 (by decide)) (h2.z 9 (by decide))
    h2.ho (by rw [h2.v2]; exact hcp) (by rw [ao_val_op, h2.v2]; simp; omega)
  rw [h2.v2, appendO_append] at s3
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by simp; omega)
  simp [fieldE, List.append_assoc]

theorem len_rep (n : ℕ) (b : Bool) : (fieldE (List.replicate n b)).length = 4 * n + 2 := by
  rw [fieldE_rep]; simp [reps_len]; ring

theorem len_enc (M k : ℕ) : (fieldE (frame (encT M (List.replicate k 0)))).length = k * (8 * M + 8) + 6 := by
  have hb : ((m2 true ++ m2 true) ++ reps M (m2 true ++ m2 false)).length = 8 * M + 8 := by simp [reps_len]; omega
  rw [fieldE_enc, List.length_append, reps_len, hb]; simp

theorem len_zW (M k : ℕ) (hk : 1 ≤ k) : (fieldE (zW M (k * (M + 1)))).length = k * (8 * M + 8) + 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hb1 : ((m2 true ++ m2 true) ++ reps M (m2 false ++ m2 false)).length = 8 * M + 8 := by simp [reps_len]; omega
  have hb2 : ((m2 false ++ m2 true) ++ reps M (m2 false ++ m2 false)).length = 8 * M + 8 := by simp [reps_len]; omega
  rw [fieldE_zW M (j + 1) hk, Nat.add_sub_cancel, List.length_append, hb1, List.length_append, reps_len, hb2]
  simp only [List.length_cons, List.length_nil]
  ring

theorem len_patT (p s k : ℕ) (hs : s < p) : (fieldE (patT p s (k * p + 1))).length = k * (4 * p) + 6 := by
  have hb : (reps s (m2 false) ++ (m2 true ++ reps (p - 1 - s) (m2 false))).length = 4 * p := by simp [reps_len]; omega
  rw [fieldE_patT p s k hs, List.length_append, reps_len, hb]; simp

theorem len_cons (M p τ : ℕ) (hp : 1 ≤ p) :
    (fieldE (fieldsU (consFrom M p 2 0 τ))).length ≤ τ * (2 * ((M + 1) * (4 * p + 4))) + 2 := by
  rw [fieldE_cons, List.length_append]
  have := consWord_len p M τ hp
  simp only [List.length_cons, List.length_nil]
  omega

/-- The setup fields' length budget. -/
def fieldsLen (R Lg cp M τ p : ℕ) : ℕ :=
  4 * R + 2 + (4 * Lg + 2) + (2 * τ * (8 * M + 8) + 6) + (2 * τ * (8 * M + 8) + 2) +
    (τ * (2 * ((M + 1) * (4 * p + 4)) + 5 * p + 2) + 2) + (2 * τ * (4 * p) + 6) + (4 * cp + 10)

/-- The setup fields' cost. -/
def fieldsCost (cap R Lg cp M τ p : ℕ) : ℕ :=
  60 * R + 40 + (60 * Lg + 40) + (2 * τ * (100 * M + 200) + 36 * τ + 108) + (2 * τ * (100 * M + 200) + 36 * τ + 110) +
    (τ * (digitCost cap M + 4) + 200 * cap + 200) + (2 * τ * (60 * p + 64) + 100 * cap + 300) + (60 * cp + 120) + 6

/-- **The setup fields, written**: on a ready state `fieldsP` appends `fieldsWordB R Lg M τ p s cp` and restores every
register. -/
theorem fieldsP_spec (hOP : ∀ i, Fr i ≠ OP) {σ : WState ns nr} {R Lg cp M τ p s : ℕ} (h : Ready O Fr σ R Lg cp M τ p s)
    (hR : R ≤ cap) (hLg : Lg ≤ cap) (hcp : cp ≤ cap) (hM : M + 1 ≤ cap) (hτ1 : 1 ≤ τ) (hτ : 2 * τ ≤ cap)
    (hp2 : 2 ≤ p) (hsp : s < p) (hp : p ≤ cap) (hc : σ.val OP + fieldsLen R Lg cp M τ p ≤ cap) :
    WExec cap (fieldsP O OP Fr) σ (appendO σ O OP (fieldsWordB R Lg M τ p s cp)) (fieldsCost cap R Lg cp M τ p) := by
  unfold fieldsLen at hc
  have s1 := repFieldW_spec cap O OP (Fr 0) (Fr 8) (Fr 9) (fne Fr (by decide)) (fne Fr (by decide))
    (fne Fr (by decide)) (hOP 8) true σ (h.z 8 (by decide)) (h.z 9 (by decide)) h.ho (by rw [h.v0]; exact hR)
    (by rw [h.v0]; omega)
  rw [h.v0] at s1
  obtain ⟨w1, hw1⟩ : ∃ w, w = fieldE (List.replicate R true) := ⟨_, rfl⟩
  rw [← hw1] at s1
  have l1 : w1.length = 4 * R + 2 := by rw [hw1, len_rep]
  have h1 := h.ao O OP Fr hOP w1
  have s2 := repFieldW_spec cap O OP (Fr 1) (Fr 8) (Fr 9) (fne Fr (by decide)) (fne Fr (by decide))
    (fne Fr (by decide)) (hOP 8) false (appendO σ O OP w1) (h1.z 8 (by decide)) (h1.z 9 (by decide)) h1.ho
    (by rw [h1.v1]; exact hLg) (by rw [ao_val_op, h1.v1, l1]; omega)
  rw [h1.v1, appendO_append] at s2
  obtain ⟨w2, hw2⟩ : ∃ w, w = w1 ++ fieldE (List.replicate Lg false) := ⟨_, rfl⟩
  rw [← hw2] at s2
  have l2 : w2.length = 4 * R + 2 + (4 * Lg + 2) := by rw [hw2, List.length_append, l1, len_rep]
  have h2 := h.ao O OP Fr hOP w2
  have s3 := segC_spec cap O OP Fr hOP h2 (by omega) hτ (by rw [ao_val_op, l2]; omega)
  rw [appendO_append] at s3
  obtain ⟨w3, hw3⟩ : ∃ w, w = w2 ++ fieldE (frame (encT M (List.replicate (2 * τ) 0))) := ⟨_, rfl⟩
  rw [← hw3] at s3
  have l3 : w3.length = 4 * R + 2 + (4 * Lg + 2) + (2 * τ * (8 * M + 8) + 6) := by
    rw [hw3, List.length_append, l2, len_enc]
  have h3 := h.ao O OP Fr hOP w3
  have s4 := segD_spec cap O OP Fr hOP h3 hτ1 (by omega) hτ (by rw [ao_val_op, l3]; omega)
  rw [appendO_append] at s4
  obtain ⟨w4, hw4⟩ : ∃ w, w = w3 ++ fieldE (zW M (2 * τ * (M + 1))) := ⟨_, rfl⟩
  rw [← hw4] at s4
  have l4 : w4.length = w3.length + (2 * τ * (8 * M + 8) + 2) := by
    rw [hw4, List.length_append, len_zW M (2 * τ) (by omega)]
  have h4 := h.ao O OP Fr hOP w4
  have s5 := segE_spec cap O OP Fr hOP h4 hp2 hM (by omega) hp (by rw [ao_val_op, l4, l3]; omega)
  rw [appendO_append] at s5
  obtain ⟨w5, hw5⟩ : ∃ w, w = w4 ++ fieldE (fieldsU (consFrom M p 2 0 τ)) := ⟨_, rfl⟩
  rw [← hw5] at s5
  have l5 : w5.length ≤ w4.length + (τ * (2 * ((M + 1) * (4 * p + 4))) + 2) := by
    rw [hw5, List.length_append]; have := len_cons M p τ (by omega); omega
  have hmono : τ * (2 * ((M + 1) * (4 * p + 4))) ≤ τ * (2 * ((M + 1) * (4 * p + 4)) + 5 * p + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have h5 := h.ao O OP Fr hOP w5
  have s6 := segF_spec cap O OP Fr hOP h5 hsp hp hτ (by rw [ao_val_op]; omega)
  rw [appendO_append] at s6
  obtain ⟨w6, hw6⟩ : ∃ w, w = w5 ++ fieldE (patT p s (2 * τ * p + 1)) := ⟨_, rfl⟩
  rw [← hw6] at s6
  have l6 : w6.length = w5.length + (2 * τ * (4 * p) + 6) := by
    rw [hw6, List.length_append, len_patT p s (2 * τ) hsp]
  have h6 := h.ao O OP Fr hOP w6
  have s7 := segG_spec cap O OP Fr hOP h6 hcp (by rw [ao_val_op]; omega)
  rw [appendO_append] at s7
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))))
    ?_ ?_
  · rw [hw6, hw5, hw4, hw3, hw2, hw1, fieldsWordB_eq]; simp only [List.append_assoc]
  · unfold fieldsCost; omega

end W

end NearCubicWires.WireExponent3_5.UnionMachine.RadFieldsP
