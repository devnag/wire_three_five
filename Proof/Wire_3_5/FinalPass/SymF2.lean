import Proof.Wire_3_5.FinalPass.SymF1
import Proof.Wire_3_5.Primitive.Writers.Arith
import Proof.Wire_3_5.FinalPass.TabEmit

/-! # SWf (the SYM words writer's flat tables), part 2: a unit's emission

After a unit's table stages (`tabPreP`), the flat table `tw ++ [false]` (`tw = tableW …`) is on stream `6` (head `0`)
and the POP-ready registers are kept: the walk length `t`, `J`, `L` (`Xe Pe 52`, `21`, `4`) and the row offset
`off` (`Xe Pe 3`), where the unit's decode parks its seed test `|FlatSeed| − j`. The emission appends to the output
`out ++ [false]` (head on the marker) the unit's piece of the flat tables word: nothing when the test is `0`, else a
separating `false` when `j > 0` (the counter's first cell) and the raw table `tw`, then the blank marker; then it
advances the unit counter. Word programs:

* `cpRBody`, `cpRLoop`, **`cpRLoop_spec`** (a raw copy of `|tw|` cells, the output's marker overwritten);
* `leadW`, **`leadW_spec`** (the separator, from a stream bit);
* `lenOps`, `lenOps_eval` (PA's straight-line kit: `c = t·((J+1)(2L+1)+1)`, the table's length);
* `emitTP`, **`emitTP_spec`**.

Paper quantity of the main type: one list seed's piece of `tablesJ` (the flat table `flatTable Pl e L` minus its
closing `false`, separated from the previous seed's, P3:1508-1520). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

section Gen
variable {ns nr : ℕ} (cap : ℕ) (T O : Fin (ns + 1)) (c : Fin nr)

theorem take_succ_getD (tw : List Bool) (i : ℕ) (hi : i < tw.length) :
    tw.take (i + 1) = tw.take i ++ [tw.getD i false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]
  rfl

/-- One table cell copied raw; both heads advanced. -/
def cpRBody : WM ns nr := .seq (.dec c) (.seq (.ifs T (.wr O true) (.wr O false)) (.seq (.fwd O) (.fwd T)))

theorem cpRBody_spec (hTO : T ≠ O) (tw Y out Z : List Bool) (i m : ℕ) (σ : WState ns nr) (hc : σ.val c = m + 1)
    (hcc : m + 1 ≤ cap) (hT : σ.st T = tw ++ Y) (hTh : σ.sh T = i) (hi : i < tw.length)
    (hO : σ.st O = out ++ tw.take i ++ Z) (hZ : Z.length ≤ 1) (hOh : σ.sh O = out.length + i) :
    ∃ σ' : WState ns nr, WExec cap (cpRBody T O c) σ σ' 8 ∧ σ'.st O = out ++ tw.take (i + 1) ∧
      σ'.sh O = out.length + (i + 1) ∧ σ'.sh T = i + 1 ∧ σ'.val c = m ∧
      (∀ s, s ≠ O → σ'.st s = σ.st s) ∧ (∀ s, s ≠ O → s ≠ T → σ'.sh s = σ.sh s) ∧
      (∀ r, r ≠ c → σ'.val r = σ.val r) ∧ σ'.cell = σ.cell := by
  have hA : (out ++ tw.take i).length = out.length + i := by
    simp only [List.length_append, List.length_take]; omega
  have e1 := WExec.dec (cap := cap) c σ (by omega)
  rw [hc, Nat.add_sub_cancel] at e1
  have hb : wbit (σ.setv c m) T = tw.getD i false := by
    unfold wbit
    simp only [WState.setv_st, WState.setv_sh]
    rw [hT, hTh]
    unfold readTapeBit
    rw [List.getD_append _ _ _ _ hi]
  have w2 : ∀ v : Bool, writeTapeBit ((σ.setv c m).st O) ((σ.setv c m).sh O) v = out ++ tw.take i ++ [v] := by
    intro v
    simp only [WState.setv_st, WState.setv_sh]
    rw [hO, hOh, ← hA, TabW.wz _ Z hZ]
  have e2 : WExec cap (.ifs T (.wr O true) (.wr O false)) (σ.setv c m)
      ((σ.setv c m).sets O (out ++ tw.take i ++ [tw.getD i false])) 2 := by
    cases hg : tw.getD i false
    · have := WExec.wr (cap := cap) O false (σ.setv c m)
      rw [w2] at this
      exact WExec.ifsF (by rw [hb, hg]) this
    · have := WExec.wr (cap := cap) O true (σ.setv c m)
      rw [w2] at this
      exact WExec.ifsT (by rw [hb, hg]) this
  have e3 := WExec.fwd (cap := cap) O ((σ.setv c m).sets O (out ++ tw.take i ++ [tw.getD i false]))
  have e4 := WExec.fwd (cap := cap) T (((σ.setv c m).sets O (out ++ tw.take i ++ [tw.getD i false])).seth O
    (((σ.setv c m).sets O (out ++ tw.take i ++ [tw.getD i false])).sh O + 1))
  refine ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st, WState.sets_st, Function.update_self]
    rw [take_succ_getD tw i hi, List.append_assoc]
  · simp [Function.update_apply, hTO, hTO.symm, hOh]
    omega
  · simp [Function.update_apply, hTO, hTO.symm, hTh]
  · simp
  · intro s hs
    simp [Function.update_apply, hs]
  · intro s hs hsT
    simp [Function.update_apply, hs, hsT]
  · intro r hr
    simp [Function.update_apply, hr]
  · rfl

/-- The raw copy, while `c` counts down. -/
def cpRLoop : WM ns nr := .whr c (cpRBody T O c)

theorem cpRLoop_spec (hTO : T ≠ O) (tw Y out : List Bool) :
    ∀ (m i : ℕ) (Z : List Bool) (σ : WState ns nr), i + m = tw.length → σ.val c = m → m ≤ cap →
      σ.st T = tw ++ Y → σ.sh T = i → σ.st O = out ++ tw.take i ++ Z → Z.length ≤ 1 →
      σ.sh O = out.length + i →
      ∃ (σ' : WState ns nr) (Zf : List Bool), WExec cap (cpRLoop T O c) σ σ' (m * 10 + 1) ∧
        σ'.st O = out ++ tw ++ Zf ∧ Zf.length ≤ 1 ∧ σ'.sh O = out.length + tw.length ∧
        (∀ s, s ≠ O → σ'.st s = σ.st s) ∧ (∀ s, s ≠ O → s ≠ T → σ'.sh s = σ.sh s) ∧
        (∀ r, r ≠ c → σ'.val r = σ.val r) ∧ σ'.cell = σ.cell
  | 0, i, Z, σ, hl, hc, _, _, _, hO, hZ, hOh => by
    have hi : i = tw.length := by omega
    refine ⟨σ, Z, WExec.cast cap (WExec.whrF hc) rfl (by omega), ?_, hZ, by rw [hOh, hi], fun _ _ => rfl,
      fun _ _ _ => rfl, fun _ _ => rfl, rfl⟩
    rw [hO, hi, List.take_of_length_le le_rfl]
  | m + 1, i, Z, σ, hl, hc, hcc, hT, hTh, hO, hZ, hOh => by
    obtain ⟨σ1, e1, o1, oh1, th1, c1, s1, h1, v1, l1⟩ :=
      cpRBody_spec cap T O c hTO tw Y out Z i m σ hc hcc hT hTh (by omega) hO hZ hOh
    obtain ⟨σ2, Zf, e2, o2, z2, oh2, s2, h2, v2, l2⟩ := cpRLoop_spec hTO tw Y out m (i + 1) [] σ1 (by omega) c1
      (by omega) (by rw [s1 T hTO]; exact hT) th1 (by rw [o1, List.append_nil]) (by simp) oh1
    refine ⟨σ2, Zf, WExec.cast cap (WExec.whrT (by rw [hc]; omega) e1 e2) rfl (by omega), o2, z2, oh2,
      fun s hs => (s2 s hs).trans (s1 s hs), fun s hs hsT => (h2 s hs hsT).trans (h1 s hs hsT),
      fun r hr => (v2 r hr).trans (v1 r hr), l2.trans l1⟩

variable (K : Fin (ns + 1))

/-- The separator: a `false` over the output's marker, head past it, when `K`'s cell reads `true`. -/
def leadW : WM ns nr := .ifs K (.seq (.wr O false) (.fwd O)) .skip

theorem leadW_spec (out : List Bool) (σ : WState ns nr) (hO : σ.st O = out ++ [false])
    (hOh : σ.sh O = out.length) :
    ∃ (σ' : WState ns nr) (Z : List Bool), WExec cap (leadW O K) σ σ' 4 ∧
      σ'.st O = out ++ (if wbit σ K then [false] else []) ++ Z ∧ Z.length ≤ 1 ∧
      σ'.sh O = (out ++ (if wbit σ K then [false] else [])).length ∧
      (∀ s, s ≠ O → σ'.st s = σ.st s) ∧ (∀ s, s ≠ O → σ'.sh s = σ.sh s) ∧ (∀ r, σ'.val r = σ.val r) ∧
      σ'.cell = σ.cell := by
  cases hk : wbit σ K
  · refine ⟨σ, [false], WExec.mono (WExec.ifsF hk (WExec.skip σ)) (by omega), ?_, by simp, ?_, fun _ _ => rfl,
      fun _ _ => rfl, fun _ => rfl, rfl⟩
    · simp [hO]
    · simp [hOh]
  · have e1 := WExec.wr (cap := cap) O false σ
    have w1 : writeTapeBit (σ.st O) (σ.sh O) false = out ++ [false] := by
      rw [hO, hOh, TabW.wz _ [false] (by simp)]
    rw [w1] at e1
    have e2 := WExec.fwd (cap := cap) O (σ.sets O (out ++ [false]))
    refine ⟨_, [], WExec.ifsT hk (WExec.seq e1 e2), ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp [hOh]
    · intro s hs
      simp [Function.update_apply, hs]
    · intro s hs
      simp [Function.update_apply, hs]
    · intro r
      rfl
    · rfl

end Gen

section Emit
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.Arith
variable (cap x : ℕ)

/-- The seed test (`Xe Pe 3`, the POP row's offset). -/
def eOff : Fin LNR := ⟨22, by decide⟩
/-- The walk length (`Xe Pe 52`). -/
def eW : Fin LNR := ⟨71, by decide⟩
/-- `J` (`Xe Pe 21`). -/
def eJ : Fin LNR := ⟨40, by decide⟩
/-- `L` (`Xe Pe 4`). -/
def eL : Fin LNR := ⟨23, by decide⟩
/-- The length program's registers: the inputs, then `Pe 64 … 67`. -/
def eZ : Fin 7 ↪ Fin LNR :=
  ⟨![⟨71, by decide⟩, ⟨40, by decide⟩, ⟨23, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩,
    ⟨86, by decide⟩], by decide⟩
def eT0 : Fin LNR := ⟨87, by decide⟩
def eT1 : Fin LNR := ⟨88, by decide⟩
/-- The copy counter (`eZ 6`). -/
def eC : Fin LNR := ⟨86, by decide⟩
/-- The unit counter's scratch. -/
def eD : Fin LNR := ⟨89, by decide⟩

/-- `c = t·((J+1)(2L+1)+1)` from `t, J, L`. -/
def lenOps : List (AOp 7) := [.add 1 3, .inc 3 1, .add 2 4, .add 2 4, .inc 4 1, .mul 3 4 5, .inc 5 1, .mul 0 5 6]

theorem lenOps_eval (w J L : ℕ) : evalL (![w, J, L, 0, 0, 0, 0] : Fin 7 → ℕ) lenOps =
    ![w, J, L, J + 1, L + L + 1, (J + 1) * (L + L + 1) + 1, w * ((J + 1) * (L + L + 1) + 1)] := by
  funext i
  fin_cases i <;> simp [evalL, lenOps, AOp.eval, Function.update_apply] <;> ring

theorem lenOps_dist : ∀ o ∈ lenOps, o.dist := by
  intro o ho
  simp only [lenOps, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with h | h | h | h | h | h | h | h <;> subst h <;> simp [AOp.dist] <;> decide

theorem costL_lenOps : costL cap lenOps = 5 * (30 * (cap + 1) * (cap + 1) + 1) + 15 := by
  simp [costL, lenOps, AOp.cost]
  ring

/-- **A unit's emission.** -/
def emitTP : WM (LNS x) LNR :=
  .seq (.ifr eOff (.seq (leadW (sk x 1) (sk x 2)) (.seq (progL eZ eT0 eT1 lenOps)
    (.seq (cpRLoop (sk x 6) (sk x 1) eC) (.wr (sk x 1) false)))) .skip) (TabW.incE (sk x 2) eD)

/-- The emission's cost bound. -/
def emitPBound (j lt : ℕ) : ℕ := costL cap lenOps + 10 * lt + 12 * j + 40

theorem rep_bit (j : ℕ) : readTapeBit (List.replicate j true) 0 = decide (j ≠ 0) := by
  cases j <;> rfl

theorem emitTP_spec (σ : WState (LNS x) LNR) (out tw Y : List Bool) (j f w J L : ℕ)
    (hO : σ.st (sk x 1) = out ++ [false]) (hOh : σ.sh (sk x 1) = out.length)
    (hK : σ.st (sk x 2) = List.replicate j true) (hKh : σ.sh (sk x 2) = 0)
    (hT : σ.st (sk x 6) = tw ++ Y) (hTh : σ.sh (sk x 6) = 0)
    (hf : σ.val eOff = f) (hw : σ.val eW = w) (hJ : σ.val eJ = J) (hL : σ.val eL = L)
    (hz : ∀ q : Fin LNR, 83 ≤ q.val → q.val ≤ 89 → σ.val q = 0)
    (htw : tw.length = w * ((J + 1) * (2 * L + 1) + 1)) (hw1 : 1 ≤ w) (hcap : tw.length ≤ cap)
    (hj : j + 1 ≤ cap) :
    ∃ (σ' : WState (LNS x) LNR) (m : ℕ), WExec cap (emitTP x) σ σ' m ∧ m ≤ emitPBound cap j tw.length ∧
      σ'.st (sk x 1) = out ++ (if f = 0 then [] else (if j = 0 then [] else [false]) ++ tw) ++ [false] ∧
      σ'.sh (sk x 1) = (out ++ (if f = 0 then [] else (if j = 0 then [] else [false]) ++ tw)).length ∧
      σ'.st (sk x 2) = List.replicate (j + 1) true ∧
      (∀ s, s ≠ sk x 1 → s ≠ sk x 2 → σ'.st s = σ.st s) := by
  have n12 : sk x 1 ≠ sk x 2 := fun e => absurd (sk_inj x e) (by decide)
  have n16 : sk x 6 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n26 : sk x 2 ≠ sk x 6 := fun e => absurd (sk_inj x e) (by decide)
  -- the flagged part
  obtain ⟨σ1, m1, e1, b1, o1, oh1, s1, h1, v1⟩ : ∃ (σ1 : WState (LNS x) LNR) (m1 : ℕ),
      WExec cap (.ifr eOff (.seq (leadW (sk x 1) (sk x 2)) (.seq (progL eZ eT0 eT1 lenOps)
        (.seq (cpRLoop (sk x 6) (sk x 1) eC) (.wr (sk x 1) false)))) .skip) σ σ1 m1 ∧
      m1 ≤ costL cap lenOps + 10 * tw.length + 20 ∧
      σ1.st (sk x 1) = out ++ (if f = 0 then [] else (if j = 0 then [] else [false]) ++ tw) ++ [false] ∧
      σ1.sh (sk x 1) = (out ++ (if f = 0 then [] else (if j = 0 then [] else [false]) ++ tw)).length ∧
      (∀ s, s ≠ sk x 1 → σ1.st s = σ.st s) ∧ (∀ s, s ≠ sk x 1 → s ≠ sk x 6 → σ1.sh s = σ.sh s) ∧
      σ1.val eD = 0 := by
    by_cases hf0 : f = 0
    · refine ⟨σ, _, WExec.ifrF (by rw [hf, hf0]) (WExec.skip σ), by omega, ?_, ?_, fun _ _ => rfl,
        fun _ _ _ => rfl, hz eD (by decide) (by decide)⟩
      · rw [hO, if_pos hf0]; simp
      · rw [hOh, if_pos hf0]; simp
    · -- the separator
      obtain ⟨σA, ZA, eA, oA, zA, ohA, sA, hA, vA, lA⟩ := leadW_spec cap (sk x 1) (sk x 2) out σ hO hOh
      have hbit : wbit σ (sk x 2) = decide (j ≠ 0) := by
        unfold wbit
        rw [hK, hKh, rep_bit]
      rw [hbit] at oA ohA
      have hlead : (if decide (j ≠ 0) = true then [false] else []) = (if j = 0 then [] else [false]) := by
        by_cases hj0 : j = 0 <;> simp [hj0]
      rw [hlead] at oA ohA
      -- the length
      have hv : ∀ i, σA.val (eZ i) = (![w, J, L, 0, 0, 0, 0] : Fin 7 → ℕ) i := by
        intro i
        rw [vA]
        fin_cases i
        · exact hw
        · exact hJ
        · exact hL
        · exact hz _ (by decide) (by decide)
        · exact hz _ (by decide) (by decide)
        · exact hz _ (by decide) (by decide)
        · exact hz _ (by decide) (by decide)
      have hTZ : ∀ i, eZ i ≠ eT0 ∧ eZ i ≠ eT1 := by decide
      have hle : ∀ i, evalL (![w, J, L, 0, 0, 0, 0] : Fin 7 → ℕ) lenOps i ≤ cap := by
        rw [lenOps_eval]
        have p1 : J + 1 ≤ (J + 1) * (L + L + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have p2 : L + L + 1 ≤ (J + 1) * (L + L + 1) := Nat.le_mul_of_pos_left _ (by omega)
        have p3 : (J + 1) * (L + L + 1) + 1 ≤ w * ((J + 1) * (L + L + 1) + 1) := Nat.le_mul_of_pos_left _ hw1
        have p4 : w ≤ w * ((J + 1) * (L + L + 1) + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have ht : w * ((J + 1) * (L + L + 1) + 1) ≤ cap := by
          rw [show L + L + 1 = 2 * L + 1 by omega, ← htw]; exact hcap
        intro i
        fin_cases i <;> simp <;> omega
      obtain ⟨nP, eP, bP⟩ := progL_spec cap eZ eT0 eT1 hTZ (by decide) lenOps σA _
        (by rw [vA]; exact hz _ (by decide) (by decide)) (by rw [vA]; exact hz _ (by decide) (by decide))
        lenOps_dist hle
      rw [setZ_self σA _ hv] at eP
      set σP := setZ eZ σA (evalL (![w, J, L, 0, 0, 0, 0] : Fin 7 → ℕ) lenOps) with hσP
      have pC : σP.val eC = tw.length := by
        rw [show eC = eZ 6 from rfl, hσP, setZ_val_Z, lenOps_eval, htw]
        show w * ((J + 1) * (L + L + 1) + 1) = w * ((J + 1) * (2 * L + 1) + 1)
        ring
      have pOther : ∀ q : Fin LNR, (∀ i, eZ i ≠ q) → σP.val q = σA.val q := fun q hq =>
        setZ_val_other (Z := eZ) σA _ q hq
      have pst : σP.st = σA.st := rfl
      have psh : σP.sh = σA.sh := rfl
      -- the copy
      obtain ⟨σL, Zf, eL', oL, zL, ohL, sL, hL', vL, lL⟩ := cpRLoop_spec cap (sk x 6) (sk x 1) eC n16 tw Y
        (out ++ (if j = 0 then [] else [false])) tw.length 0 ZA σP (by omega) pC hcap
        (by rw [pst, sA _ n16, hT]) (by rw [psh, hA _ n16, hTh]) (by rw [pst, oA]; simp) zA
        (by rw [psh, ohA]; simp)
      have eW' := WExec.wr (cap := cap) (sk x 1) false σL
      have wL : writeTapeBit (σL.st (sk x 1)) (σL.sh (sk x 1)) false =
          out ++ (if j = 0 then [] else [false]) ++ tw ++ [false] := by
        rw [oL, ohL, show (out ++ (if j = 0 then [] else [false])).length + tw.length =
          (out ++ (if j = 0 then [] else [false]) ++ tw).length by simp only [List.length_append],
          TabW.wz _ Zf zL]
      rw [wL] at eW'
      refine ⟨_, _, WExec.ifrT (by rw [hf]; exact hf0) (WExec.seq eA (WExec.seq eP (WExec.seq eL' eW'))),
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [costL_lenOps] at bP ⊢
        omega
      · simp only [WState.sets_st, Function.update_self]
        rw [if_neg hf0]
        simp
      · simp only [WState.sets_sh]
        rw [ohL, if_neg hf0]
        simp only [List.length_append]
        omega
      · intro s hs
        simp only [WState.sets_st]
        rw [Function.update_of_ne hs, sL s hs, pst, sA s hs]
      · intro s hs hs6
        simp only [WState.sets_sh]
        rw [hL' s hs hs6, psh, hA s hs]
      · simp only [WState.sets_val]
        rw [vL eD (by decide), pOther eD (by decide), vA]
        exact hz eD (by decide) (by decide)
  -- the counter
  obtain ⟨σ2, e2, k2, -, s2, h2, -, -⟩ := TabW.incE_spec cap (sk x 2) eD j hj σ1 (by rw [s1 _ n12.symm, hK])
    (by rw [h1 _ n12.symm n26, hKh]) v1
  refine ⟨σ2, _, WExec.seq e1 e2, ?_, by rw [s2 _ n12, o1], by rw [h2 _ n12, oh1], k2, ?_⟩
  · unfold emitPBound TabW.incCostE
    omega
  · intro s hs1 hs2
    rw [s2 s hs2, s1 s hs1]

end Emit

end NearCubicWires.WireExponent3_5.FinalPass.SymF
