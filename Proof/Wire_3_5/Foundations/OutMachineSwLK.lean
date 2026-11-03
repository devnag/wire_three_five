import Proof.Wire_3_5.Foundations.SwPartsTmpl
import Proof.Wire_3_5.Primitive.Writers.SparseNum
import Proof.Wire_3_5.FinalPass.S5TUtil

/-! # SWl, part 1: one circuit's template on a blank stream, and the bounds

The SYM words writer's templates (slots `28 … 31`, `symWords` word `4·3 + j` = `S3.templJ`, P3:1449-1477,
1508-1520) are E's raw template word `tplWord M S J L` (`tplWord_eq`: `levelWord M J W (blank rows)` of the
base list at `S = ⌈√(64²B)⌉`, `L = |G_j|`). Generic in the bank:

* **`circ`**, **`circ_spec`**: `M`, `L` copied into E's block (`W 25`, `W 26`), `tplW` on the blank stream `O`, the
  stream rewound by the output counter `W 24`, the copies cleared: exit `σ.sets O (tplWord M S J L)` (every register and
  head as at the entry), within `30000·(cap+2)^3` steps;
* `tplWBound_le`, **`tplWord_length_le`** (the word within `M + 2 + (J+1)·(5·(64 + S + 2^J) + 5 + L)`),
  `sqrtCost_le` (`sqrtW` within `200·(X+2)^3`).

Paper quantity of the main type: the stage-5 template word of the base list for circuit `j` (P3:1449-1477,
3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SwL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO)
open NearCubicWires.WireExponent3_5.FinalPass.SymParts.Tmpl (tplW tplW_spec tplWord tplRec tplRec_length tplWBound
  tplBodyBound repsB_eq)

/-- A bound on E's template cost. -/
theorem tplWBound_le (cap J M : ℕ) (hJ : J + 1 ≤ cap) (hM : M ≤ cap) : tplWBound cap J M ≤ 27000 * (cap + 2) ^ 3 := by
  have hB : tplBodyBound cap + 4 ≤ 25000 * (cap + 2) ^ 2 := by
    unfold tplBodyBound PrimAsm.LevelW.phBound PrimAsm.UnaryPow.sq
    nlinarith
  have hP : (J + 1) * (tplBodyBound cap + 4) ≤ (cap + 2) * (25000 * (cap + 2) ^ 2) :=
    Nat.mul_le_mul (by omega) hB
  have e : (cap + 2) * (25000 * (cap + 2) ^ 2) = 25000 * (cap + 2) ^ 3 := by ring
  have h3 : cap + 2 ≤ (cap + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold tplWBound
  omega

/-- The template word's length. -/
theorem tplWord_length_le (M Sv J L : ℕ) :
    (tplWord M Sv J L).length ≤ M + 2 + (J + 1) * (5 * (64 + Sv + 2 ^ J) + 5 + L) := by
  unfold tplWord
  simp only [List.length_append, repsB_eq, List.length_replicate, List.length_singleton, List.length_flatMap]
  have hs := List.sum_le_card_nsmul ((FinalPass.ListEval.levels J).map fun j => (tplRec Sv J j L).length)
    (5 * (64 + Sv + 2 ^ J) + 5 + L) (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have hjJ : j ≤ J := by
        unfold FinalPass.ListEval.levels at hj
        rw [List.mem_reverse, List.mem_range] at hj
        omega
      rw [tplRec_length]
      have hw := PrimAsm.LevelW.winAt_le Sv J j
      have hp := PrimAsm.LevelW.pow_clog_le (2 * PrimAsm.LevelW.winAt Sv J j + 1) (by omega)
      have hq : 2 ^ (j / 3) ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
  rw [smul_eq_mul, List.length_map] at hs
  have hl : (FinalPass.ListEval.levels J).length = J + 1 := by simp [FinalPass.ListEval.levels]
  rw [hl] at hs
  omega

/-- A bound on `sqrtW` cost at `X`. -/
theorem sqrtCost_le (X : ℕ) :
    18 * X + 3 + 1 + (3 + 1 + ((X + 1) * (PrimAsm.LevelW.stepCost X (CanonicalFourfoldRowProgram.natCeilSqrt X) + 4) +
      1)) ≤ 200 * (X + 2) ^ 3 := by
  have hs := PrimAsm.LevelW.natCeilSqrt_le X
  generalize CanonicalFourfoldRowProgram.natCeilSqrt X = s at hs ⊢
  have h1 : s * (18 * s + 8) ≤ (X + 2) * (18 * (X + 2) + 8) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : s * s ≤ (X + 2) * (X + 2) := Nat.mul_le_mul (by omega) (by omega)
  have hst : PrimAsm.LevelW.stepCost X s + 4 ≤ 190 * (X + 2) ^ 2 := by
    unfold PrimAsm.LevelW.stepCost
    nlinarith
  have hm : (X + 1) * (PrimAsm.LevelW.stepCost X s + 4) ≤ (X + 2) * (190 * (X + 2) ^ 2) :=
    Nat.mul_le_mul (by omega) hst
  have e : (X + 2) * (190 * (X + 2) ^ 2) = 190 * (X + 2) ^ 3 := by ring
  have h3 : 4 * (X + 2) ≤ (X + 2) ^ 3 := by
    have h4 : 4 ≤ (X + 2) ^ 2 := by nlinarith
    calc 4 * (X + 2) ≤ (X + 2) ^ 2 * (X + 2) := Nat.mul_le_mul_right _ h4
      _ = (X + 2) ^ 3 := by ring
  omega

section Kit
variable {ns nr : ℕ} (cap : ℕ)

/-- **One circuit's template**: `M`, `L` into `W 25`, `W 26`; E's `tplW` on `O`; `O` rewound by `W 24`; the copies
cleared. -/
def circ (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (Mr Lr t : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR Mr (W 25) t) (.seq (FinalPass.Hash4.wcopyR Lr (W 26) t) (.seq (tplW O W)
    (.seq (WM.rewind O (W 24)) (.seq (WM.clear (W 25)) (WM.clear (W 26))))))

theorem circ_spec (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (Mr Lr t : Fin nr) (hMW : ∀ i, W i ≠ Mr)
    (hLW : ∀ i, W i ≠ Lr) (htW : ∀ i, W i ≠ t) (hMt : Mr ≠ t) (hLt : Lr ≠ t) (σ : WState ns nr)
    (M Sv J L : ℕ) (h0 : σ.val (W 0) = Sv) (h1 : σ.val (W 1) = J) (hz : ∀ i : Fin 30, 2 ≤ i.val → σ.val (W i) = 0)
    (hM : σ.val Mr = M) (hL : σ.val Lr = L) (ht : σ.val t = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0)
    (hcap : PrimAsm.LevelW.lvCap Sv J J ≤ cap) (hw : (tplWord M Sv J L).length ≤ cap) (hJ : J + 1 ≤ cap)
    (hLc : L ≤ cap) (hMc : M ≤ cap) :
    ∃ n, n ≤ 30000 * (cap + 2) ^ 3 ∧ WExec cap (circ O W Mr Lr t) σ (σ.sets O (tplWord M Sv J L)) n := by
  have hne : ∀ {i k : Fin 30}, i ≠ k → W i ≠ W k := fun h => W.injective.ne h
  have z24 := hz 24 (by decide)
  have z25 := hz 25 (by decide)
  have z26 := hz 26 (by decide)
  have e1 := PrimAsm.SparseNum.copy1 cap Mr (W 25) t (hMW 25).symm hMt (htW 25) M σ hM z25 ht hMc
  have e2 := PrimAsm.SparseNum.copy1 cap Lr (W 26) t (hLW 26).symm hLt (htW 26) L (σ.setv (W 25) M)
    (by simp [Function.update_apply, Ne.symm (hLW 25), hL])
    (by simp [Function.update_apply, hne (by decide : (26 : Fin 30) ≠ 25), z26])
    (by simp [Function.update_apply, Ne.symm (htW 25), ht]) hLc
  set σ2 := (σ.setv (W 25) M).setv (W 26) L with hσ2
  obtain ⟨n3, e3, hn3⟩ := tplW_spec cap O W σ2 M Sv J L
    (by simp [hσ2, Function.update_apply, hne (by decide : (0 : Fin 30) ≠ 26), hne (by decide : (0 : Fin 30) ≠ 25), h0])
    (by simp [hσ2, Function.update_apply, hne (by decide : (1 : Fin 30) ≠ 26), hne (by decide : (1 : Fin 30) ≠ 25), h1])
    (by simp [hσ2, Function.update_apply, hne (by decide : (25 : Fin 30) ≠ 26)])
    (by simp [hσ2])
    (fun i hi2 hi23 => by
      have a1 : i ≠ 25 := fun e => by subst e; simp at hi23
      have a2 : i ≠ 26 := fun e => by subst e; simp at hi23
      simp [hσ2, Function.update_apply, hne a1, hne a2, hz i hi2])
    (by simp [hσ2, Function.update_apply, hne (by decide : (27 : Fin 30) ≠ 26), hne (by decide : (27 : Fin 30) ≠ 25),
      hz 27 (by decide)])
    (by simp [hσ2, Function.update_apply, hne (by decide : (28 : Fin 30) ≠ 26), hne (by decide : (28 : Fin 30) ≠ 25),
      hz 28 (by decide)])
    (by simp [hσ2, Function.update_apply, hne (by decide : (29 : Fin 30) ≠ 26), hne (by decide : (29 : Fin 30) ≠ 25),
      hz 29 (by decide)])
    (by simp [hσ2, hO, hOh]) hcap
    (by simp [hσ2, Function.update_apply, hne (by decide : (24 : Fin 30) ≠ 26), hne (by decide : (24 : Fin 30) ≠ 25),
      z24, hw]) hJ hLc hMc
  set u := tplWord M Sv J L with hu
  set σ3 := appendO σ2 O (W 24) u with hσ3
  have h3v : σ3.val (W 24) = u.length := by
    simp [hσ3, hσ2, Function.update_apply, hne (by decide : (24 : Fin 30) ≠ 26),
      hne (by decide : (24 : Fin 30) ≠ 25), z24]
  have e4 := wrewind_spec cap O (W 24) u.length σ3 h3v (by rw [h3v]; exact hw)
  set σ4 := (σ3.setv (W 24) 0).seth O (σ3.sh O - u.length) with hσ4
  have e5 := PrimAsm.SparseNum.clear1 cap (W 25) M σ4
    (by simp [hσ4, hσ3, hσ2, Function.update_apply, hne (by decide : (25 : Fin 30) ≠ 24),
      hne (by decide : (25 : Fin 30) ≠ 26)]) hMc
  have e6 := PrimAsm.SparseNum.clear1 cap (W 26) L (σ4.setv (W 25) 0)
    (by simp [hσ4, hσ3, hσ2, Function.update_apply, hne (by decide : (26 : Fin 30) ≠ 24),
      hne (by decide : (26 : Fin 30) ≠ 25)]) hLc
  have hsq : PrimAsm.UnaryPow.sq cap ≤ 200 * (cap + 2) ^ 3 := by
    have h := Nat.pow_le_pow_right (show 1 ≤ cap + 2 by omega) (show 2 ≤ 3 by norm_num)
    have e : PrimAsm.UnaryPow.sq cap = 200 * (cap + 2) ^ 2 := by unfold PrimAsm.UnaryPow.sq; ring
    omega
  have hT := tplWBound_le cap J M hJ hMc
  have h3 : cap + 2 ≤ (cap + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  refine ⟨_, ?_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_
    le_rfl⟩
  · omega
  · refine WState.eq ?_ ?_ ?_ ?_
    · funext i
      by_cases hi : i = O
      · subst hi; simp [hσ4, hσ3, hσ2, hOh]
      · simp [hσ4, hσ3, hσ2, Function.update_apply, hi]
    · funext i
      by_cases hi : i = O
      · subst hi; simp [hσ4, hσ3, hσ2, hO]
      · simp [hσ4, hσ3, hσ2, Function.update_apply, hi]
    · funext q
      by_cases q24 : q = W 24
      · subst q24
        simp [hσ4, hσ3, hσ2, Function.update_apply, hne (by decide : (24 : Fin 30) ≠ 26),
          hne (by decide : (24 : Fin 30) ≠ 25), z24]
      · by_cases q25 : q = W 25
        · subst q25; simp [Function.update_apply, hne (by decide : (25 : Fin 30) ≠ 26), z25]
        · by_cases q26 : q = W 26
          · subst q26; simp [z26]
          · simp [hσ4, hσ3, hσ2, Function.update_apply, q24, q25, q26]
    · simp [hσ4, hσ3, hσ2]

end Kit

end NearCubicWires.WireExponent3_5.FinalPass.Out.SwL
