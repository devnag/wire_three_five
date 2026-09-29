import Proof.Wire_3_5.UnionMachine.RadAsm0

/-! # RADIX assembly (1): the numbers (stage 3) on the setup's cell (P3:2585-2623)

From the level records `winRecs` on stream `131` (head `0`) and the inputs `G = |thrPool|` (`414`), `row` (`413`),
`M` (`423`), `τ₀` (`422`), `J` (`426`), `p` (`411`): the scan (`RadScan.scanLoop_spec`) gives `S1 = Σ_j W'_j` and
`S2 = |winRecs|`, stream `131` is rewound, the eight inputs go to `rQ 0 … 7`, and `RadNums.numsP` computes Route B's
numbers `lb = 4S1+1`, `Mlab = (4row+4)G`, `lw = M+2+S2+(J+1)G`, `X`, `U = 2^20 X`, `R = U^40`, `cap = U^45`,
`Lg = R+1` into `rQ 8 … 15`.

* `ph2` / **`ph2_spec`**: the numbers; only `rY 2` (the scan's decoder sum) and the block `rQ` change.

Paper quantity of the main type: the RADIX row's Route-B numbers (`RadSpec.reqB`'s `R`, `Lg`, `cap`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.FinalPass.Hash4

variable (cap : ℕ) (x : ℕ)

/-- **Stage 3 on the cell.** -/
def ph2 : WM (LNS x) LNR :=
  .seq (RadScan.scanLoop (sk x 131) (rY 1) (rY 2) (rY 3))
  (.seq (wcopyR (rY 1) (rQ 7) (rY 4))
  (.seq (WM.rewind (sk x 131) (rY 1))
  (.seq (WM.move (rY 3) (rQ 6))
  (.seq (wcopyR (rIn 4) (rQ 0) (rY 4)) (.seq (wcopyR (rIn 3) (rQ 1) (rY 4)) (.seq (wcopyR (rIn 13) (rQ 2) (rY 4))
  (.seq (wcopyR (rIn 12) (rQ 3) (rY 4)) (.seq (wcopyR (rIn 16) (rQ 4) (rY 4)) (.seq (wcopyR (rIn 1) (rQ 5) (rY 4))
    (RadNums.numsP rQ))))))))))

/-- Stage 3's cost. -/
def ph2Cost (n S1 G row M τ J p c : ℕ) : ℕ :=
  (13 * n + 1) + 1 + ((18 * n + 3) + 1 + ((5 * n + 1) + 1 + ((7 * S1 + 1) + 1 + ((18 * G + 3) + 1 + ((18 * row + 3) + 1 +
    ((18 * M + 3) + 1 + ((18 * τ + 3) + 1 + ((18 * J + 3) + 1 + ((18 * p + 3) + 1 + RadNums.numsCost c)))))))))

/-- The Route-B `X` of the numbers. -/
def xOf (G row M τ J p S1 S2 : ℕ) : ℕ :=
  RadSpec.radX M τ G ((4 * row + 4) * G) (4 * S1 + 1) (M + 2 + S2 + (J + 1) * G) p 2

theorem ph2_spec (σ : WState (LNS x) LNR) (l : List (ℕ × ℕ)) (G row M τ J p : ℕ)
    (hW : σ.st (sk x 131) = RadScan.recsW l) (hWh : σ.sh (sk x 131) = 0)
    (hG : σ.val (rIn 4) = G) (hrow : σ.val (rIn 3) = row) (hM : σ.val (rIn 13) = M) (hτ : σ.val (rIn 12) = τ)
    (hJ : σ.val (rIn 16) = J) (hp : σ.val (rIn 1) = p)
    (hy : ∀ i : Fin 32, σ.val (rY i) = 0) (hq : ∀ i : Fin 48, σ.val (rQ i) = 0)
    (hc1 : (RadScan.recsW l).length + (l.map Prod.fst).sum + (l.map Prod.snd).sum + G + row + M + τ + J + p ≤ cap)
    (hcap : (1048576 * xOf G row M τ J p (l.map Prod.snd).sum (RadScan.recsW l).length) ^ 45 + 1048576 + 4 * row + J +
      8 ≤ cap) :
    ∃ τ' : WState (LNS x) LNR, WExec cap (ph2 x) σ τ'
        (ph2Cost (RadScan.recsW l).length (l.map Prod.snd).sum G row M τ J p cap) ∧
      Keep σ τ' (fun _ => False) (fun r => r = rY 2 ∨ r.val < 48) ∧
      τ'.val (rQ 0) = G ∧ τ'.val (rQ 1) = row ∧ τ'.val (rQ 2) = M ∧ τ'.val (rQ 3) = τ ∧ τ'.val (rQ 4) = J ∧
      τ'.val (rQ 5) = p ∧ τ'.val (rQ 7) = (RadScan.recsW l).length ∧ τ'.val (rQ 8) = 4 * (l.map Prod.snd).sum + 1 ∧ τ'.val (rQ 9) = (4 * row + 4) * G ∧
      τ'.val (rQ 10) = M + 2 + (RadScan.recsW l).length + (J + 1) * G ∧
      τ'.val (rQ 12) = 1048576 * xOf G row M τ J p (l.map Prod.snd).sum (RadScan.recsW l).length ∧
      τ'.val (rQ 13) = (1048576 * xOf G row M τ J p (l.map Prod.snd).sum (RadScan.recsW l).length) ^ 40 ∧
      τ'.val (rQ 14) = (1048576 * xOf G row M τ J p (l.map Prod.snd).sum (RadScan.recsW l).length) ^ 45 ∧
      τ'.val (rQ 15) = (1048576 * xOf G row M τ J p (l.map Prod.snd).sum (RadScan.recsW l).length) ^ 40 + 1 := by
  have hQY : ∀ i j, rQ i ≠ rY j := QY
  have hYQ : ∀ j i, rY j ≠ rQ i := fun j i e => QY i j e.symm
  have hQI : ∀ i k h, rQ i ≠ rIn k h := Qin
  have hIQ : ∀ k h i, rIn k h ≠ rQ i := fun k h i e => Qin i k h e.symm
  have hYI : ∀ i k h, rY i ≠ rIn k h := Yin
  have hIY : ∀ k h i, rIn k h ≠ rY i := fun k h i e => Yin i k h e.symm
  have y1 := hy 1
  have y2 := hy 2
  have y3 := hy 3
  have y4 := hy 4
  -- 1: the scan
  have s1 := RadScan.scanLoop_spec cap (sk x 131) (rY 1) (rY 2) (rY 3) (rY.injective.ne (by decide))
    (rY.injective.ne (by decide)) (rY.injective.ne (by decide)) l σ [] (by simpa using hW) (by simpa using hWh)
    (by rw [y1]; omega) (by rw [y2]; omega) (by rw [y3]; omega)
  unfold RadScan.scanSt at s1
  simp only [hWh, y1, y2, y3, Nat.zero_add] at s1
  set n := (RadScan.recsW l).length with hn
  set a := (l.map Prod.fst).sum with ha
  set b := (l.map Prod.snd).sum with hb
  set σ1 := (((σ.seth (sk x 131) n).setv (rY 1) n).setv (rY 2) a).setv (rY 3) b with hσ1
  -- 2: S2 := n
  have s2 := wcopyR_spec cap (rY 1) (rQ 7) (rY 4) (hYQ 1 7) (rY.injective.ne (by decide)) (hQY 7 4) σ1
    (by simp [σ1, hQY, hq 7]) (by simp [σ1, y4]) (by simp [σ1]; omega)
  have v1 : σ1.val (rY 1) = n := by simp [σ1]
  rw [v1] at s2
  -- 3: rewind
  set σ2 := σ1.setv (rQ 7) n with hσ2
  have s3 := wrewind_spec cap (sk x 131) (rY 1) n σ2 (by simp [σ2, σ1, hYQ]) (by simp [σ2, σ1, hYQ]; omega)
  -- 4: S1 into rQ 6
  set σ3 := (σ2.setv (rY 1) 0).seth (sk x 131) (σ2.sh (sk x 131) - n) with hσ3
  have s4 := wmove_spec cap (rY 3) (rQ 6) (hYQ 3 6) b σ3 (by simp [σ3, σ2, σ1, hYQ]) (by simp [σ3, σ2, σ1, hYQ]; omega)
    (by simp [σ3, σ2, σ1, hYQ, hQY, hq 6]; omega)
  have e4 : (σ3.setv (rY 3) 0).setv (rQ 6) (σ3.val (rQ 6) + σ3.val (rY 3)) = (σ3.setv (rY 3) 0).setv (rQ 6) b := by
    simp [σ3, σ2, σ1, hYQ, hQY, hq 6]
  rw [e4] at s4
  set σ4 := (σ3.setv (rY 3) 0).setv (rQ 6) b with hσ4
  -- 5 … 10: the inputs
  have s5 := wcopyR_spec cap (rIn 4) (rQ 0) (rY 4) (hIQ 4 _ 0) (hIY 4 _ 4) (hQY 0 4) σ4
    (by simp [σ4, σ3, σ2, σ1, hQY, hq 0]) (by simp [σ4, σ3, σ2, σ1, hYQ, y4]) (by simp [σ4, σ3, σ2, σ1, hIQ, hIY, hG]; omega)
  have w5 : σ4.val (rIn 4) = G := by simp [σ4, σ3, σ2, σ1, hIQ, hIY, hG]
  rw [w5] at s5
  set σ5 := σ4.setv (rQ 0) G with hσ5
  have s6 := wcopyR_spec cap (rIn 3) (rQ 1) (rY 4) (hIQ 3 _ 1) (hIY 3 _ 4) (hQY 1 4) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, hQY, hq 1]) (by simp [σ5, σ4, σ3, σ2, σ1, hYQ, y4])
    (by simp [σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hrow]; omega)
  have w6 : σ5.val (rIn 3) = row := by simp [σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hrow]
  rw [w6] at s6
  set σ6 := σ5.setv (rQ 1) row with hσ6
  have s7 := wcopyR_spec cap (rIn 13) (rQ 2) (rY 4) (hIQ 13 _ 2) (hIY 13 _ 4) (hQY 2 4) σ6
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hQY, hq 2]) (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hYQ, y4])
    (by simp [σ6, σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hM]; omega)
  have w7 : σ6.val (rIn 13) = M := by simp [σ6, σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hM]
  rw [w7] at s7
  set σ7 := σ6.setv (rQ 2) M with hσ7
  have s8 := wcopyR_spec cap (rIn 12) (rQ 3) (rY 4) (hIQ 12 _ 3) (hIY 12 _ 4) (hQY 3 4) σ7
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hQY, hq 3]) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, y4])
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hτ]; omega)
  have w8 : σ7.val (rIn 12) = τ := by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hτ]
  rw [w8] at s8
  set σ8 := σ7.setv (rQ 3) τ with hσ8
  have s9 := wcopyR_spec cap (rIn 16) (rQ 4) (rY 4) (hIQ 16 _ 4) (hIY 16 _ 4) (hQY 4 4) σ8
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hQY, hq 4]) (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, y4])
    (by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hJ]; omega)
  have w9 : σ8.val (rIn 16) = J := by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hJ]
  rw [w9] at s9
  set σ9 := σ8.setv (rQ 4) J with hσ9
  have s10 := wcopyR_spec cap (rIn 1) (rQ 5) (rY 4) (hIQ 1 _ 5) (hIY 1 _ 4) (hQY 5 4) σ9
    (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hQY, hq 5]) (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, y4])
    (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hp]; omega)
  have w10 : σ9.val (rIn 1) = p := by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hIQ, hIY, hp]
  rw [w10] at s10
  set σ10 := σ9.setv (rQ 5) p with hσ10
  -- 11: the numbers
  have s11 := RadNums.numsP_spec cap rQ σ10 G row M τ J p b n
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, hQY])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, hQY])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, hQY])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, hQY])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, hQY])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, hQY])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, hQY])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, hQY])
    (fun i hi8 hi28 => by
      have n0 : i ≠ 0 := fun e => by subst e; simp at hi8
      have n1 : i ≠ 1 := fun e => by subst e; simp at hi8
      have n2 : i ≠ 2 := fun e => by subst e; simp at hi8
      have n3 : i ≠ 3 := fun e => by subst e; simp at hi8
      have n4 : i ≠ 4 := fun e => by subst e; simp at hi8
      have n5 : i ≠ 5 := fun e => by subst e; simp at hi8
      have n6 : i ≠ 6 := fun e => by subst e; simp at hi8
      have n7 : i ≠ 7 := fun e => by subst e; simp at hi8
      simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hQY, n0, n1, n2, n3, n4, n5, n6, n7, hq i])
    (by unfold xOf at hcap; exact hcap)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 s11)))))))))) (by unfold ph2Cost; omega), ?_, ?_⟩
  · refine ⟨fun i _ => ?_, fun r hr => ?_⟩
    · by_cases hi : i = sk x 131
      · subst hi; simp [RadNums.numsOut, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hWh]
      · simp [RadNums.numsOut, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, hi]
    · simp only [not_or] at hr
      obtain ⟨hr2, hr48⟩ := hr
      have nq : ∀ i : Fin 48, r ≠ rQ i := fun i e => hr48 (by rw [e, rQ_val]; exact i.isLt)
      by_cases h1 : r = rY 1
      · subst h1; simp [RadNums.numsOut, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, y1]
      · by_cases h3 : r = rY 3
        · subst h3; simp [RadNums.numsOut, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hYQ, y3]
        · simp [RadNums.numsOut, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, nq, h1, h3, hr2]
  · simp [RadNums.numsOut, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, xOf, hYQ, hQY]

end NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
