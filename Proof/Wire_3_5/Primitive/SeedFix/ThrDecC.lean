import Proof.Wire_3_5.Primitive.SeedFix.ThrDecB

/-! # THR decode front, part C: the call's numbers, composed (register-only)

`tNW = tN1W ; tN2W`: phase A (the request), C1 (the sixteen numbers `hashNums`, `HashDec.hC1_run`), C2 (the
carriers' lengths), D1 (the THR filter's parameters), the filter's numbers (`GapNums.gapNums_spec`), D3 (the unit
layout, `TOT`). **`tN_run`**: from the unit's fresh cell to **`TNums`**, the decoded numbers state: the streams as at
the entry but the data tape's head, the numbers in their registers, SymDec's block `H` zero, the registers below
`250` and `398 … 407` (the markers and the FILTER bank) zero, every register within the capacity.

Paper quantities of the main type: the THR call's numbers (`hashNums`), its filter's parameters and seed count, and
the THR tape's unit count `TOT` (P3:2543-2558, 3011-3016). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum

/-- **The decoded numbers state** of a THR unit. -/
structure TNums (x cap : ℕ) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool)
    (n a nc kh : ℕ) (hs xs : List ℕ) (FP : GapParams) (EU N2 pS nG TOT : ℕ) : Prop where
  st : σ.st = (CellLoopD.blankCellD x w out j u).st
  sh : ∀ s, s ≠ sk x 113 → σ.sh s = (CellLoopD.blankCellD x w out j u).sh s
  cell : σ.cell = false
  vN : σ.val dN = n
  vA : σ.val dA = a
  vNC : σ.val dNC = nc
  vLEN : σ.val LEN = w.length
  vKh : σ.val (SGb 8) = kh
  hb : ∀ k : Fin 32, k.val < 16 → σ.val (Hb k) = hs.getD k.val 0
  vXA : σ.val XA = xs.getD 0 0
  vXB : σ.val XB = xs.getD 1 0
  vMS : σ.val dMS = hs.getD 8 0
  g0 : σ.val (G 0) = FP.cap
  g1 : σ.val (G 1) = FP.len
  g2 : σ.val (G 2) = FP.errExp
  g55 : σ.val (G 55) = EU
  g53 : σ.val (G 53) = N2
  g52 : σ.val (G 52) = pS
  g41 : σ.val (G 41) = nG
  g56 : σ.val (G 56) = TOT
  g32 : σ.val (G 32) = 0
  zH : ∀ k, σ.val (H k) = 0
  zl : ∀ q : Fin LNR, q.val < 250 → σ.val q = 0
  zm : ∀ q : Fin LNR, 398 ≤ q.val → q.val < 408 → σ.val q = 0
  zTM : σ.val TM = 0
  zK : σ.val dK = 0
  bd : ∀ q, σ.val q ≤ cap

section N
variable (cap : ℕ) (x : ℕ)

/-- Phases A, C1, C2. -/
def tN1W (cr fe : ℕ) : WM (LNS x) LNR := .seq (tAW x cr fe) (.seq (hC1W x) (tC2W x))

/-- Phases D1, the filter's numbers, D3. -/
def tN2W : WM (LNS x) LNR := .seq (tD1W x) (.seq (GapNums.gapNumsW (KG.trans G)) (tD3W x))

/-- **The THR decode's numbers.** -/
def tNW (cr fe : ℕ) : WM (LNS x) LNR := .seq (tN1W x cr fe) (tN2W x)

theorem hC1Out_hb (σ : WState (LNS x) LNR) (l : List ℕ) (k : Fin 32) (hk : k.val < 16) :
    (hC1Out x σ l).val (Hb k) = 0 + l.getD k.val 0 := by
  unfold hC1Out
  fin_cases k <;> simp [Function.update_apply, Fin.ext_iff, Hb_val, -List.getD_eq_getElem?_getD] at hk ⊢

theorem hC1Out_other (σ : WState (LNS x) LNR) (l : List ℕ) (r : Fin LNR) (hr : r.val < 337 ∨ 353 ≤ r.val) :
    (hC1Out x σ l).val r = σ.val r := by
  have e : ∀ i : ℕ, i < 16 → r.val ≠ 337 + i := fun i hi => by omega
  unfold hC1Out
  simp [Function.update_apply, Fin.ext_iff, Hb_val, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
    e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega), e 10 (by omega),
    e 11 (by omega), e 12 (by omega), e 13 (by omega), e 14 (by omega), e 15 (by omega)]

/-- Phases D1, the filter's numbers, D3, run: the G block's values, every register outside `G` kept. -/
theorem tN2_run (σ : WState (LNS x) LNR) (nc n kh feL nG pS : ℕ) (FP : GapParams)
    (h0 : σ.val (Hb 0) = nc) (h1 : σ.val (Hb 1) = FP.cap) (h2 : σ.val (Hb 2) = nG) (h6 : σ.val (Hb 6) = pS)
    (hN : σ.val dN = n) (h8 : σ.val (SGb 8) = kh) (hF : σ.val (SGb 10) = feL)
    (zG : ∀ i, σ.val (G i) = 0) (zT : σ.val TM = 0)
    (hPl : FP.len = 2 * (n + 1) ^ 26) (hPe : FP.errExp = feL) (hPc1 : 1 ≤ FP.cap)
    (hc : FP.cap + feL + (n + 1) ^ 26 * 2 + n + 2 ≤ cap)
    (hcG1 : FP.cap * 32 + 2 ≤ cap) (hcG2 : FP.len + 8 ≤ cap) (hcG3 : FP.errExp + 4 ≤ cap)
    (hcG4 : 2 ^ (FP.seedBits + 1) ≤ cap) (hcG5 : FP.labelBits + FP.fieldBits + FP.walkLen + 512 ≤ cap)
    (hEU : (nc + 1) * 3 + 2 ≤ cap) (hkh : 2 ^ (2 * kh + 1) ≤ cap) (hv : 2 ^ FP.seedBits + nG + pS ≤ cap)
    (hm1 : 2 ^ FP.seedBits * nG ≤ cap) (hm2 : 2 ^ FP.seedBits * nG * pS ≤ cap)
    (hm3 : 2 ^ FP.seedBits * nG * pS * 2 ^ (2 * kh) ≤ cap)
    (hm4 : 2 ^ FP.seedBits * nG * pS * 2 ^ (2 * kh) * ((nc + 1) * 3 + 2) ≤ cap) :
    ∃ τ, WExec cap (tN2W x) σ τ (123 * UnaryPow.sq cap + 1 + (110 * UnaryPow.sq cap + 1 + 48 * UnaryPow.sq cap)) ∧
      τ.val (G 0) = FP.cap ∧ τ.val (G 1) = FP.len ∧ τ.val (G 2) = FP.errExp ∧
      τ.val (G 55) = (nc + 1) * 3 + 2 ∧ τ.val (G 53) = 2 ^ (2 * kh) ∧ τ.val (G 52) = pS ∧ τ.val (G 41) = nG ∧
      τ.val (G 56) = 2 ^ FP.seedBits * nG * pS * 2 ^ (2 * kh) * ((nc + 1) * 3 + 2) ∧ τ.val (G 32) = 0 ∧
      (∀ r : Fin LNR, (∀ i : Fin 64, r ≠ G i) → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell := by
  have e1 := tD1_run cap x σ FP.cap n feL h1 hN hF zG zT hc
  set σ1 := tD1Out x σ FP.cap n feL with hσ1
  have k1G : ∀ i : Fin 64, 3 ≤ i.val → i.val < 32 → σ1.val (G i) = 0 := fun i hi hi2 => by
    rw [hσ1]; unfold tD1Out
    have a0 : i.val ≠ 0 := by omega
    have a1 : i.val ≠ 1 := by omega
    have a2 : i.val ≠ 2 := by omega
    have a60 : i.val ≠ 60 := by omega
    simp [Function.update_apply, Fin.ext_iff, G_val, a0, a1, a2, a60, zG]
  have g0 : σ1.val (G 0) = FP.cap := by rw [hσ1]; unfold tD1Out; simp [Function.update_apply, Fin.ext_iff, G_val]
  have g1 : σ1.val (G 1) = FP.len := by
    rw [hσ1]; unfold tD1Out; simp [Function.update_apply, Fin.ext_iff, G_val, hPl, mul_comm]
  have g2 : σ1.val (G 2) = FP.errExp := by
    rw [hσ1]; unfold tD1Out; simp [Function.update_apply, Fin.ext_iff, G_val, hPe]
  have g32p : ∀ i : Fin 64, 32 ≤ i.val → σ1.val (G i) = 0 := fun i hi => by
    rw [hσ1]; unfold tD1Out
    have a0 : i.val ≠ 0 := by omega
    have a1 : i.val ≠ 1 := by omega
    have a2 : i.val ≠ 2 := by omega
    by_cases h60 : i.val = 60
    · simp [Function.update_apply, Fin.ext_iff, G_val, h60]
    · simp [Function.update_apply, Fin.ext_iff, G_val, a0, a1, a2, h60, zG]
  have hzK : ∀ i : Fin 32, 3 ≤ i.val → σ1.val ((KG.trans G) i) = 0 := fun i hi => by
    simp only [Function.Embedding.trans_apply]
    apply k1G
    · fin_cases i <;> simp at hi ⊢
    · fin_cases i <;> simp
  have hlen2 : 2 ≤ FP.len := by
    rw [hPl]; have := Nat.one_le_pow 26 (n + 1) (by omega); omega
  have e2 := GapNums.gapNums_spec cap (KG.trans G) σ1 FP
    (by simpa [KG_apply, Function.Embedding.trans_apply] using g0)
    (by simpa [KG_apply, Function.Embedding.trans_apply] using g1)
    (by simpa [KG_apply, Function.Embedding.trans_apply] using g2) hzK hPc1 hlen2 (by omega)
    hcG1 hcG2 hcG3 hcG4 hcG5
  set σ2 := (((((σ1.setv ((KG.trans G) 3) FP.prefixBits).setv ((KG.trans G) 4) FP.labelBits).setv
      ((KG.trans G) 5) FP.fieldBits).setv ((KG.trans G) 6) FP.walkLen).setv ((KG.trans G) 20) FP.seedBits).setv
      ((KG.trans G) 21) (2 ^ FP.seedBits) with hσ2
  have k1 : ∀ r : Fin LNR, (∀ i : Fin 64, r ≠ G i) → σ1.val r = σ.val r := by
    intro r hr
    rw [hσ1]; unfold tD1Out
    simp [Function.update_apply, hr]
  have k2 : ∀ r : Fin LNR, (∀ i : Fin 64, r ≠ G i) → σ2.val r = σ1.val r := by
    intro r hr
    rw [hσ2]
    simp [Function.update_apply, hr]
  have g21 : σ2.val (G 21) = 2 ^ FP.seedBits := by
    rw [hσ2]; simp [Function.Embedding.trans_apply, KG_apply]
  have gb2 : ∀ i : Fin 64, 32 ≤ i.val → σ2.val (G i) = σ1.val (G i) := fun i hi => by
    rw [hσ2]
    have a3 : i.val ≠ 3 := by omega
    have a4 : i.val ≠ 4 := by omega
    have a5 : i.val ≠ 5 := by omega
    have a6 : i.val ≠ 6 := by omega
    have a20 : i.val ≠ 20 := by omega
    have a21 : i.val ≠ 21 := by omega
    simp [Function.update_apply, Function.Embedding.trans_apply, KG_apply, Fin.ext_iff, G_val, a3, a4, a5, a6, a20,
      a21]
  have g0' : σ2.val (G 0) = FP.cap := by
    rw [hσ2]; simp [Function.update_apply, Function.Embedding.trans_apply, KG_apply, Fin.ext_iff, G_val, g0]
  have g1' : σ2.val (G 1) = FP.len := by
    rw [hσ2]; simp [Function.update_apply, Function.Embedding.trans_apply, KG_apply, Fin.ext_iff, G_val, g1]
  have g2' : σ2.val (G 2) = FP.errExp := by
    rw [hσ2]; simp [Function.update_apply, Function.Embedding.trans_apply, KG_apply, Fin.ext_iff, G_val, g2]
  have nGr : ∀ r : Fin LNR, r.val < 408 → ∀ i : Fin 64, r ≠ G i := fun r h i e => by rw [e, G_val] at h; omega
  have v2 : ∀ r : Fin LNR, r.val < 408 → σ2.val r = σ.val r := fun r h => by
    rw [k2 r (nGr r h), k1 r (nGr r h)]
  have e3 := tD3_run cap x σ2 nc nG pS kh (2 ^ FP.seedBits)
    (by rw [v2 _ (by rw [Hb_val]; omega)]; exact h0) (by rw [v2 _ (by rw [Hb_val]; omega)]; exact h2)
    (by rw [v2 _ (by rw [Hb_val]; omega)]; exact h6) (by rw [v2 _ (by rw [SGb_val]; omega)]; exact h8) g21
    (fun i hi => by rw [gb2 i hi]; exact g32p i hi) (by rw [v2 _ (by rw [rv_TM']; omega)]; exact zT)
    hEU hkh hv hm1 hm2 hm3 hm4
  set σ3 := tD3Out x σ2 nc nG pS kh (2 ^ FP.seedBits) with hσ3
  have k3 : ∀ r : Fin LNR, (∀ i : Fin 64, r ≠ G i) → σ3.val r = σ2.val r := by
    intro r hr
    rw [hσ3]; unfold tD3Out
    simp [Function.update_apply, tM3_apply, tP2_apply, tT1_apply, tT2_apply, tT3_apply, tT4_apply, hr]
  have gv3 : ∀ i : Fin 64, i.val < 32 → σ3.val (G i) = σ2.val (G i) := by
    intro i hi
    rw [hσ3]; unfold tD3Out
    have a : ∀ k : ℕ, 32 ≤ k → i.val ≠ k := fun k hk => by omega
    simp [Function.update_apply, tM3_apply, tP2_apply, tT1_apply, tT2_apply, tT3_apply, tT4_apply, Fin.ext_iff,
      G_val, a 55 (by omega), a 58 (by omega), a 57 (by omega), a 54 (by omega), a 53 (by omega), a 52 (by omega),
      a 41 (by omega), a 56 (by omega)]
  refine ⟨σ3, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gv3 0 (by decide)]; exact g0'
  · rw [gv3 1 (by decide)]; exact g1'
  · rw [gv3 2 (by decide)]; exact g2'
  · rw [hσ3]; unfold tD3Out; simp [Function.update_apply, Fin.ext_iff, G_val]
  · rw [hσ3]; unfold tD3Out; simp [Function.update_apply, Fin.ext_iff, G_val]
  · rw [hσ3]; unfold tD3Out; simp [Function.update_apply, Fin.ext_iff, G_val]
  · rw [hσ3]; unfold tD3Out; simp [Function.update_apply, Fin.ext_iff, G_val]
  · rw [hσ3]; unfold tD3Out; simp [Function.update_apply, Fin.ext_iff, G_val]
  · rw [hσ3]; unfold tD3Out
    simp [Function.update_apply, Fin.ext_iff, G_val]
    rw [gb2 32 (by decide)]; exact g32p 32 (by decide)
  · intro r hr
    rw [k3 r hr, k2 r hr, k1 r hr]
  · rw [hσ3]; unfold tD3Out; simp [hσ2, hσ1, tD1Out]
  · rw [hσ3]; unfold tD3Out; simp [hσ2, hσ1, tD1Out]
  · rw [hσ3]; unfold tD3Out; simp [hσ2, hσ1, tD1Out]

/-- **The numbers phase's capacity needs** (every register value the phase writes, and the gap numbers' needs). -/
structure TNeed (w : List Bool) (n : ℕ) (codes cc : List ℕ) (Kb cr fe : ℕ) (hs xs : List ℕ) (tg : ℕ)
    (FP : GapParams) (kh : ℕ) : Prop where
  c1 : 2 * w.length + 2 ≤ cap
  cP : 2 ^ (natBitLength n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
    Kb + n + codes.length + 1 ≤ cap
  c3 : (fe + 4) * (n + 3) + 2 * cr + 20 ≤ cap
  cl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap
  cD : FP.cap + fe * Nat.clog 2 (n + 2) + (n + 1) ^ 26 * 2 + n + 2 ≤ cap
  cG1 : FP.cap * 32 + 2 ≤ cap
  cG2 : FP.len + 8 ≤ cap
  cG3 : FP.errExp + 4 ≤ cap
  cG4 : 2 ^ (FP.seedBits + 1) ≤ cap
  cG5 : FP.labelBits + FP.fieldBits + FP.walkLen + 512 ≤ cap
  cEU : (xs.length + 1) * 3 + 2 ≤ cap
  ckh : 2 ^ (2 * kh + 1) ≤ cap
  cv : 2 ^ FP.seedBits + hs.getD 2 0 + hs.getD 6 0 ≤ cap
  cm1 : 2 ^ FP.seedBits * hs.getD 2 0 ≤ cap
  cm2 : 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 ≤ cap
  cm3 : 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * kh) ≤ cap
  cm4 : 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * kh) * ((xs.length + 1) * 3 + 2) ≤ cap

/-- The numbers phase's cost. -/
def tNCost (n a nc Kb cr fe cap : ℕ) : ℕ :=
  tACost n a nc Kb cr fe cap + 1 + (34 * UnaryPow.sq cap + 1 + 20 * UnaryPow.sq cap) + 1 +
    (123 * UnaryPow.sq cap + 1 + (110 * UnaryPow.sq cap + 1 + 48 * UnaryPow.sq cap))

end N

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
