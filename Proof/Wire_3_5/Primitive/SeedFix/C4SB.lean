import Proof.Wire_3_5.Primitive.SeedFix.C4SA
import Proof.Wire_3_5.Primitive.Writers.SymDecRun

/-! # C4 per-call setup (item 3), part 2: the SYM call's numbers in registers

P3:2987-2988, 3154-3162 (`samp:q`: the SYM sample count `Q = symCount`), P3:3011-3016 (the state matrices `t < n_T`,
`n_T = |GapSeed|·|FlatSeed|·Π_j(m_j+1)²`), P3:1188-1189 (the star numbers `r, s, b, k`, `kh = s·(r/2)`): from the SYM
call's request `frame w` and its counts (the carriers' sizes and the circuits' bottom counts, `Data.unaryList`), on PA's
SYM-decode layout at the capacity `cap`:

1. PA's decode first stage `p1W` (`n`, `a`, `|carriers|`, the counts `m_j`, `Σm_j`);
2. PA's `starCapW` (the star numbers in `SGb`, the SYM cap `B_S` in `Hb 13`);
3. PA's `symNumsW` (the block `G`: `|GapSeed| = G 21`, `|FlatSeed| = G 41`, `Π_j(m_j+1)² = G 52`, …);
4. `kLoadW` (the count's inputs into the block `KB 0 … 10`), PA's `SymQM.symQW` (`Q` into `KB 52`).

* `KB`, `rT0`, `kLoadW`, `numsSW`, `symInOf`, `numsSCost`, **`numsS_spec`**.

Paper quantities of the main type: `SeedFix.symCount`'s value `Q` (`symQval`), `|GapSeed|`, `|FlatSeed|`, `Π(m_j+1)²`,
the star numbers and the SYM cap. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

/-- The count's register block: registers `0 … 63` (below every block of PA's decode). -/
def KB : Fin 64 ↪ Fin LNR := ⟨fun i => ⟨i.val, by have := i.isLt; unfold LNR; omega⟩,
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simpa using this)⟩

theorem KB_val (i : Fin 64) : (KB i).val = i.val := rfl

/-- The copies' scratch register. -/
def rT0 : Fin LNR := ⟨100, by decide⟩

/-- The count's input registers: the SYM cap, `n`, the error exponent, `L`, `kh`, `|carriers|`, `a`, the four bottom
counts. -/
def srcR : Fin 11 → Fin LNR := ![Hb 13, dN, SGb 10, SGb 1, SGb 8, dNC, dA, dM0, dM1, dM2, dM3]

theorem srcR_ge (j : Fin 11) : 250 ≤ (srcR j).val := by fin_cases j <;> decide

theorem srcR_ne_T (j : Fin 11) : srcR j ≠ rT0 := by fin_cases j <;> decide

/-- The first `k` copies. -/
def kLW : ℕ → WM (LNS 0) LNR
  | 0 => .skip
  | k + 1 => if h : k < 11 then .seq (kLW k) (FinalPass.Hash4.wcopyR (srcR ⟨k, h⟩) (KB ⟨k, by omega⟩) rT0) else kLW k

/-- **The count's inputs into `KB 0 … 10`.** -/
def kLoadW : WM (LNS 0) LNR := kLW 11

/-- The state after the first `k` copies. -/
def kPart (σ : WState (LNS 0) LNR) (v : Fin 11 → ℕ) : ℕ → WState (LNS 0) LNR
  | 0 => σ
  | k + 1 => if h : k < 11 then (kPart σ v k).setv (KB ⟨k, by omega⟩) (v ⟨k, h⟩) else kPart σ v k

theorem kPart_st (σ : WState (LNS 0) LNR) (v : Fin 11 → ℕ) : ∀ k, (kPart σ v k).st = σ.st
  | 0 => rfl
  | k + 1 => by unfold kPart; split_ifs <;> simp [WState.setv, kPart_st σ v k]

theorem kPart_sh (σ : WState (LNS 0) LNR) (v : Fin 11 → ℕ) : ∀ k, (kPart σ v k).sh = σ.sh
  | 0 => rfl
  | k + 1 => by unfold kPart; split_ifs <;> simp [WState.setv, kPart_sh σ v k]

theorem kPart_cell (σ : WState (LNS 0) LNR) (v : Fin 11 → ℕ) : ∀ k, (kPart σ v k).cell = σ.cell
  | 0 => rfl
  | k + 1 => by unfold kPart; split_ifs <;> simp [WState.setv, kPart_cell σ v k]

theorem wc (cap : ℕ) (a b : Fin LNR) (σ : WState (LNS 0) LNR) (hab : a ≠ b) (hat : a ≠ rT0) (hbt : b ≠ rT0)
    (hb : σ.val b = 0) (ht : σ.val rT0 = 0) (ha : σ.val a ≤ cap) :
    WExec cap (FinalPass.Hash4.wcopyR a b rT0) σ (σ.setv b (σ.val a)) (18 * σ.val a + 3) :=
  FinalPass.Hash4.wcopyR_spec cap a b rT0 hab hat hbt σ hb ht ha

theorem KB_mk_val (k : ℕ) (h : k < 64) : (KB ⟨k, h⟩).val = k := rfl

theorem kPart_other (σ : WState (LNS 0) LNR) (v : Fin 11 → ℕ) (r : Fin LNR) (hr : 11 ≤ r.val) :
    ∀ k, (kPart σ v k).val r = σ.val r
  | 0 => rfl
  | k + 1 => by
    unfold kPart
    by_cases hk : k < 11
    · rw [dif_pos hk]
      have e : r ≠ KB ⟨k, by omega⟩ := fun e' => by
        have := congrArg Fin.val e'; rw [KB_mk_val] at this; omega
      simp only [WState.setv, Function.update_apply, if_neg e]
      exact kPart_other σ v r hr k
    · rw [dif_neg hk]; exact kPart_other σ v r hr k

theorem kPart_KB (σ : WState (LNS 0) LNR) (v : Fin 11 → ℕ) (i : ℕ) (hi : i < 11) :
    ∀ k, (kPart σ v k).val (KB ⟨i, by omega⟩) = if i < k then v ⟨i, hi⟩ else σ.val (KB ⟨i, by omega⟩)
  | 0 => by simp [kPart]
  | k + 1 => by
    unfold kPart
    by_cases hk : k < 11
    · rw [dif_pos hk]
      simp only [WState.setv, Function.update_apply]
      by_cases e : i = k
      · subst e; simp
      · have e' : KB ⟨i, by omega⟩ ≠ KB ⟨k, by omega⟩ := fun e2 => by
          have := congrArg Fin.val e2; rw [KB_mk_val, KB_mk_val] at this; exact e this
        rw [if_neg e', kPart_KB σ v i hi k]
        by_cases h1 : i < k
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    · rw [dif_neg hk, kPart_KB σ v i hi k]
      have h1 : i < k := by omega
      rw [if_pos h1, if_pos (by omega)]

/-- **The first `k` copies, run.** -/
theorem kLW_spec (cap : ℕ) (σ : WState (LNS 0) LNR) (v : Fin 11 → ℕ) (hsrc : ∀ j, σ.val (srcR j) = v j)
    (hz : ∀ r : Fin LNR, r.val < 11 → σ.val r = 0) (ht : σ.val rT0 = 0) (hc : ∀ j, v j ≤ cap) :
    ∀ k, k ≤ 11 → WExec cap (kLW k) σ (kPart σ v k) (k * (18 * cap + 5))
  | 0, _ => by simpa [kLW, kPart] using WExec.skip (cap := cap) σ
  | k + 1, hk => by
    have ih := kLW_spec cap σ v hsrc hz ht hc k (by omega)
    have hk' : k < 11 := by omega
    simp only [kLW, kPart, dif_pos hk']
    have ekv : (kPart σ v k).val (srcR ⟨k, hk'⟩) = v ⟨k, hk'⟩ := by
      rw [kPart_other σ v _ (by have := srcR_ge ⟨k, hk'⟩; omega)]; exact hsrc _
    have ekb : (kPart σ v k).val (KB ⟨k, by omega⟩) = 0 := by
      rw [kPart_KB σ v k hk' k, if_neg (by omega)]; exact hz _ (by rw [KB_val]; exact hk')
    have ekt : (kPart σ v k).val rT0 = 0 := by
      rw [kPart_other σ v _ (by decide)]; exact ht
    have hne : srcR ⟨k, hk'⟩ ≠ KB ⟨k, by omega⟩ := fun e => by
      have := congrArg Fin.val e; rw [KB_val] at this; have := srcR_ge ⟨k, hk'⟩; omega
    have hkt : KB ⟨k, by omega⟩ ≠ rT0 := fun e => by
      have := congrArg Fin.val e; rw [KB_val] at this; simp [rT0] at this; omega
    have w := wc cap (srcR ⟨k, hk'⟩) (KB ⟨k, by omega⟩) (kPart σ v k) hne (srcR_ne_T _) hkt ekb ekt
      (by rw [ekv]; exact hc _)
    rw [ekv] at w
    refine WExec.cast cap (WExec.seq ih w) rfl ?_
    have := hc ⟨k, hk'⟩
    nlinarith

/-- **The SYM numbers program.** -/
def numsSW (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM (LNS 0) LNR :=
  .seq (p1W 0) (.seq (starCapW 0 cr fe ζ Cδ C) (.seq (symNumsW 0) (.seq kLoadW (SymQM.symQW KB))))

/-- The count's inputs at the call's numbers. -/
def symInOf (capS n err L kh nc a : ℕ) (cy : List ℕ) : SymQM.SymIn :=
  ⟨capS, n, err, L, kh, nc, a, fun j => cy.getD j.val 0⟩

/-- The numbers program's step bound. -/
def numsSCost (cap n cr fe t sp L a nc Kb Cmax M : ℕ) : ℕ :=
  (4 * UnaryPow.sq cap + 1 + (reqParseCost n a nc Kb + 1 + (5 * UnaryPow.sq cap + 1 +
    (30 * UnaryPow.sq cap + 1 + countsCost nc Cmax M)))) + 1 +
  (starCapCost n cr fe t sp L cap + 1 + (500 * UnaryPow.sq cap + 1 + (11 * (18 * cap + 5) + 1 + 600 * UnaryPow.sq cap)))


/-- **The SYM call's numbers, run**: from the cell's entry (the request, the counts), the decode's numbers, the star
numbers, the SYM cap, the block `G`, and the count `Q` in `KB 52`; the registers `64 … 249` still `0`; the streams
as at entry (the counts' head aside). -/
theorem numsS_spec (cap cr fe : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w : List Bool) (codes ccs : List ℕ) (tl : List Bool)
    (cx cy : List ℕ) (Kb Cmax capS err L kh : ℕ)
    (hw : w = Data.reqW P.n false codes ccs tl) (hccs : ccs.length = cx.length) (hcx : cx.length ≤ 2)
    (hcy : cy.length ≤ 4) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hC : ∀ c ∈ cx ++ cy, c ≤ Cmax)
    (hN1 : P1Need cap w P.n codes ccs cx cy Kb Cmax)
    (hcapS : capS = Ledger.rowBCap C .sym P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (herr : err = fe * Ledger.Lq P.n) (hL : L = Ledger.Lq P.n) (hkh : kh = P.s * (P.r / 2))
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq P.n) (Ledger.rowBt h0 h1 P.n - 1) ≤ cap)
    (hcC : CapNeed C .sym P.n P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) cap)
    (hN2 : NumsNeed cap P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
      (cy.getD 3 0))
    (hn : 2 ≤ P.n) (hQ : 2 * (symInOf capS P.n err L kh cx.length codes.length cy).Q ≤ cap)
    (hv : ∀ j : Fin 11, (![capS, P.n, err, L, kh, cx.length, codes.length, cy.getD 0 0, cy.getD 1 0, cy.getD 2 0,
      cy.getD 3 0] : Fin 11 → ℕ) j ≤ cap) :
    ∃ τ c, WExec cap (numsSW cr fe ζ Cδ C) (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (cx ++ cy))) τ c ∧
      τ.val dN = P.n ∧ τ.val dA = codes.length ∧ τ.val dNC = cx.length ∧
      τ.val dM0 = cy.getD 0 0 ∧ τ.val dM1 = cy.getD 1 0 ∧ τ.val dM2 = cy.getD 2 0 ∧ τ.val dM3 = cy.getD 3 0 ∧
      τ.val dMS = cy.sum ∧ τ.val (SGb 1) = L ∧ τ.val (SGb 3) = P.r ∧ τ.val (SGb 4) = P.s ∧ τ.val (SGb 5) = P.b ∧
      τ.val (SGb 6) = P.r / 2 ∧
      τ.val (SGb 8) = kh ∧ τ.val (SGb 9) = P.k ∧ τ.val (SGb 10) = err ∧ τ.val (Hb 13) = capS ∧
      (∀ i, τ.val (G i) = numsVec P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0)
        (cy.getD 2 0) (cy.getD 3 0) i) ∧
      τ.val (KB 52) = (symInOf capS P.n err L kh cx.length codes.length cy).Q ∧
      (∀ q : Fin LNR, 64 ≤ q.val → q.val < 250 → τ.val q = 0) ∧
      τ.st = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (cx ++ cy))).st ∧
      (∀ s, s ≠ sk 0 113 → τ.sh s = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (cx ++ cy))).sh s) ∧
      τ.cell = false ∧
      c ≤ numsSCost cap P.n cr fe (Ledger.rowBt h0 h1 P.n) (Ledger.rowBSparse h0 h1 2 Cδ P.n) (Ledger.Lq P.n)
        codes.length cx.length Kb Cmax cy.sum := by
  obtain ⟨τ1, c1, e1, v1N, v1A, v1NC, v1M0, v1M1, v1M2, v1M3, v1MS, v1XA, v1XB, z1, v1L, s1, sh1, cl1, c1le⟩ :=
    p1_spec cap 0 w [] 0 P.n codes ccs tl cx cy Kb Cmax hw hccs hcx hcy hKb hC hN1
  have nv : ∀ (r q : Fin LNR), r.val ≠ q.val → r ≠ q := fun r q h e => h (congrArg Fin.val e)
  have zP1 : ∀ r : Fin LNR, (r.val < 320 ∨ (323 ≤ r.val ∧ r.val < 330) ∨ (335 ≤ r.val ∧ r.val < 369) ∨
      372 ≤ r.val) → τ1.val r = 0 := fun r h =>
    z1 r (nv _ _ (by show r.val ≠ 320; omega)) (nv _ _ (by show r.val ≠ 321; omega)) (nv _ _ (by show r.val ≠ 322; omega))
      (nv _ _ (by show r.val ≠ 330; omega)) (nv _ _ (by show r.val ≠ 331; omega)) (nv _ _ (by show r.val ≠ 332; omega))
      (nv _ _ (by show r.val ≠ 333; omega)) (nv _ _ (by show r.val ≠ 334; omega)) (nv _ _ (by show r.val ≠ 369; omega))
      (nv _ _ (by show r.val ≠ 370; omega)) (nv _ _ (by show r.val ≠ 371; omega))
  obtain ⟨τ2, c2, e2, q1, q3, q4, q5, q6, q8, q9, q10, -, q13, k2, st2, sh2, cl2, c2le⟩ :=
    starCap_spec cap 0 cr fe h0 h1 Cδ C P hrP τ1 v1N
      (fun i => zP1 _ (by rw [SGb_val]; have := i.isLt; omega)) (fun i => zP1 _ (by rw [Gb_val]; have := i.isLt; omega))
      (fun i => zP1 _ (by rw [Hb_val]; have := i.isLt; omega)) (zP1 _ (by decide)) hcS hcP hcC
  have oN : Outside dN := by unfold SymDec.Outside; decide
  have oA : Outside dA := by unfold SymDec.Outside; decide
  have oNC : Outside dNC := by unfold SymDec.Outside; decide
  have oM0 : Outside dM0 := by unfold SymDec.Outside; decide
  have oM1 : Outside dM1 := by unfold SymDec.Outside; decide
  have oM2 : Outside dM2 := by unfold SymDec.Outside; decide
  have oM3 : Outside dM3 := by unfold SymDec.Outside; decide
  have oMS : Outside dMS := by unfold SymDec.Outside; decide
  have hz2 : ∀ i, τ2.val (G i) = 0 := fun i => by rw [k2 _ (out_G i)]; exact zP1 _ (by rw [G_val]; omega)
  have e3 := symNums_spec 0 cap τ2 P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0)
    (cy.getD 2 0) (cy.getD 3 0) (by rw [q13, hcapS]) (by rw [k2 _ oN, v1N]) (by rw [q10, herr])
    (by rw [k2 _ oMS, v1MS]) (by rw [k2 _ oNC, v1NC]) (by rw [q1, hL]) (by rw [q8, hkh]) (by rw [k2 _ oA, v1A])
    (by rw [k2 _ oM0, v1M0]) (by rw [k2 _ oM1, v1M1]) (by rw [k2 _ oM2, v1M2]) (by rw [k2 _ oM3, v1M3]) hz2 hN2
  set τ3 := numsOut 0 τ2 P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
    (cy.getD 3 0) with hτ3
  have g3 := fun i => numsOut_val 0 τ2 P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0)
    (cy.getD 2 0) (cy.getD 3 0) hz2 i
  have k3 : ∀ r, (∀ i, G i ≠ r) → τ3.val r = τ2.val r := fun r hr =>
    numsOut_other 0 τ2 P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0) (cy.getD 1 0) (cy.getD 2 0)
      (cy.getD 3 0) r hr
  have st3 : τ3.st = τ2.st := numsOut_st 0 τ2 P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0)
    (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0)
  have sh3 : τ3.sh = τ2.sh := numsOut_sh 0 τ2 P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0)
    (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0)
  have cl3 : τ3.cell = τ2.cell := numsOut_cell 0 τ2 P.n capS err cy.sum cx.length L kh codes.length (cy.getD 0 0)
    (cy.getD 1 0) (cy.getD 2 0) (cy.getD 3 0)
  have nG : ∀ r : Fin LNR, r.val < 408 → ∀ i, G i ≠ r := fun r h i e => by rw [← e, G_val] at h; omega
  -- the low registers
  have low3 : ∀ q : Fin LNR, q.val < 250 → τ3.val q = 0 := fun q hq => by
    rw [k3 _ (nG q (by omega)), k2 q (by unfold SymDec.Outside; omega)]; exact zP1 q (by omega)
  -- the count's inputs
  set v : Fin 11 → ℕ := ![capS, P.n, err, L, kh, cx.length, codes.length, cy.getD 0 0, cy.getD 1 0, cy.getD 2 0,
    cy.getD 3 0] with hvd
  have hsrc : ∀ j, τ3.val (srcR j) = v j := by
    intro j
    fin_cases j
    · show τ3.val (Hb 13) = capS; rw [k3 _ (nG _ (by decide)), q13, hcapS]
    · show τ3.val dN = P.n; rw [k3 _ (nG _ (by decide)), k2 _ oN, v1N]
    · show τ3.val (SGb 10) = err; rw [k3 _ (nG _ (by decide)), q10, herr]
    · show τ3.val (SGb 1) = L; rw [k3 _ (nG _ (by decide)), q1, hL]
    · show τ3.val (SGb 8) = kh; rw [k3 _ (nG _ (by decide)), q8, hkh]
    · show τ3.val dNC = cx.length; rw [k3 _ (nG _ (by decide)), k2 _ oNC, v1NC]
    · show τ3.val dA = codes.length; rw [k3 _ (nG _ (by decide)), k2 _ oA, v1A]
    · show τ3.val dM0 = cy.getD 0 0; rw [k3 _ (nG _ (by decide)), k2 _ oM0, v1M0]
    · show τ3.val dM1 = cy.getD 1 0; rw [k3 _ (nG _ (by decide)), k2 _ oM1, v1M1]
    · show τ3.val dM2 = cy.getD 2 0; rw [k3 _ (nG _ (by decide)), k2 _ oM2, v1M2]
    · show τ3.val dM3 = cy.getD 3 0; rw [k3 _ (nG _ (by decide)), k2 _ oM3, v1M3]
  have e4 := kLW_spec cap τ3 v hsrc (fun r hr => low3 r (by omega)) (low3 rT0 (by decide)) hv 11 le_rfl
  set τ4 := kPart τ3 v 11 with hτ4
  have ev : ∀ k (hk : k < 11), τ4.val (KB ⟨k, by omega⟩) = v ⟨k, hk⟩ := fun k hk => by
    rw [hτ4, kPart_KB τ3 v k hk 11, if_pos hk]
  have hin : SymQM.InBlk KB τ4 (symInOf capS P.n err L kh cx.length codes.length cy) :=
    ⟨by exact ev 0 (by decide), by exact ev 1 (by decide), by exact ev 2 (by decide), by exact ev 3 (by decide),
      by exact ev 4 (by decide), by exact ev 5 (by decide), by exact ev 6 (by decide), by exact ev 7 (by decide),
      by exact ev 8 (by decide), by exact ev 9 (by decide), by exact ev 10 (by decide), fun i hi => by
      rw [hτ4, kPart_other τ3 v (KB i) (by rw [KB_val]; exact hi)]; exact low3 _ (by rw [KB_val]; omega)⟩
  obtain ⟨τ5, e5, q52, -, frm⟩ := SymQM.symQ_spec cap KB τ4 _ hin
    (by show 1 ≤ capS; exact hN2.c1) hn hQ
  obtain ⟨st5, sh5, cl5, k5⟩ := frm
  have nK : ∀ r : Fin LNR, 64 ≤ r.val → ∀ i, KB i ≠ r := fun r h i e => by rw [← e, KB_val] at h; omega
  have back : ∀ r : Fin LNR, 250 ≤ r.val → r.val < 408 → τ5.val r = τ2.val r := fun r h1' h2' => by
    rw [k5 r (nK r (by omega)), hτ4, kPart_other τ3 v r (by omega), k3 r (nG r h2')]
  refine ⟨τ5, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i => ?_, ?_, fun q hq1 hq2 => ?_, ?_, fun s hs => ?_, ?_, ?_⟩
  · rw [back _ (by decide) (by decide), k2 _ oN, v1N]
  · rw [back _ (by decide) (by decide), k2 _ oA, v1A]
  · rw [back _ (by decide) (by decide), k2 _ oNC, v1NC]
  · rw [back _ (by decide) (by decide), k2 _ oM0, v1M0]
  · rw [back _ (by decide) (by decide), k2 _ oM1, v1M1]
  · rw [back _ (by decide) (by decide), k2 _ oM2, v1M2]
  · rw [back _ (by decide) (by decide), k2 _ oM3, v1M3]
  · rw [back _ (by decide) (by decide), k2 _ oMS, v1MS]
  · rw [back _ (by decide) (by decide), q1, hL]
  · rw [back _ (by decide) (by decide), q3]
  · rw [back _ (by decide) (by decide), q4]
  · rw [back _ (by decide) (by decide), q5]
  · rw [back _ (by decide) (by decide), q6]
  · rw [back _ (by decide) (by decide), q8, hkh]
  · rw [back _ (by decide) (by decide), q9]
  · rw [back _ (by decide) (by decide), q10, herr]
  · rw [back _ (by decide) (by decide), q13, hcapS]
  · rw [k5 _ (nK _ (by rw [G_val]; omega)), hτ4, kPart_other τ3 v _ (by rw [G_val]; omega)]; exact g3 i
  · exact q52
  · rw [k5 q (nK q hq1), hτ4, kPart_other τ3 v q (by omega)]; exact low3 q hq2
  · rw [st5, hτ4, kPart_st, st3, st2, s1]
  · rw [sh5, hτ4, kPart_sh, sh3, sh2, sh1 s hs]
  · rw [cl5, hτ4, kPart_cell, cl3, cl2, cl1]
  · unfold numsSCost
    rw [hccs] at c1le
    have := UnaryPow.sq_ge cap
    omega

end NearCubicWires.WireExponent3_5.PrimT.C4Set
