import Proof.Wire_3_5.Primitive.Writers.PopSetupRun
import Proof.Wire_3_5.Primitive.Writers.PopSetupNeed

/-! # PA POP setup, part 5b: the POP-ready state and the machine, to `PopSetupSpecB2`

"`P'^{(s)}_{Z} = Maj_t(P^{(1)}_{s}, …, P^{(t)}_{s})` [...] the zero coordinate repaired" (list:flatten, P3:1491-1498,
1505-1520): from the POP setup's entry bank (`PopSetup.PopIn`: the flat list's `M, B, errExp`, the list seed's index
`f`, the sign, the target `s`, the slice `r4, G, off, L`), the setup program `PopSetupRun.popProg` computes the flat
list's numbers and writes the walk bank's inputs at the list seed and C5's builder entry state, and raises the POP flag:
a POP-ready unit state (`UnitReady.PopReady`) at the list seed `(flatSeedEquiv Pl).symm f`, at every capacity above
`PopSetupMath.popNeed` (all the POP row's capacities, `PopSetupNeed`), within `popCost cap = O(cap³)`.

* **`pop_run`**: the whole program's run and every fact of the state `PopReady` reads;
* **`pop_ready`**: `PopSetupSpec.run`'s conclusion;
* **`popSetupSpecB2 W : PopSetupSpecB2 W`** (the consumer: the SYM leaf `SymLeaf.symLeaf2`), with `need_le` at
  `K_n = 2^800`, `D_n = 40` (`popNeed_le`) and `bound_le` at `K_b = 10^6`, `D_b = 3`.

Paper quantity of the main type: the POP-ready unit state of the flat list's row `[report = s]` at the call's list seed
(list:flatten P3:1491-1498, row:sym P3:2477-2496). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopSetupReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetupRun NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.ExtDecompositionBatch

variable (cap : ℕ)

/-! ## The whole run -/

theorem pop_run (x : ℕ) (σ : WState (LNS x) LNR) (w out u : List Bool) (j M B err f sg s r4 G off L : ℕ)
    (hin : PopSetup.PopIn x σ w out j u M B err f sg s r4 G off L) (hc1 : 1 ≤ cap)
    (hN : runNeed M B err f sg s r4 G off L ≤ cap) :
    ∃ τ : WState (LNS x) LNR, WExec cap (popProg x) σ τ (PopSetupRun.popCost cap) ∧ τ.cell = σ.cell ∧ τ.sh = σ.sh ∧
      (∀ i, i ∉ PopSetupWords.pwOut x → τ.st i = σ.st i) ∧
      τ.st (sk x 25) = List.replicate (pSb M B) true ∧ τ.st (sk x 26) = List.replicate (pN err) true ∧
      τ.st (sk x 27) = List.replicate (pSb M B + pSb M B + 1) true ∧
      τ.st (sk x 28) = List.replicate (pSb M B + pSb M B + 1) true ∧
      τ.st (sk x 24) = frame (binary (pWid M B err) f) ∧
      τ.st (sk x 8) = frame (binary (pRk M B + pRk M B + pRk M B - 1) 0) ∧
      τ.st (sk x 14) = frame (binary (pRk M B) 0) ∧ τ.st (sk x 15) = frame (binary (pRk M B) 0) ∧
      τ.st (sk x 16) = frame (binary (pRk M B + pRk M B - 1) 0) ∧
      τ.st (sk x 9) = List.replicate (pJ B + 1) true ++ [false] ∧ τ.st (sk x 150) = [true] ∧
      τ.val 6 = pSb M B ∧ τ.val 7 = pRk M B ∧ τ.val 8 = pRk M B - 1 ∧ τ.val 10 = L ∧ τ.val 15 = pPad M B ∧
      τ.val 20 = r4 ∧ τ.val 21 = G ∧ τ.val 22 = off ∧ τ.val 23 = L ∧ τ.val 39 = pS B ∧ τ.val 40 = pJ B ∧
      τ.val 63 = M ∧ τ.val 64 = L ∧ τ.val 69 = sg ∧ τ.val 71 = pN err + 1 ∧ τ.val 72 = err / 4 + 1 ∧
      τ.val 82 = s ∧ τ.val 199 = pMl r4 G off L ∧
      (∀ r : Fin LNR, r.val < 250 → r ∉ lowOut → τ.val r = 0) := by
  have hcB : Nat.clog 2 B ≤ B := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hcM : Nat.clog 2 M ≤ M := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hmx : max (Nat.clog 2 B + 9) (Nat.clog 2 M) ≤ B + M + 9 := max_le (by omega) (by omega)
  obtain ⟨τA, eA, stA, shA, ceA, oA, a441, a442, a443, a444, a446, a447, a448, a449, a458, a459, a460, a461, a462,
    a463, a465⟩ := runA cap σ M B err f sg s r4 G off L hin.vM hin.vB hin.vErr hin.vSeed hin.vSgn hin.vS hin.vR4 hin.vG
      hin.vOff hin.vL hin.zHigh hc1 hN
  obtain ⟨τB, eB, stB, shB, ceB, oB, b6, b7, b8, b10, b15, b20, b21, b22, b23, b39, b40, b63, b64, b69, b71, b72, b82,
    b199⟩ := runB cap τA M B err sg s r4 G off L
      (by rw [oA _ (by decide)]; exact hin.vM) (by rw [oA _ (by decide)]; exact hin.vSgn)
      (by rw [oA _ (by decide)]; exact hin.vS) (by rw [oA _ (by decide)]; exact hin.vR4)
      (by rw [oA _ (by decide)]; exact hin.vG) (by rw [oA _ (by decide)]; exact hin.vOff)
      (by rw [oA _ (by decide)]; exact hin.vL) a442 a443 a444 a446 a447 a448 a460 a463 a465
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zLow _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide)) (by rw [oA _ (by decide)]; exact hin.zHigh _ (by decide))
      hc1 (by unfold runNeed at hN ⊢; omega)
  have hcapW : pSb M B + pN err + (pSb M B + pSb M B + 1) + f + 2 * pWid M B err +
      2 * (pRk M B + pRk M B + pRk M B - 1) + 2 * pRk M B + 2 * (pRk M B + pRk M B - 1) + (pJ B + 1) + 1000 ≤ cap := by
    simp only [pWid, pSb, pRk, pJ, pN]
    unfold runNeed at hN
    omega
  obtain ⟨τW, eW, vvW, shW, ceW, ostW, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ :=
    PopSetupWords.pwords_spec cap x τB (pSb M B) (pN err) (pSb M B + pSb M B + 1) f (pWid M B err)
      (pRk M B + pRk M B + pRk M B - 1) (pRk M B) (pRk M B + pRk M B - 1) (pJ B + 1)
      (by rw [oB _ (by decide)]; exact a447) (by rw [oB _ (by decide)]; exact a441)
      (by rw [oB _ (by decide)]; exact a459) (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.vSeed)
      (by rw [oB _ (by decide)]; exact a461) (by rw [oB _ (by decide)]; exact a449)
      (by rw [oB _ (by decide)]; exact a446) (by rw [oB _ (by decide)]; exact a458)
      (by rw [oB _ (by decide)]; exact a462)
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (by rw [oB _ (by decide), oA _ (by decide)]; exact hin.zHigh _ (by decide))
      (fun q h0 h1 h2 h3 => by rw [stB, stA, shB, shA]; exact hin.blank q h0 h1 h2 h3) hcapW
  have nA : ∀ q ∈ outA, 250 ≤ q.val := by decide
  have nB : ∀ q ∈ outB, q ∈ lowOut ∨ 250 ≤ q.val := by decide
  refine ⟨τW, WExec.mono (WExec.seq eA (WExec.seq eB eW)) (by unfold PopSetupRun.popCost; omega), by rw [ceW, ceB, ceA],
    by rw [shW, shB, shA], fun i hi => by rw [ostW i hi, stB, stA], w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10,
    by rw [vvW]; exact b6, by rw [vvW]; exact b7, by rw [vvW]; exact b8, by rw [vvW]; exact b10,
    by rw [vvW]; exact b15, by rw [vvW]; exact b20, by rw [vvW]; exact b21, by rw [vvW]; exact b22,
    by rw [vvW]; exact b23, by rw [vvW]; exact b39, by rw [vvW]; exact b40, by rw [vvW]; exact b63,
    by rw [vvW]; exact b64, by rw [vvW]; exact b69, by rw [vvW]; exact b71, by rw [vvW]; exact b72,
    by rw [vvW]; exact b82, by rw [vvW]; exact b199, ?_⟩
  intro r hr hno
  have r1 : r ∉ outA := fun h => by have := nA r h; omega
  have r2 : r ∉ outB := fun h => by rcases nB r h with h' | h'; exact hno h'; omega
  rw [vvW, oB r r2, oA r r1]
  exact hin.zLow r hr

/-! ## C5's builder entry state at the zero seed word -/

theorem binary_zero' : ∀ b : ℕ, binary b 0 = List.replicate b false
  | 0 => rfl
  | b + 1 => by simp [binary, binary_zero' b, List.replicate_succ]

section YC
variable (Pl : FlatListParams) (e : Pl.FlatSeed) (L R LW : ℕ)

theorem yC_st1 : (PopPipe.yC Pl e L R LW).st 1 = [] := rfl
theorem yC_st3 : (PopPipe.yC Pl e L R LW).st 3 =
    frameP (List.replicate (2 * sideB Pl.base.rank - padB Pl.base.rank) false) ++ [false] := rfl
theorem yC_st4 : (PopPipe.yC Pl e L R LW).st 4 = List.replicate (Pl.base.J + 1) true ++ [false] := rfl
theorem yC_st5 : (PopPipe.yC Pl e L R LW).st 5 = [] := rfl
theorem yC_st6 : (PopPipe.yC Pl e L R LW).st 6 = [] := rfl
theorem yC_st7 : (PopPipe.yC Pl e L R LW).st 7 = [] := rfl
theorem yC_st8 : (PopPipe.yC Pl e L R LW).st 8 = [] := rfl
theorem yC_st9 : (PopPipe.yC Pl e L R LW).st 9 = frame (binary Pl.base.rank 0) := rfl
theorem yC_st10 : (PopPipe.yC Pl e L R LW).st 10 =
    frameP (bwOfSw Pl.base.rank (List.replicate (2 * sideB Pl.base.rank - padB Pl.base.rank) false)) ++ [false] := rfl
theorem yC_st11 : (PopPipe.yC Pl e L R LW).st 11 =
    frameP (epOfSw Pl.base.rank (List.replicate (2 * sideB Pl.base.rank - padB Pl.base.rank) false)) ++ [false] := rfl
theorem yC_val : (PopPipe.yC Pl e L R LW).val =
    ![0, 0, 0, 0, 0, 0, sideB Pl.base.rank, Pl.base.rank, Pl.base.rank - 1, 0, L, 0, 0, 0, 0, padB Pl.base.rank, 0, 0,
      0] := rfl

end YC

theorem sb_eq (r : ℕ) (hr : 1 ≤ r) : (r + r + r) / 2 = sideB r := by
  unfold sideB SupplierWalkBridge.toeplitzWalkSideBits SupplierWalkBridge.toeplitzSeedBits; omega

theorem pad_eq (r : ℕ) (hr : 1 ≤ r) : (r + r + r) / 2 + (r + r + r) / 2 - (r + r + r - 1) = padB r := by
  unfold padB sideB SupplierWalkBridge.toeplitzWalkSideBits SupplierWalkBridge.toeplitzSeedBits; omega

theorem pmw_len (r : ℕ) (hr : 1 ≤ r) : 2 * sideB r - padB r = r + r + r - 1 := by
  unfold padB sideB SupplierWalkBridge.toeplitzWalkSideBits SupplierWalkBridge.toeplitzSeedBits; omega

theorem bw_zero (r : ℕ) (hr : 1 ≤ r) : bwOfSw r (List.replicate (r + r + r - 1) false) = List.replicate r false := by
  unfold bwOfSw
  rw [List.drop_replicate, List.take_replicate]
  congr 1
  omega

theorem ep_zero (r : ℕ) (hr : 1 ≤ r) :
    epOfSw r (List.replicate (r + r + r - 1) false) = List.replicate (r + r - 1) false := by
  unfold epOfSw
  rw [List.take_replicate, List.drop_replicate, List.take_replicate, List.reverse_replicate, ← List.replicate_add]
  congr 1
  omega

/-! ## The need and the bound -/

theorem runNeed_le (Pl : FlatListParams) (f : ℕ) (hf : f < Fintype.card Pl.FlatSeed) (sg s L r4 G off : ℕ)
    (hsg : sg ≤ 1) (hs : s ≤ Pl.M) :
    runNeed Pl.M Pl.B Pl.errExp f sg s r4 G off L ≤ PopSetupMath.popNeed Pl L r4 G off := by
  have hx2 := PopSetupMath.x_ge Pl L r4 G off
  have hM := PopSetupMath.M_le_x Pl L r4 G off
  have hB := PopSetupMath.B_le_x Pl L r4 G off
  have hE := PopSetupMath.err_le_x Pl L r4 G off
  have hC := PopSetupMath.card_le_x Pl L r4 G off
  have hr := PopSetupMath.r4_le_x Pl L r4 G off
  have hm := PopSetupMath.mlab_le_x Pl L r4 G off
  have hGo := PopSetupMath.G_off_le_x Pl L r4 G off
  have hmG : (r4 + 4) * G ≤ PopSetup.popMlab r4 G off L := by unfold PopSetup.popMlab; omega
  have hU := PopSetupMath.u_ge Pl L r4 G off
  unfold runNeed
  unfold PopSetupMath.popNeed
  unfold PopSetupMath.popU at hU ⊢
  generalize PopSetupMath.popX Pl L r4 G off = X at *
  have h1 : 4096 * Pl.B + 2 ≤ 4097 * X := by omega
  have h2 : (4096 * Pl.B + 2) * (4096 * Pl.B + 2) ≤ (4097 * X) * (4097 * X) := Nat.mul_le_mul h1 h1
  have h3 : 1000000 * (Pl.M + Pl.B + Pl.errExp + f + sg + s + r4 + G + off + L + 10) ≤ 16000000 * X := by omega
  have h4 : 16000000 * X + X + (4097 * X) * (4097 * X) ≤ (2 ^ 20 * X) ^ 2 := by nlinarith
  have h5 : (2 ^ 20 * X) ^ 2 ≤ (2 ^ 20 * X) ^ 40 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem popCost_le (c : ℕ) : PopSetupRun.popCost c ≤ 1000000 * (c + 1) ^ 3 := by
  unfold PopSetupRun.popCost UnaryPow.sq
  have h1 : c + 2 ≤ 2 * (c + 1) := by omega
  have h2 : (c + 2) * (c + 2) ≤ 2 * (c + 1) * (2 * (c + 1)) := Nat.mul_le_mul h1 h1
  have h3 : (c + 2) * (c + 2) * (c + 2) ≤ 2 * (c + 1) * (2 * (c + 1)) * (2 * (c + 1)) := Nat.mul_le_mul h2 h1
  have h4 : (c + 1) * (c + 1) ≤ (c + 1) ^ 3 := by nlinarith
  have h5 : 1 ≤ (c + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have e3 : (c + 1) ^ 3 = (c + 1) * (c + 1) * (c + 1) := by ring
  nlinarith

/-! ## The POP-ready state -/

theorem pwOut_val (x : ℕ) : (PopSetupWords.pwOut x).map Fin.val = [25, 26, 27, 28, 24, 8, 14, 15, 16, 9, 150] := rfl

theorem lowOut_vals : ∀ q ∈ lowOut, q.val = 6 ∨ q.val = 7 ∨ q.val = 8 ∨ q.val = 10 ∨ q.val = 15 ∨ q.val = 20 ∨
    q.val = 21 ∨ q.val = 22 ∨ q.val = 23 ∨ q.val = 39 ∨ q.val = 40 ∨ q.val = 63 ∨ q.val = 64 ∨ q.val = 69 ∨
    q.val = 71 ∨ q.val = 72 ∨ q.val = 82 ∨ q.val = 199 := by decide

/-- **`PopSetupSpec.run`'s conclusion**: the program's run to a POP-ready state at the list seed of index `f`. -/
theorem pop_ready (W : WalkBankProducer) (Pl : FlatListParams) (f : ℕ) (hf : f < Fintype.card Pl.FlatSeed)
    (L r4 G off : ℕ) (sgn : Bool) (s : ℕ) (hs : s < Pl.M + 1) (w out u : List Bool) (j : ℕ)
    (σ : WState (LNS W.x) LNR) (hneed : PopSetupMath.popNeed Pl L r4 G off ≤ cap)
    (hin : PopSetup.PopIn W.x σ w out j u Pl.M Pl.B Pl.errExp f (if sgn then 1 else 0) s r4 G off L) :
    ∃ τ m, WExec cap (popProg W.x) σ τ m ∧ m ≤ PopSetupRun.popCost cap ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧
      τ.st (sk W.x 150) = [true] ∧ τ.sh (sk W.x 150) = 0 ∧
      ∃ hlabs : 4 * L ≤ (Emit.sliceLabs r4 G off L).length,
        UnitReady.PopReady cap W τ out Pl ((PrimAsm.Enum.flatSeedEquiv Pl).symm ⟨f, hf⟩) L r4 G off
          (PopSetup.popMlab r4 G off L) (PopSetup.popLw Pl L) (PopSetup.popCAP r4 G off L) (PopSetup.popLL r4 G off L)
          (PopSetup.popR Pl r4 G off L) (PopSetup.popCp Pl r4 G off L) (PopSetup.popRW Pl) (PopSetup.popRW Pl) sgn
          ⟨s, hs⟩ hlabs := by
  have hsg : (if sgn then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have hN := le_trans (runNeed_le Pl f hf _ s L r4 G off hsg (by omega)) hneed
  have hc1 : 1 ≤ cap := by unfold runNeed at hN; omega
  obtain ⟨τ, hx, hcl, hsh, hfr, w25, w26, w27, w28, w24, w8, w14, w15, w16, w9, w150, v6, v7, v8, v10, v15, v20, v21,
    v22, v23, v39, v40, v63, v64, v69, v71, v72, v82, v199, hlow⟩ :=
      pop_run cap W.x σ w out u j Pl.M Pl.B Pl.errExp f (if sgn then 1 else 0) s r4 G off L hin hc1 hN
  have kept : ∀ k : Fin 161, k.val ∉ [25, 26, 27, 28, 24, 8, 14, 15, 16, 9, 150] →
      τ.st (sk W.x k) = σ.st (sk W.x k) := fun k hk => hfr _ (fun h => hk (by
        have := List.mem_map_of_mem (f := Fin.val) h
        rwa [pwOut_val, sk_val] at this))
  have heads : ∀ i, τ.sh i = σ.sh i := fun i => by rw [hsh]
  have blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 →
      k.val ∉ [25, 26, 27, 28, 24, 8, 14, 15, 16, 9, 150] → τ.st (sk W.x k) = [] ∧ τ.sh (sk W.x k) = 0 :=
    fun k h0 h1 h2 h3 hw => ⟨by rw [kept k hw]; exact (hin.blank k h0 h1 h2 h3).1,
      by rw [heads]; exact (hin.blank k h0 h1 h2 h3).2⟩
  have zh : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → τ.sh (sk W.x k) = 0 :=
    fun k h0 h1 h2 h3 => by rw [heads]; exact (hin.blank k h0 h1 h2 h3).2
  obtain ⟨hpad, hps, hsd, hlb, hnJ⟩ := PopSetupMath.rank_facts Pl
  have hrk : pRk Pl.M Pl.B = Pl.base.rank := rfl
  have hsb : pSb Pl.M Pl.B = sideB Pl.base.rank := sb_eq _ hlb
  have hpb : pPad Pl.M Pl.B = padB Pl.base.rank := pad_eq _ hlb
  have hpm : 2 * sideB Pl.base.rank - padB Pl.base.rank = Pl.base.rank + Pl.base.rank + Pl.base.rank - 1 :=
    pmw_len _ hlb
  set e := (PrimAsm.Enum.flatSeedEquiv Pl).symm ⟨f, hf⟩ with he
  have hidx : seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e =
      binary (160 * (2 * (Pl.errExp / 4)) + 2 * sideB Pl.base.rank) f := by
    unfold seedIndexWord
    have e1 : (SupplierWalkBridge.positiveWalkSampleFinEquiv (2 ^ sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e).val = f := by
      show ((PrimAsm.Enum.flatSeedEquiv Pl) ((PrimAsm.Enum.flatSeedEquiv Pl).symm ⟨f, hf⟩)).val = f
      rw [Equiv.apply_symm_apply]
    rw [e1]
  have hwid : pWid Pl.M Pl.B Pl.errExp = 160 * (2 * (Pl.errExp / 4)) + 2 * sideB Pl.base.rank := by
    unfold pWid pN; rw [hsb]; ring
  have hports : ∀ jj : Fin 14, τ.st (sk W.x (portT jj)) = inPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4))
      (PopSetup.popRW Pl) (PopSetup.popRW Pl) (seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e) jj := by
    intro jj
    fin_cases jj
    all_goals first
      | exact (blank _ (by decide) (by decide) (by decide) (by decide) (by decide)).1
      | skip
    · show τ.st (sk W.x 24) = frame (seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e)
      rw [hidx, w24, hwid]
    · show τ.st (sk W.x 25) = List.replicate (sideB Pl.base.rank) true
      rw [w25, hsb]
    · show τ.st (sk W.x 26) = List.replicate (2 * (Pl.errExp / 4)) true
      rw [w26]; rfl
    · show τ.st (sk W.x 27) = List.replicate (PopSetup.popRW Pl) true
      rw [w27, hsb]; unfold PopSetup.popRW; congr 1; omega
    · show τ.st (sk W.x 28) = List.replicate (PopSetup.popRW Pl) true
      rw [w28, hsb]; unfold PopSetup.popRW; congr 1; omega
  have hh : ∀ jj : Fin 14, τ.sh (sk W.x (portT jj)) = 0 := by
    intro jj
    fin_cases jj <;> exact zh _ (by decide) (by decide) (by decide) (by decide)
  have hC5 : ∀ i : Fin 12, i.val ≠ 0 → i.val ≠ 2 →
      τ.st (fsC W.x i) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st i ∧ τ.sh (fsC W.x i) = 0 := by
    intro i h0 h2
    fin_cases i
    · exact absurd rfl h0
    · refine ⟨?_, zh 6 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 6) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 1
      rw [yC_st1]
      exact (blank 6 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · exact absurd rfl h2
    · refine ⟨?_, zh 8 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 8) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 3
      rw [yC_st3, w8, hrk, hpm, binary_zero', ← frame_eq_frameP]
    · refine ⟨?_, zh 9 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 9) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 4
      rw [yC_st4, w9]; rfl
    · refine ⟨?_, zh 10 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 10) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 5
      rw [yC_st5]
      exact (blank 10 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · refine ⟨?_, zh 11 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 11) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 6
      rw [yC_st6]
      exact (blank 11 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · refine ⟨?_, zh 12 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 12) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 7
      rw [yC_st7]
      exact (blank 12 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · refine ⟨?_, zh 13 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 13) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 8
      rw [yC_st8]
      exact (blank 13 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · refine ⟨?_, zh 14 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 14) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 9
      rw [yC_st9, w14]; rfl
    · refine ⟨?_, zh 15 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 15) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 10
      rw [yC_st10, w15, hrk, hpm, bw_zero _ hlb, binary_zero', ← frame_eq_frameP]
    · refine ⟨?_, zh 16 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 16) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 11
      rw [yC_st11, w16, hrk, hpm, ep_zero _ hlb, binary_zero', ← frame_eq_frameP]
  have hC5r : ∀ r : Fin 19, τ.val (frC r) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).val r := by
    intro r
    rw [yC_val]
    fin_cases r
    all_goals first
      | (rw [hlow _ (by decide) (by decide)]; rfl)
      | skip
    · show τ.val 6 = sideB Pl.base.rank; rw [v6, hsb]
    · show τ.val 7 = Pl.base.rank; rw [v7]; rfl
    · show τ.val 8 = Pl.base.rank - 1; rw [v8]; rfl
    · show τ.val 10 = L; rw [v10]
    · show τ.val 15 = padB Pl.base.rank; rw [v15, hpb]
  have hscr : ∀ jj : Fin (IPL (negFam F35).t + 1), jj.val ≠ 0 → jj.val ≠ 45 →
      τ.st (PopPipe.tmapQ W.x jj) = [] ∧ τ.sh (PopPipe.tmapQ W.x jj) = 0 := by
    intro jj h0 h45
    have hj : jj.val < 48 := PopPipe.IPL1 ▸ jj.isLt
    have hv := PopPipe.portP_cast_val jj h0 h45
    have e2 : PopPipe.tmapQ W.x jj = sk W.x ⟨29 + jj.val, by omega⟩ := by
      apply Fin.ext
      show (portP (Fin.cast PopPipe.IPL1 jj)).val = 29 + jj.val
      exact hv
    rw [e2]
    refine blank _ (by show 29 + jj.val ≠ 0; omega) (by show 29 + jj.val ≠ 1; omega) (by show 29 + jj.val ≠ 2; omega)
      (by show 29 + jj.val ≠ 113; omega) ?_
    show 29 + jj.val ∉ [25, 26, 27, 28, 24, 8, 14, 15, 16, 9, 150]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hlen := PopSetupMath.sliceLabs_length r4 G off L
  have hlabs : 4 * L ≤ (Emit.sliceLabs r4 G off L).length := le_of_eq hlen.symm
  have hcf := PopSetupNeed.popCapFacts Pl L r4 G off cap hneed
  refine ⟨τ, PopSetupRun.popCost cap, hx, le_rfl, ?_, ?_, ?_, w150, zh 150 (by decide) (by decide) (by decide) (by decide),
    hlabs, ?_⟩
  · rw [kept 0 (by decide)]; exact hin.s0
  · rw [kept 2 (by decide)]; exact hin.s2
  · rw [heads]; exact hin.h2
  exact {
    hlen := hlen
    hnest := fun h jj i hi => Pl.base.inLevel_nest h jj i hi
    hlw := rfl
    hCAP := rfl
    hLL := rfl
    hR := rfl
    hcp := rfl
    hok := PopSetupMath.pop_hok Pl e L r4 G off sgn ⟨s, hs⟩ hlabs
    hRW := le_rfl
    hLW := le_rfl
    hpad := hpad
    hps := hps
    hsd := hsd
    hlb := hlb
    hnJ := hnJ
    hcapC := hcf.hcapC
    hO := hcf.hO
    hout := by rw [kept 1 (by decide)]; exact hin.s1
    houth := by rw [heads]; exact hin.h1
    hrec := (blank 3 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    hrec0 := zh 3 (by decide) (by decide) (by decide) (by decide)
    hD := by
      rw [(blank 4 (by decide) (by decide) (by decide) (by decide) (by decide)).1,
        zh 4 (by decide) (by decide) (by decide) (by decide)]
      rfl
    hin := hports
    hh := hh
    hsc := fun k => by
      rw [hfr _ (fun h => by
        have := List.mem_map_of_mem (f := Fin.val) h
        rw [pwOut_val, sT_val] at this
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        omega)]
      exact (hin.blankT k).1
    hsh := fun k => by rw [heads]; exact (hin.blankT k).2
    hC5 := hC5
    hC5r := hC5r
    hcell := by rw [hcl, hin.cell]; rfl
    hscr := hscr
    h0 := hlow _ (by decide) (by decide)
    h1 := by rw [show PopCellW.Xe Pe 1 = (20 : Fin LNR) from Fin.ext rfl]; exact v20
    h2 := by rw [show PopCellW.Xe Pe 2 = (21 : Fin LNR) from Fin.ext rfl]; exact v21
    h3 := by rw [show PopCellW.Xe Pe 3 = (22 : Fin LNR) from Fin.ext rfl]; exact v22
    h4 := by rw [show PopCellW.Xe Pe 4 = (23 : Fin LNR) from Fin.ext rfl]; exact v23
    h20 := by
      rw [show PopCellW.Xe Pe 20 = (39 : Fin LNR) from Fin.ext rfl, v39]
      unfold pS
      norm_num
      rfl
    h21 := by rw [show PopCellW.Xe Pe 21 = (40 : Fin LNR) from Fin.ext rfl, v40]; rfl
    h44 := by rw [show PopCellW.Xe Pe 44 = (63 : Fin LNR) from Fin.ext rfl]; exact v63
    h45 := by rw [show PopCellW.Xe Pe 45 = (64 : Fin LNR) from Fin.ext rfl]; exact v64
    h50 := by rw [show PopCellW.Xe Pe 50 = (69 : Fin LNR) from Fin.ext rfl]; exact v69
    h52 := by rw [show PopCellW.Xe Pe 52 = (71 : Fin LNR) from Fin.ext rfl, v71]; rfl
    h53 := by
      rw [show PopCellW.Xe Pe 53 = (72 : Fin LNR) from Fin.ext rfl, v72]
      unfold SupplierWalk.majorityThreshold FlatListParams.walkLen
      omega
    h63 := by rw [show PopCellW.Xe Pe 63 = (82 : Fin LNR) from Fin.ext rfl]; exact v82
    hzA := by
      intro k hk
      refine hlow _ (by show 19 + k.val < 250; omega) (fun h => ?_)
      have := lowOut_vals _ h
      have e3 : (PopCellW.Xe Pe k).val = 19 + k.val := rfl
      rw [e3] at this
      omega
    hz := by
      intro jj h64 h170
      refine hlow _ (by rw [Pe_val]; omega) (fun h => ?_)
      have := lowOut_vals _ h
      rw [Pe_val] at this
      omega
    h180 := by rw [show Pe 180 = (199 : Fin LNR) from Fin.ext rfl]; exact v199
    hM := le_rfl
    hcap := hcf.hcap
    hdc := hcf.hdc
    hJc := hcf.hJc
    hSc := hcf.hSc
    hlwc := hcf.hlwc
    hMc := hcf.hMc
    hcL := hcf.hcL
    hcap3 := hcf.hcap3
    hac3 := hcf.hac3
    hQc := hcf.hQc
    hc4 := hcf.hc4
    hin2 := hcf.hin2
    hnum := PopSetupNeed.popHnum Pl L r4 G off cap hneed
    h2c := hcf.h2c
    hcV := hcf.hcV
    hcT := hcf.hcT
    hθc := hcf.hθc
    hRc1 := hcf.hRc1
    hcpc := hcf.hcpc
    hbig := PopSetupNeed.popHbig Pl L r4 G off cap hneed e sgn ⟨s, hs⟩ hlabs }

/-! ## The machine -/

/-- **The POP setup, to `PopSetupSpecB2`**: the program `popProg`, the need `popNeed = (2^20·popX)^40`, the bound
`popCost` (`O(cap³)`). -/
noncomputable def popSetupSpecB2 (W : WalkBankProducer) : PopSetup.PopSetupSpecB2 W where
  prog := popProg W.x
  need := PopSetupMath.popNeed
  bound := PopSetupRun.popCost
  run := fun cap Pl f hf L r4 G off sgn s hs w out u j σ hneed hin =>
    pop_ready cap W Pl f hf L r4 G off sgn s hs w out u j σ hneed hin
  Kn := 2 ^ 800
  Dn := 40
  need_le := fun Pl L r4 G off => PopSetupMath.popNeed_le Pl L r4 G off
  Kb := 1000000
  Db := 3
  bound_le := popCost_le

end NearCubicWires.WireExponent3_5.PrimAsm.PopSetupReady
