import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF3

/-! # THR decode front, assembly part 4: the front machine and its run

**`frontM`** = `W1` compiled ; `branchM (rRadK ≠ 0)` (the two docks, else nothing) ; `W2 = ifr rRadK pbPostW skip`
compiled. The register programs run at a VIRTUAL capacity `c₀` (the front's quasi-bounded need, independent of the
unit `j`) and are lifted to the unit's capacity `cap ≥ c₀` (`capUp'`); the docks run at `cap`. So the front's cost
bound does not depend on `j` (only the capacity grows with `j`, `ThrDecFront.run`).

* `W2`, `frontM`, `idle_step'`, `bit_regT`; **`front_run`**: the three outcomes of `ThrDec.ThrDecOut` at the
  front's values (FILTER: `FsIn2`; RADIX: `RsIn4` at the scan's item `t`; the rest: `IdleAt`).

Paper quantity of the main type: the THR tape's unit `j` and its row's setup entry (P3:3011-3016, 2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.UnionMachine.ThrDec
open NearCubicWires.WireExponent3_5.PrimThrW.Joins NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

theorem idle_step' {t : ℕ} (H : Fin t → ℕ) (A : Fin t → List Bool) : Step (Block.idle t) 0 H A H A := by
  obtain ⟨r, hr, hf, hs⟩ := (Timed.refl (Block.idle t) ⟨(Block.idle t).start, H, A⟩).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], hs.le⟩

theorem bit_regT (cap x : ℕ) (σ : WState (LNS x) LNR) (r : Fin LNR) :
    readTapeBit ((wenc cap σ).A (rTape r)) ((wenc cap σ).H (rTape r)) = decide (σ.val r ≠ 0) := by
  rw [wenc_A_r, wenc_H_r, regTape_read]

section F4
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (x : ℕ)

/-- The register program after the docks. -/
def W2 : WM (LNS x) LNR := .ifr rRadK (pbPostW x) .skip

/-- **The THR decode front's machine.** -/
noncomputable def frontM (hx : dX T N ≤ x) (cr fe : ℕ) :=
  Composition.machine (Composition.machine (W1 T N x hx cr fe).toProg.compile
    (Block.branchM (rTape (ns := LNS x) (nr := LNR) rRadK) (docksMT T N x hx) (Block.idle (LNS x + 2 + LNR))))
    (W2 x).toProg.compile

/-- The post-dock program's cost bound (`pbPost_run`). -/
def postCost (cap Llen uLen : ℕ) : ℕ :=
  UnaryPow.sq cap + 1 + (3 + 1 + ((Llen + 1) * (10 * UnaryPow.sq cap) + 1 + (5 * uLen + 1))) + 1 +
    (64 * (3 * cap + 2) + 1 + 58 * UnaryPow.sq cap) + 1 + (40 * (3 * cap + 2) + 1 + (UnaryPow.sq cap + 1 +
    (18 * (UnaryPow.sq cap + 1) + 1 + UnaryPow.sq cap) + 1 + (5 * cap + 1)))

/-- **The front's run** from the unit's fresh cell: the register programs at the virtual capacity `c₀`, the docks at
the unit's capacity `cap ≥ c₀`. -/
theorem front_run (hx : dX T N ≤ x) (cr fe cap c₀ : ℕ) (hc₀ : c₀ ≤ cap) (P : Shared.StarParams)
    (hrP : P.r = Ledger.rowBr cr P.n) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (cc : List ℕ)
    (tl : List Bool) (Kb : ℕ) (hKb : ∀ c ∈ ReqBridge.thrCodes Cs, natBitLength c ≤ Kb) (out : List Bool) (j : ℕ)
    (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2) (h0v : hs.getD 0 0 = xs.length)
    (hcc : cc.length = xs.length) (FP : GapParams) (hPc : FP.cap = hs.getD 1 0)
    (hPl : FP.len = 2 * (P.n + 1) ^ 26) (hPe : FP.errExp = fe * Nat.clog 2 (P.n + 2)) (hPc1 : 1 ≤ FP.cap)
    (hF : FNeed N c₀ (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) P.n (ReqBridge.thrCodes Cs) cc Kb cr fe hs xs
      tg FP (P.s * (P.r / 2)) (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut))
    (hLs : (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut).sum = hs.getD 6 0)
    (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
    (rq : ℕ → ℕ → ℕ → List Bool) :
    ∃ σD m, Step (frontM T N x hx cr fe) m
        (wenc cap (CellLoopD.blankCellD x (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) out j
          (Data.unaryList (hs ++ (xs ++ [tg]))))).H
        (wenc cap (CellLoopD.blankCellD x (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) out j
          (Data.unaryList (hs ++ (xs ++ [tg]))))).A (wenc cap σD).H (wenc cap σD).A ∧
      m ≤ W1Cost P.n (ReqBridge.thrCodes Cs).length cc.length Kb cr fe c₀
          (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2))
          (tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 1 0)
          (hs.getD 0 0) N.Dn + 1 +
        (T.cost (tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n (hs.getD 1 0) N.Cn N.Dn) + 1 +
          N.cost (P.n + tV (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl).length P.n (hs.getD 1 0) N.Cn N.Dn +
            hs.getD 1 0) + 2) + 1 +
        (postCost c₀ (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut).length
          (Data.unaryList (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut)).length + 1) ∧
      σD.st (sk x 0) = frame (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) ∧ σD.sh (sk x 0) = 0 ∧
      σD.st (sk x 2) = List.replicate j true ∧ σD.sh (sk x 2) = 0 ∧
      (IsReqU (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2))
          xs.length j → rowOfU xs.length j < xs.length → σD.val rRadK = 0 ∧ σD.val rFltK ≠ 0 ∧
        FsIn2 x σD (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) out j (Data.unaryList (hs ++ (xs ++ [tg])))
          FP.len FP.cap FP.errExp (j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) / hs.getD 6 0 / hs.getD 2 0)
          (2 * (2 * (j / thrEU xs.length % 2 ^ (2 * (P.s * (P.r / 2))))))
          (2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0)
          (fbOff (rowOfU xs.length j) (xs.getD 0 0)) (fbL (rowOfU xs.length j) (xs.getD 0 0) (xs.getD 1 0))) ∧
      (IsReqU (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2))
          xs.length j → rowOfU xs.length j = xs.length → σD.val rRadK ≠ 0 ∧ σD.val rFltK = 0 ∧
        ∃ t, t < (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut).length ∧
          ((primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut).take t).sum ≤
            j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) % hs.getD 6 0 ∧
          j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) % hs.getD 6 0 <
            ((primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut).take (t + 1)).sum ∧
          RsIn4 x σD (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) out j (Data.unaryList (hs ++ (xs ++ [tg])))
            (![j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) / hs.getD 6 0 % hs.getD 2 0,
              (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut).getD t 0,
              j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) % hs.getD 6 0 -
                ((primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut).take t).sum,
              j / thrEU xs.length % 2 ^ (2 * (P.s * (P.r / 2))),
              2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0, 2 * (xs.getD 0 0 + xs.getD 1 0), P.n, hs.getD 2 0,
              hs.getD 3 0, hs.getD 4 0, hs.getD 5 0, hs.getD 6 0, hs.getD 7 0, hs.getD 8 0, hs.getD 9 0,
              hs.getD 10 0, hs.getD 11 0, hs.getD 12 0, hs.getD 14 0, hs.getD 15 0] : Fin 20 → ℕ)
            (Data.unaryList (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut))
            (winRecs (thrMP (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).M
              (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).A (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).Bs
              (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).den))
            (frame (SignedSortKey.binary (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).ell0
              (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).pMod)) xs.length (hs.getD 1 0)
            (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else [])
            (ReqBridge.thrCodes Cs).length) ∧
      (¬ IsReqU (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2))
          xs.length j →
        IdleAt x σD (Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl) out (unitE (2 ^ FP.seedBits * hs.getD 2 0 *
          hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2)) (xs.length + 1) 0 rq j) j) := by
  set w := Data.reqW P.n true (ReqBridge.thrCodes Cs) cc tl with hw
  set TOT := 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2)
    with hTOT
  obtain ⟨τ1, c1, e1, c1le, s0, h0, s2, h2, hFo, hPo, hIo⟩ := W1_run T N c₀ x hx cr fe P hrP w out j
    (ReqBridge.thrCodes Cs) cc tl Kb hw hKb hs xs tg hhs hxs h0v hcc FP hPc hPl hPe hPc1
    (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut) hF rq
  have c1le' : c1 ≤ W1Cost P.n (ReqBridge.thrCodes Cs).length cc.length Kb cr fe c₀ TOT
      (tV w.length P.n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 1 0) (hs.getD 0 0) N.Dn := c1le
  have st1 := (WExec.exec cap (capUp' hc₀ e1)).step
  by_cases hR : τ1.val rRadK = 0
  · -- no RADIX unit: nothing docked, nothing after
    have sb := Block.branch_false (rTape (ns := LNS x) (nr := LNR) rRadK) (docksMT T N x hx)
      (idle_step' (wenc cap τ1).H (wenc cap τ1).A) (by rw [bit_regT]; simp [hR])
    have e2 : WExec cap (W2 x) τ1 τ1 1 := WExec.ifrF hR (WExec.skip τ1)
    have st2 := (WExec.exec cap e2).step
    refine ⟨τ1, _, Step.seq (Step.seq st1 sb) st2, ?_, s0, h0, s2, h2, hFo, fun hq hr => ?_, hIo⟩
    · unfold postCost; omega
    · exact absurd (hPo hq hr).vR (by rw [hR]; omega)
  · -- a RADIX unit
    have hq : IsReqU TOT xs.length j := by
      by_contra hq; exact hR (hIo hq).1
    have hr : rowOfU xs.length j = xs.length := by
      have := rowOfU_le TOT xs.length j hq
      by_contra hne; exact hR (hFo hq (by omega)).1
    have hPre := hPo hq hr
    obtain ⟨-, hpS, -⟩ := pos_factors _ _ _ _ _ (show 0 < TOT by have := hq.1; omega)
    have hidx : j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) % hs.getD 6 0 <
        (primesList (thrNumVals P Cs alg Dexp xs.length (hs.getD 1 0)).cut).sum := by
      rw [hLs]; exact Nat.mod_lt _ hpS
    have hk : cc.length ≤ 2 := by omega
    have hcapT : 1 ≤ hs.getD 1 0 := by rw [← hPc]; exact hPc1
    obtain ⟨τD, τ, c, t, sD, eP, cle, vD, tlt, tle, tlt2, r1, r2, hRs⟩ := rad_cont T N c₀ cap x hx τ1 P Cs cc tl out j hs
      xs tg P.n (ReqBridge.thrCodes Cs).length (j / thrEU xs.length % 2 ^ (2 * (P.s * (P.r / 2))))
      (j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) / hs.getD 6 0 % hs.getD 2 0)
      (j / thrEU xs.length / 2 ^ (2 * (P.s * (P.r / 2))) % hs.getD 6 0)
      (tV w.length P.n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 1 0) hPre hhs hxs h0v hn ha hd hcapT
      (tf2ok_tV Cs cc tl ha hk (hs.getD 1 0) N.Cn N.Dn) (need_le_tV N w.length P.n (hs.getD 1 0)) hidx
      (by have := hF.post; omega) hF.pool hF.pos
    have sb := Block.branch_true (rTape (ns := LNS x) (nr := LNR) rRadK) (Block.idle (LNS x + 2 + LNR)) sD
      (by rw [bit_regT]; simp [hR])
    have hRD : τD.val rRadK ≠ 0 := by rw [vD]; exact hR
    have e2 : WExec cap (W2 x) τD τ (c + 1) := WExec.ifrT hRD (capUp' hc₀ eP)
    have st2 := (WExec.exec cap e2).step
    refine ⟨τ, _, Step.seq (Step.seq st1 sb) st2, ?_, hRs.s0, hRs.h0, hRs.s2, hRs.h2, fun _ h => absurd hr (by omega),
      fun _ _ => ⟨r1, r2, t, tlt, tle, tlt2, hRs⟩, fun h => absurd hq h⟩
    unfold postCost; omega

end F4

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
