import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF1

/-! # THR decode front, assembly part 2: the RADIX continuation (the docks, then the post-dock program)

From the RADIX pre-dock outcome (`PreOK`): the two docks (`docksT_run`, `TF2Ok` at `tV` and W6's need) reach W6's
words and the payloads; with the decoded registers kept that is the post-dock entry **`PostIn`**, and the post-dock
program (`pbPost_run`) reaches `RsIn4`. **`rad_cont`**.

Paper quantity of the main type: the RADIX row's setup entry (P3:2585-2623). -/

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
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.UnionMachine.ThrDec NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

section F2
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (cap capR : ℕ) (x : ℕ)

/-- **The RADIX continuation**: the docks (at any capacity `capR`), then the post-dock program (at `cap`). -/
theorem rad_cont (hx : dX T N ≤ x) (τP : WState (LNS x) LNR) (P : Shared.StarParams) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (codes : List ℕ) (tl : List Bool) (out : List Bool)
    (j : ℕ) (hs xs : List ℕ) (tg n a row gi idx V capT : ℕ)
    (hPre : PreOK T N cap x hx τP (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) out j hs xs tg n a row gi idx V
      capT)
    (hhs : hs.length = 16) (hxs : xs.length ≤ 2) (h0v : hs.getD 0 0 = xs.length)
    (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hcap : 1 ≤ capT)
    (hok : PrimThrW.TopFront2.TF2Ok Cs codes V) (hneed : N.need (P.n + capT) ≤ V)
    (hidx : idx < (primesList (thrNumVals P Cs alg Dexp xs.length capT).cut).sum)
    (hLc : (Data.unaryList (primesList (thrNumVals P Cs alg Dexp xs.length capT).cut)).length + idx + 2 ≤ cap)
    (cPool : 2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0 ≤ cap)
    (cPos : hs.sum + (xs.getD 0 0 + xs.getD 1 0) + 16 + xs.length ≤ cap) :
    ∃ τD τ c t, Step (docksMT T N x hx) (T.cost V + 1 + N.cost (P.n + V + capT)) (wenc capR τP).H (wenc capR τP).A
        (wenc capR τD).H (wenc capR τD).A ∧ WExec cap (pbPostW x) τD τ c ∧
      c ≤ UnaryPow.sq cap + 1 + (3 + 1 + (((primesList (thrNumVals P Cs alg Dexp xs.length capT).cut).length + 1) *
        (10 * UnaryPow.sq cap) + 1 + (5 * (Data.unaryList (primesList (thrNumVals P Cs alg Dexp xs.length
        capT).cut)).length + 1))) + 1 + (64 * (3 * cap + 2) + 1 + 58 * UnaryPow.sq cap) + 1 +
        (40 * (3 * cap + 2) + 1 + (UnaryPow.sq cap + 1 + (18 * (UnaryPow.sq cap + 1) + 1 + UnaryPow.sq cap) + 1 +
        (5 * cap + 1))) ∧
      τD.val = τP.val ∧
      t < (primesList (thrNumVals P Cs alg Dexp xs.length capT).cut).length ∧
      ((primesList (thrNumVals P Cs alg Dexp xs.length capT).cut).take t).sum ≤ idx ∧
      idx < ((primesList (thrNumVals P Cs alg Dexp xs.length capT).cut).take (t + 1)).sum ∧
      τ.val rRadK ≠ 0 ∧ τ.val rFltK = 0 ∧
      RsIn4 x τ (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) out j (Data.unaryList (hs ++ (xs ++ [tg])))
        (![gi, (primesList (thrNumVals P Cs alg Dexp xs.length capT).cut).getD t 0,
          idx - ((primesList (thrNumVals P Cs alg Dexp xs.length capT).cut).take t).sum, row,
          2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0, 2 * (xs.getD 0 0 + xs.getD 1 0), n, hs.getD 2 0,
          hs.getD 3 0, hs.getD 4 0, hs.getD 5 0, hs.getD 6 0, hs.getD 7 0, hs.getD 8 0, hs.getD 9 0, hs.getD 10 0,
          hs.getD 11 0, hs.getD 12 0, hs.getD 14 0, hs.getD 15 0] : Fin 20 → ℕ)
        (Data.unaryList (primesList (thrNumVals P Cs alg Dexp xs.length capT).cut))
        (winRecs (thrMP (thrNumVals P Cs alg Dexp xs.length capT).M (thrNumVals P Cs alg Dexp xs.length capT).A
          (thrNumVals P Cs alg Dexp xs.length capT).Bs (thrNumVals P Cs alg Dexp xs.length capT).den))
        (frame (SignedSortKey.binary (thrNumVals P Cs alg Dexp xs.length capT).ell0
          (thrNumVals P Cs alg Dexp xs.length capT).pMod)) xs.length (hs.getD 1 0)
        (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else []) a := by
  obtain ⟨τD, sD, hDO⟩ := docksT_run T N capR x hx τP P Cs codes tl V xs.length capT hPre.dock hn ha hd hxs hcap hok
    hneed
  have oth : ∀ k : Fin 161, k.val ≠ 0 → (k.val < 130 ∨ 136 < k.val) →
      τD.st (sk x k) = τP.st (sk x k) ∧ τD.sh (sk x k) = τP.sh (sk x k) := hDO.other
  have hPI : PostIn cap x τD (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) out j hs xs tg
      (primesList (thrNumVals P Cs alg Dexp xs.length capT).cut)
      (winRecs (thrMP (thrNumVals P Cs alg Dexp xs.length capT).M (thrNumVals P Cs alg Dexp xs.length capT).A
        (thrNumVals P Cs alg Dexp xs.length capT).Bs (thrNumVals P Cs alg Dexp xs.length capT).den))
      (frame (SignedSortKey.binary (thrNumVals P Cs alg Dexp xs.length capT).ell0
        (thrNumVals P Cs alg Dexp xs.length capT).pMod))
      (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else []) n a gi row idx :=
    { hhs := hhs
      hxs := hxs
      s0 := hDO.s0
      h0 := hDO.hd 0 (Or.inl rfl)
      s1 := by rw [(oth 1 (by decide) (by decide)).1]; exact hPre.s1
      h1 := by rw [(oth 1 (by decide) (by decide)).2]; exact hPre.h1
      s2 := by rw [(oth 2 (by decide) (by decide)).1]; exact hPre.s2
      h2 := by rw [(oth 2 (by decide) (by decide)).2]; exact hPre.h2
      s113 := by rw [(oth 113 (by decide) (by decide)).1]; exact hPre.s113
      h113 := by rw [(oth 113 (by decide) (by decide)).2]; exact hPre.h113
      sPr := hDO.sPr
      hPr := hDO.hd 130 (Or.inr ⟨by decide, by decide⟩)
      sWin := hDO.sWin
      hWin := hDO.hd 131 (Or.inr ⟨by decide, by decide⟩)
      sMod := hDO.sMod
      hMod := hDO.hd 132 (Or.inr ⟨by decide, by decide⟩)
      sPay := hDO.sPay
      hPay := fun i => hDO.hd _ (Or.inr ⟨by simp only; omega, by simp only; omega⟩)
      blank := fun k a0 a1 a2 a3 a4 => by
        rw [(oth k a0 a4).1, (oth k a0 a4).2]; exact hPre.blank k a0 a1 a2 a3 a4
      cell := by rw [hDO.cell]; exact hPre.cell
      vN := by rw [hDO.val]; exact hPre.vN
      vA := by rw [hDO.val]; exact hPre.vA
      hb := fun k hk => by rw [hDO.val]; exact hPre.hb k hk
      vXA := by rw [hDO.val]; exact hPre.vXA
      vXB := by rw [hDO.val]; exact hPre.vXB
      vMS := by rw [hDO.val]; exact hPre.vMS
      h0v := h0v
      vRow := by rw [hDO.val]; exact hPre.vRow
      vGi := by rw [hDO.val]; exact hPre.vGi
      vIdx := by rw [hDO.val]; exact hPre.vIdx
      zScan := fun k a b c d e f => by rw [hDO.val]; exact hPre.zScan k a b c d e f
      zl := fun q h => by rw [hDO.val]; exact hPre.zl q h
      zm := fun q a b => by rw [hDO.val]; exact hPre.zm q a b
      vR := by rw [hDO.val, hPre.vR]; omega
      zT := by rw [hDO.val]; exact hPre.zT
      zK := by rw [hDO.val]; exact hPre.zK
      bd := fun q => by rw [hDO.val]; exact hPre.bd q }
  obtain ⟨τ, c, t, e, cle, tlt, tle, tlt2, r1, r2, hR⟩ := pbPost_run cap x τD _ out j hs xs tg _ _ _ _ n a gi row idx
    hPI hidx hLc cPool cPos
  exact ⟨τD, τ, c, t, sD, e, cle, hDO.val, tlt, tle, tlt2, r1, r2, hR⟩

end F2

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
