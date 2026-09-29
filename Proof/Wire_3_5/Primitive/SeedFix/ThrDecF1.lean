import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR9

/-! # THR decode front, assembly part 1: the register program before the docks

`W1 = tNW ; cmpW ; ifr [j < TOT] (dec ; idxW ; tBrW fbTW pbPreW) skip`: the numbers (register-only, `tN_run2`), the
capped test (`cmp_run`), and at `j < TOT` the index split (`tIdx_run`) and the branch (`tBr_spec`): the FILTER
finisher (`fbT_spec`, `FsIn2`), the RADIX pre-dock program (`pbPre_run`, the docks' entry), the markers.

* `W1`, **`W1a_run`** (numbers and test), **`W1b_run`** (index and branch at `j < TOT`).

Paper quantity of the main types: the THR tape's unit `j` and its row's setup entry (P3:3011-3016). -/

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
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.UnionMachine.ThrDec

section F1
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (cap : ℕ) (x : ℕ)

/-- **The register program before the docks.** -/
def W1 (hx : dX T N ≤ x) (cr fe : ℕ) : WM (LNS x) LNR :=
  .seq (.seq (tNW x cr fe) (cmpW x)) (.ifr (H 22) (.seq (.dec (H 22)) (.seq (idxW x) (tBrW x (fbTW x) (pbPreW T N x hx))))
    .skip)

/-- **The numbers and the capped test, run.** -/
theorem W1a_run (cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w out : List Bool) (j : ℕ)
    (codes cc : List ℕ) (tl : List Bool) (Kb : ℕ) (hw : w = Data.reqW P.n true codes cc tl)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb) (hs xs : List ℕ) (tg : ℕ) (hhs : hs.length = 16) (hxs : xs.length ≤ 2)
    (h0v : hs.getD 0 0 = xs.length) (FP : GapParams) (hPc : FP.cap = hs.getD 1 0)
    (hPl : FP.len = 2 * (P.n + 1) ^ 26) (hPe : FP.errExp = fe * Nat.clog 2 (P.n + 2)) (hPc1 : 1 ≤ FP.cap)
    (hN : TNeed cap w P.n codes cc Kb cr fe hs xs tg FP (P.s * (P.r / 2)))
    (hTc : 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2) + 2
      ≤ cap) :
    ∃ σN c, WExec cap (.seq (tNW x cr fe) (cmpW x))
        (CellLoopD.blankCellD x w out j (Data.unaryList (hs ++ (xs ++ [tg])))) (σN.setv (H 22)
          (if j < 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2)
            then 1 else 0)) c ∧
      c ≤ tNCost P.n codes.length cc.length Kb cr fe cap + 1 + (UnaryPow.sq cap +
        16 * (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2)) + 16) ∧
      TNums x cap σN w out j (Data.unaryList (hs ++ (xs ++ [tg]))) P.n codes.length cc.length (P.s * (P.r / 2)) hs xs
        FP ((xs.length + 1) * 3 + 2) (2 ^ (2 * (P.s * (P.r / 2)))) (hs.getD 6 0) (hs.getD 2 0)
        (2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) * ((xs.length + 1) * 3 + 2)) ∧
      σN.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take (16 + xs.length))).length := by
  obtain ⟨σN, c1, e1, c1le, hT, h113⟩ :=
    tN_run2 cap x cr fe P hrP w out j true codes cc tl Kb hw hKb hs xs tg hhs hxs h0v FP hPc hPl hPe hPc1 hN
  have n20 : sk x 2 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n21 : sk x 2 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n2B0 : sk x 2 ≠ sk x 0 := fun e => absurd (sk_inj x e) (by decide)
  obtain ⟨σC, c2, e2, c2le, f22, k2, st2, sh2, cl2⟩ := cmp_run cap x σN j _ hT.g56 (hT.zH 20) (hT.zH 21) (hT.zH 22)
    hT.zTM (by rw [hT.st]; simp [CellLoopD.blankCellD, blankCell, n20, n21, n2B0])
    (by rw [hT.sh _ n20]; simp [CellLoopD.blankCellD, blankCell, n21]) hTc
  have eq : σC = σN.setv (H 22) (if j < 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * (P.s * (P.r / 2))) *
      ((xs.length + 1) * 3 + 2) then 1 else 0) := by
    refine WState.eq (by rw [sh2]; rfl) (by rw [st2]; rfl) ?_ (by rw [cl2]; rfl)
    funext r
    by_cases h : r = H 22
    · subst h; simp [f22]
    · simp [Function.update_of_ne h, k2 r h]
  rw [eq] at e2
  exact ⟨σN, _, WExec.seq e1 e2, by omega, hT, h113⟩

/-- **The RADIX pre-dock outcome**: the docks' entry, the RADIX marker, and every fact the post-dock entry
(`PostIn`) keeps from the decoded state. -/
structure PreOK (hx : dX T N ≤ x) (τ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (hs xs : List ℕ) (tg : ℕ)
    (n a row gi idx V capT : ℕ) : Prop where
  dock : DockInT T N x τ w V xs.length capT
  vR : τ.val rRadK = 1
  s1 : τ.st (sk x 1) = out ++ [false]
  h1 : τ.sh (sk x 1) = out.length
  s2 : τ.st (sk x 2) = List.replicate j true
  h2 : τ.sh (sk x 2) = 0
  s113 : τ.st (sk x 113) = Data.unaryList (hs ++ (xs ++ [tg]))
  h113 : τ.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take (16 + xs.length))).length
  blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → (k.val < 130 ∨ 136 < k.val) →
    τ.st (sk x k) = [] ∧ τ.sh (sk x k) = 0
  cell : τ.cell = false
  vN : τ.val dN = n
  vA : τ.val dA = a
  hb : ∀ k : Fin 32, k.val < 16 → τ.val (Hb k) = hs.getD k.val 0
  vXA : τ.val XA = xs.getD 0 0
  vXB : τ.val XB = xs.getD 1 0
  vMS : τ.val dMS = hs.getD 8 0
  vRow : τ.val (H 13) = row
  vGi : τ.val (H 17) = gi
  vIdx : τ.val (H 15) = idx
  zScan : ∀ k : Fin 40, 24 ≤ k.val → k.val ≤ 37 → k.val ≠ 29 → k.val ≠ 30 → k.val ≠ 31 → k.val ≠ 32 →
    τ.val (H k) = 0
  zl : ∀ q : Fin LNR, q.val < 250 → τ.val q = 0
  zm : ∀ q : Fin LNR, 398 < q.val → q.val < 408 → τ.val q = 0
  zT : τ.val TM = 0
  zK : τ.val dK = 0
  bd : ∀ q, τ.val q ≤ cap

/-- The finishers' cost bound. -/
def finCost (cap V ncar capT Dn : ℕ) : ℕ :=
  fbCost cap + 4 + (150 * UnaryPow.sq cap + (Dn + 1) * (4 * UnaryPow.sq cap) + 40 * (V + ncar + capT) + 40)

/-- **The index and the branch, run** at `j < TOT`. -/
theorem W1b_run (hx : dX T N ≤ x) (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (hs xs : List ℕ) (tg : ℕ)
    (n a nc kh : ℕ) (FP : GapParams) (N2 pS nG TOT : ℕ) (rq : ℕ → ℕ → ℕ → List Bool)
    (hT : TNums x cap σ w out j (Data.unaryList (hs ++ (xs ++ [tg]))) n a nc kh hs xs FP ((xs.length + 1) * 3 + 2) N2 pS nG
      TOT) (h113 : σ.sh (sk x 113) = (Data.unaryList ((hs ++ (xs ++ [tg])).take (16 + xs.length))).length)
    (hnc : nc = xs.length) (hxs : xs.length ≤ 2) (h0v : hs.getD 0 0 = xs.length) (hj : j < TOT) (hN2 : 1 ≤ N2) (hpS : 1 ≤ pS) (hnG : 1 ≤ nG)
    (hc : 2 * TOT + ((xs.length + 1) * 3 + 2) + N2 + pS + nG + nc + 20 ≤ cap)
    (cF : 4 * (j / thrEU nc % N2) + 2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0 + 1 ≤ cap)
    (hcA : w.length + (n + 1) ^ 26 * 2 + n + hs.getD 1 0 + 42 ≤ cap) (hCn : N.Cn ≤ cap)
    (hPD : (n + hs.getD 1 0 + 1) ^ N.Dn ≤ cap)
    (hcB : tV w.length n (hs.getD 1 0) N.Cn N.Dn + n + hs.getD 1 0 + hs.getD 0 0 + 42 ≤ cap) :
    ∃ τ c, WExec cap (.seq (idxW x) (tBrW x (fbTW x) (pbPreW T N x hx))) σ τ c ∧
      c ≤ 30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap + 1 +
        (finCost cap (tV w.length n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 0 0) (hs.getD 1 0) N.Dn + 12) ∧
      (IsReqU TOT nc j → rowOfU nc j < nc → τ.val rRadK = 0 ∧ τ.val rFltK ≠ 0 ∧
        FsIn2 x τ w out j (Data.unaryList (hs ++ (xs ++ [tg]))) FP.len FP.cap FP.errExp (j / thrEU nc / N2 / pS / nG)
          (2 * (2 * (j / thrEU nc % N2))) (2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0)
          (fbOff (rowOfU nc j) (xs.getD 0 0)) (fbL (rowOfU nc j) (xs.getD 0 0) (xs.getD 1 0))) ∧
      (IsReqU TOT nc j → rowOfU nc j = nc →
        PreOK T N cap x hx τ w out j hs xs tg n a (j / thrEU nc % N2) (j / thrEU nc / N2 / pS % nG)
          (j / thrEU nc / N2 % pS) (tV w.length n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 1 0)) ∧
      (¬ IsReqU TOT nc j → IdleAt x τ w out (unitE TOT (nc + 1) 0 rq j) j) := by
  have hsq := UnaryPow.sq_ge cap
  have n2B : sk x 2 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n21 : sk x 2 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n20 : sk x 2 ≠ sk x 0 := fun e => absurd (sk_inj x e) (by decide)
  have n1B : sk x 1 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n0B : sk x 0 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have n01 : sk x 0 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have hEU : (xs.length + 1) * 3 + 2 = thrEU nc := by rw [hnc]; rfl
  obtain ⟨σI, eI, hV, kI, stI, shI, clI⟩ := tIdx_run cap x σ j TOT (thrEU nc) N2 pS nG nc
    (by rw [hT.st]; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21])
    (by rw [hT.sh _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]) hT.g56 (by rw [← hEU]; exact hT.g55) hT.g32
    hT.g53 hT.g52 hT.g41 hT.vNC hT.zH (by rw [← hEU]; omega) hN2 hpS hnG hj (by rw [← hEU]; omega)
  have low : ∀ r : Fin LNR, r.val < 472 → σI.val r = σ.val r := fun r h => kI r (fun k => (H_ne k r h).symm)
  have hBI : ∀ q, σI.val q ≤ cap := wexec_le cap eI hT.bd
  set u := Data.unaryList (hs ++ (xs ++ [tg])) with hu
  have stI' : σI.st = (CellLoopD.blankCellD x w out j u).st := by rw [stI, hT.st]
  have shI' : ∀ s, s ≠ sk x 113 → σI.sh s = (CellLoopD.blankCellD x w out j u).sh s := fun s h => by
    rw [shI, hT.sh s h]
  obtain ⟨τ, c, e, cle, hFo, hPo, hIo⟩ := tBr_spec cap x (fbTW x) (pbPreW T N x hx) σI out w j TOT nc N2 pS nG
    (finCost cap (tV w.length n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 0 0) (hs.getD 1 0) N.Dn) rq
    (fun τ => τ.val rRadK = 0 ∧ τ.val rFltK ≠ 0 ∧
      FsIn2 x τ w out j u FP.len FP.cap FP.errExp (j / thrEU nc / N2 / pS / nG) (2 * (2 * (j / thrEU nc % N2)))
        (2 * (xs.getD 0 0 + xs.getD 1 0) + hs.getD 8 0) (fbOff (rowOfU nc j) (xs.getD 0 0))
        (fbL (rowOfU nc j) (xs.getD 0 0) (xs.getD 1 0)))
    (fun τ => PreOK T N cap x hx τ w out j hs xs tg n a (j / thrEU nc % N2) (j / thrEU nc / N2 / pS % nG)
      (j / thrEU nc / N2 % pS) (tV w.length n (hs.getD 1 0) N.Cn N.Dn) (hs.getD 1 0))
    hV (by rw [stI']; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm])
    (by rw [shI' _ n1B]; simp [CellLoopD.blankCellD, blankCell])
    (by rw [stI']; simp [CellLoopD.blankCellD, blankCell, sk_inj x |>.ne (show (150 : Fin 161) ≠ 0 by decide),
      sk_inj x |>.ne (show (150 : Fin 161) ≠ 1 by decide), sk_inj x |>.ne (show (150 : Fin 161) ≠ 2 by decide),
      sk_inj x |>.ne (show (150 : Fin 161) ≠ 113 by decide)])
    (by rw [shI' _ (sk_inj x |>.ne (show (150 : Fin 161) ≠ 113 by decide))]
        simp [CellLoopD.blankCellD, blankCell, sk_inj x |>.ne (show (150 : Fin 161) ≠ 1 by decide)])
    (by rw [stI']; simp [CellLoopD.blankCellD, blankCell, sk_inj x |>.ne (show (151 : Fin 161) ≠ 0 by decide),
      sk_inj x |>.ne (show (151 : Fin 161) ≠ 1 by decide), sk_inj x |>.ne (show (151 : Fin 161) ≠ 2 by decide),
      sk_inj x |>.ne (show (151 : Fin 161) ≠ 113 by decide)])
    (by rw [shI' _ (sk_inj x |>.ne (show (151 : Fin 161) ≠ 113 by decide))]
        simp [CellLoopD.blankCellD, blankCell, sk_inj x |>.ne (show (151 : Fin 161) ≠ 1 by decide)])
    (by rw [stI']; simp [CellLoopD.blankCellD, blankCell, n0B])
    (by rw [shI' _ n0B]; simp [CellLoopD.blankCellD, blankCell, n01])
    (by rw [stI']; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21])
    (by rw [shI' _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21])
    (by rw [low _ (by decide)]; exact hT.zm _ (by decide) (by decide))
    (by rw [low _ (by decide)]; exact hT.zm _ (by decide) (by decide))
    (fun hq hr => by
      have hr1 : rowOfU nc j ≤ 1 := by omega
      obtain ⟨τF, mF, eF, mle, r0, f0, hFs⟩ := fbT_spec cap x σI w out u j FP (j / thrEU nc / N2 / pS / nG)
        (j / thrEU nc % N2) (xs.getD 0 0) (xs.getD 1 0) (hs.getD 8 0) (rowOfU nc j) hr1 stI' shI' (by rw [clI, hT.cell])
        (fun q hq => by rw [low q (by omega)]; exact hT.zl q hq)
        (fun q a b => by rw [low q (by omega)]; exact hT.zm q a b)
        (by rw [low _ (by decide)]; exact hT.zTM) hBI
        (by rw [low _ (by rw [G_val]; omega)]; exact hT.g0) (by rw [low _ (by rw [G_val]; omega)]; exact hT.g1)
        (by rw [low _ (by rw [G_val]; omega)]; exact hT.g2) hV.h18 hV.h13 (by rw [hV.h9]; rfl)
        (by rw [low _ (by decide)]; exact hT.vXA) (by rw [low _ (by decide)]; exact hT.vXB)
        (by rw [low _ (by decide)]; exact hT.vMS) (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨τF, mF, eF, ⟨r0, f0, hFs⟩, by unfold finCost; omega⟩)
    (fun hq hr => by
      obtain ⟨τP, mP, eP, mle, hDI, r1, v20, kP, stP, shP, clP⟩ := pbPre_run T N cap x hx σI w out j u w.length n
        (hs.getD 1 0) (hs.getD 0 0) stI' shI' (by rw [low _ (by decide)]; exact hT.vLEN)
        (by rw [low _ (by decide)]; exact hT.vN) (by rw [low _ (by rw [Hb_val]; omega)]; exact hT.hb 0 (by decide))
        (by rw [low _ (by rw [Hb_val]; omega)]; exact hT.hb 1 (by decide)) (fun k hk => hV.hz k hk)
        (by rw [low _ (by decide)]; exact hT.zTM) (by rw [low _ (by decide)]; exact hT.zm _ (by decide) (by decide))
        hcA hCn hPD hcB
      refine ⟨τP, mP, eP, ?_, by unfold finCost; omega⟩
      have kl : ∀ r : Fin LNR, r ≠ rRadK → r.val < 472 → τP.val r = σ.val r := fun r a b => by
        rw [kP r a (fun e => by rw [e, H_val] at b; omega), low r b]
      have kH : ∀ k : Fin 40, k.val ≠ 20 → τP.val (H k) = σI.val (H k) := fun k hk =>
        kP _ (fun e => by have := congrArg Fin.val e; rw [H_val] at this; simp [rRadK] at this; omega)
          (fun e => hk (by have := congrArg Fin.val e; rw [H_val, H_val] at this; omega))
      have stk : ∀ k : Fin 161, τP.st (sk x k) = σI.st (sk x k) := fun k =>
        stP _ (Or.inl (by rw [sk_val]; omega))
      exact
        { dock := by rw [h0v] at hDI; exact hDI
          vR := r1
          s1 := by rw [stk, stI']; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm]
          h1 := by rw [shP, shI' _ n1B]; simp [CellLoopD.blankCellD, blankCell]
          s2 := by rw [stk, stI']; simp [CellLoopD.blankCellD, blankCell, n2B, n20, n21]
          h2 := by rw [shP, shI' _ n2B]; simp [CellLoopD.blankCellD, blankCell, n21]
          s113 := by rw [stk, stI']; simp [CellLoopD.blankCellD, hu]
          h113 := by rw [shP, shI, h113]
          blank := fun k a0 a1 a2 a3 a4 => by
            have m0 : sk x k ≠ sk x 0 := fun e => a0 (by rw [sk_inj x e]; rfl)
            have m1 : sk x k ≠ sk x 1 := fun e => a1 (by rw [sk_inj x e]; rfl)
            have m2 : sk x k ≠ sk x 2 := fun e => a2 (by rw [sk_inj x e]; rfl)
            have m3 : sk x k ≠ sk x 113 := fun e => a3 (by rw [sk_inj x e]; rfl)
            refine ⟨?_, ?_⟩
            · rw [stk, stI']; simp [CellLoopD.blankCellD, blankCell, m0, m1, m2, m3]
            · rw [shP, shI' _ m3]; simp [CellLoopD.blankCellD, blankCell, m1]
          cell := by rw [clP, clI, hT.cell]
          vN := by rw [kl _ (by decide) (by decide)]; exact hT.vN
          vA := by rw [kl _ (by decide) (by decide)]; exact hT.vA
          hb := fun k hk => by
            rw [kl _ (fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [rRadK] at this; omega)
              (by rw [Hb_val]; omega)]; exact hT.hb k hk
          vXA := by rw [kl _ (by decide) (by decide)]; exact hT.vXA
          vXB := by rw [kl _ (by decide) (by decide)]; exact hT.vXB
          vMS := by rw [kl _ (by decide) (by decide)]; exact hT.vMS
          vRow := by rw [kH 13 (by decide)]; exact hV.h13
          vGi := by rw [kH 17 (by decide)]; exact hV.h17
          vIdx := by rw [kH 15 (by decide)]; exact hV.h15
          zScan := fun k a b c d e f => by rw [kH k (by omega)]; exact hV.hz k (by omega)
          zl := fun q hq => by rw [kl q (fun e => by rw [e] at hq; simp [rRadK] at hq) (by omega)]; exact hT.zl q hq
          zm := fun q a b => by
            rw [kl q (fun e => by rw [e] at a; simp [rRadK] at a) (by omega)]; exact hT.zm q (by omega) b
          zT := by rw [kl _ (by decide) (by decide)]; exact hT.zTM
          zK := by rw [kl _ (by decide) (by decide)]; exact hT.zK
          bd := wexec_le cap eP hBI })
  refine ⟨τ, _, WExec.seq eI e, by omega, hFo, hPo, hIo⟩

end F1

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
