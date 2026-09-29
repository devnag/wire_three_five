import Proof.Wire_3_5.Primitive.Writers.HashCellC

/-! # HASH setup (C), P2b part 8: the HASH cell's run at a THR call

P3:2253-2290 and P3:3011-3016: at a THR call, the HASH cell (`cellM`: fill ; decode and counts ; front end and numbers
machine ; the loop's inputs ; the populations) runs from the call's request, data word, `1^V` and `1^W`, at capacity
`2W + 2`, under its capacity facts (`CellFit`), the front end's `TF2Ok` at `V` and the numbers machine's need, and
leaves the kept words writer's inputs `kwIns (hashDataOf …) c i` on the streams `kS i` (`i ≠ 0, 10`), the request, the
data word and `1^V` kept.

* `caout_dockin` (part A's exit is the docks' entry); **`CellFit`**, `callCost`, **`cell_call`**.

Paper quantities of the main type: the kept words writer's inputs `kwIns (hashDataOf …) c i` (P3:2253-2290). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimT.HbM (popsWord)

section Dock
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- **Part A's exit is the docks' entry.** -/
theorem caout_dockin (cap : ℕ) (τ : WState (LNS (cX T N)) LNR) (w : List Bool) (V : ℕ) (u : List Bool)
    (nc capT kh nP nE aC aL : ℕ) (h : CAOut cap (cX T N) τ w V u nc capT kh nP nE aC aL) :
    DockIn T N τ w V nc capT := by
  have hst : ∀ k : Fin 161, k.val ≠ 153 → k.val ≠ 154 → k.val ≠ 155 → k.val ≠ 156 → k.val ≠ 157 →
      τ.st (sk (cX T N) k) = (CellLoopD.blankCellD (cX T N) w [] V u).st (sk (cX T N) k) := by
    intro k a b c d e
    rw [h.st]
    rw [Function.update_of_ne (skne _ k 157 e), Function.update_of_ne (skne _ k 155 c),
      Function.update_of_ne (skne _ k 156 d), Function.update_of_ne (skne _ k 154 b),
      Function.update_of_ne (skne _ k 153 a)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.sh _ (skne _ 0 113 (by decide)), h.sh _ (skne _ 2 113 (by decide)), ?_, ?_⟩
  · rw [hst 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, skne _ 0 113 (by decide)]
  · rw [hst 2 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, skne _ 2 113 (by decide),
      skne _ 2 0 (by decide), skne _ 2 1 (by decide)]
  · rw [h.st]
    rw [Function.update_of_ne (skne _ 153 157 (by decide)), Function.update_of_ne (skne _ 153 155 (by decide)),
      Function.update_of_ne (skne _ 153 156 (by decide)), Function.update_of_ne (skne _ 153 154 (by decide)),
      Function.update_self]
  · rw [h.st]
    rw [Function.update_of_ne (skne _ 154 157 (by decide)), Function.update_of_ne (skne _ 154 155 (by decide)),
      Function.update_of_ne (skne _ 154 156 (by decide)), Function.update_self]
  · intro k hk
    rw [hst k (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact bcD_st _ w V u k (by omega) (by omega) (by omega) (by omega)
  · intro k
    rw [h.st]
    have ne : ∀ j : Fin 161, sT (cX T N) k ≠ sk (cX T N) j := fun j e => sk_ne_sT _ j k e.symm
    rw [Function.update_of_ne (ne 157), Function.update_of_ne (ne 155), Function.update_of_ne (ne 156),
      Function.update_of_ne (ne 154), Function.update_of_ne (ne 153)]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, ne]
  · intro k hk
    exact h.sh _ (skne _ k 113 (by omega))
  · intro k
    exact h.sh _ (fun e => sk_ne_sT _ 113 k e.symm)

end Dock

section Call
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E}
  (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ}
  (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
  (translation : List ℕ)

/-- **The HASH cell's capacity facts at a THR call** (capacity `cap`; the populations' per-row bounds `Bm`, `Sm`). -/
structure CellFit (cr Bm Sm cap : ℕ) : Prop where
  c1 : 2 * (cw ha' Cs carriers translation).length + 2 ≤ cap
  c2 : 2 ^ (natBitLength n + 1) ≤ cap
  c3 : (0 + 4) * (n + 3) + 2 * cr + 20 ≤ cap
  cl : ∀ k, (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (I.filterParams .thr n).cap ++
    (carriers.map List.length ++ [(PrimT.ThrTab.tupleG Cs).length])).getD k 0 ≤ cap
  cs : (carriers.map List.length).sum + (PrimT.ThrTab.tupleG Cs).length + 4 ≤ cap
  cD1 : (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (I.filterParams .thr n).cap).getD 13 0 +
    2 * (carriers.map List.length).sum + (carriers.length + 1) * 4096 * (I.filterParams .thr n).cap +
    (carriers.length + 1) * 4096 + (I.filterParams .thr n).cap + 10 ≤ cap
  cG1 : (WriterIface.auxP alg I hs Cs carriers).cap * 32 + 2 ≤ cap
  cG2 : (WriterIface.auxP alg I hs Cs carriers).len + 8 ≤ cap
  cG3 : (WriterIface.auxP alg I hs Cs carriers).errExp + 4 ≤ cap
  cG4 : 2 ^ ((WriterIface.auxP alg I hs Cs carriers).seedBits + 1) ≤ cap
  cG5 : (WriterIface.auxP alg I hs Cs carriers).labelBits + (WriterIface.auxP alg I hs Cs carriers).fieldBits +
    (WriterIface.auxP alg I hs Cs carriers).walkLen + 512 ≤ cap
  cD3 : 2 * (carriers.map List.length).sum + (Primitive.thrOccs (I.starParams n hs) Cs).length +
    2 ^ (WriterIface.auxP alg I hs Cs carriers).seedBits +
    2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2)) + 1) +
    2 ^ (WriterIface.auxP alg I hs Cs carriers).seedBits * 2 ^ (2 * ((I.starParams n hs).s * ((I.starParams n hs).r / 2)))
      * 5 + 10 ≤ cap
  ckh : 2 ^ ((I.starParams n hs).s * ((I.starParams n hs).r / 2) + 1) ≤ cap
  cB : (cv alg I hs Cs carriers).nG + (cv alg I hs Cs carriers).dig + (WriterIface.auxP alg I hs Cs carriers).len +
    (cv alg I hs Cs carriers).Bs + 4096 * (WriterIface.auxP alg I hs Cs carriers).cap + 2 ^ 13 ≤ cap
  cneed : ∀ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg
    (Primitive.thrCallDen alg I hs Cs)), FinalPass.DigsBody.digsWImpl.need
      (FinalPass.Digs.digsN (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) pr.val) ≤ cap
  cBm : ∀ pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff (I.starParams n hs) Cs alg
    (Primitive.thrCallDen alg I hs Cs)), FinalPass.DigsBody.digsWImpl.bound
      (FinalPass.Digs.digsN (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) pr.val) ≤ Bm
  cSm : ∀ (g : Primitive.ThrEq (I.starParams n hs) Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff
    (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs))),
    ((HashPops.digL (I.starParams n hs) Cs carriers alg (Primitive.thrCallDen alg I hs Cs) g pr).flatMap
      HashPops.segW).length ≤ Sm
  cn : Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs) ≤ cap
  cc : (popsWord (PrimT.C4H.hashPopsOf alg I hs Cs carriers)).length + 2 * Sm + 4 ≤ cap
  cP : (PrimAsm.Data.unaryList (HashPops.hPrimes alg I hs Cs)).length + 1 ≤ cap
  cG : HashPops.hNG alg Cs + 1 ≤ cap

/-- The cell's step bound at the call. -/
noncomputable def callCost {Dexp : ℕ} (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
    (cr V W Bm Sm : ℕ) : ℕ :=
  cellCost W (cACost (2 * W + 2) n (cw ha' Cs carriers translation).length cr)
    (T.cost V + 1 + N.cost (n + V + (I.filterParams .thr n).cap))
    (cBCost (2 * W + 2) + 1 + popsCost alg I hs Cs Bm Sm)

/-- **The HASH cell at a THR call**: the kept words writer's inputs on the streams `kS i`. -/
theorem cell_call (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg I.D)
    (cr V W Bm Sm : ℕ) (hrP : (I.starParams n hs).r = Ledger.rowBr cr n) (hn1 : 1 ≤ n)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) (hnc : carriers.length ≤ 2)
    (hcapT : 1 ≤ (I.filterParams .thr n).cap)
    (hok : PrimThrW.TopFront2.TF2Ok Cs (carriers.map Stars.Carrier.code) V)
    (hneed : N.need (n + (I.filterParams .thr n).cap) ≤ V)
    (hfit : CellFit alg I hs ha' Cs carriers translation cr Bm Sm (2 * W + 2)) :
    ∃ (τF : WState (LNS (cX T N)) LNR) (m : ℕ),
      Step (cellM T N cr) (callCost alg I hs ha' Cs carriers translation T N cr V W Bm Sm) (fun _ => 0)
        (Fin.addCases (rawX (cX T N) (cw ha' Cs carriers translation) (cu alg I hs Cs carriers) V W)
          (fun _ : Fin 1 => [])) (fun _ => 0)
        (Fin.addCases (Fin.addCases (wenc (2 * W + 2) τF).A (xB W)) (fun _ : Fin 1 => List.replicate m false)) ∧
      τF.st (sk (cX T N) 0) = frame (cw ha' Cs carriers translation) ∧
      τF.st (sk (cX T N) 113) = cu alg I hs Cs carriers ∧ τF.st (sk (cX T N) 2) = List.replicate V true ∧
      ∀ (c : ℕ) (i : Fin 12), i.val ≠ 0 → i.val ≠ 10 →
        τF.st (sk (cX T N) (kS i)) = PrimT.C4KW.kwIns (PrimT.C4H.hashDataOf alg I hs Cs carriers) c i := by
  set cap := 2 * W + 2 with hcap
  set P := I.starParams n hs with hP
  set hsL := ThrData.hashNums P Cs carriers alg I.D (I.filterParams .thr n).cap with hhsL
  set xs := carriers.map List.length with hxs
  set tg := (PrimT.ThrTab.tupleG Cs).length with htg
  set Pa := WriterIface.auxP alg I hs Cs carriers with hPa
  set v := cv alg I hs Cs carriers with hv
  have hw : cw ha' Cs carriers translation = Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation) := by
    have h := ReqBridge.reqW_thrReq ha' Cs carriers translation []
    rw [List.append_nil, List.append_nil] at h
    exact h.symm
  have hu : cu alg I hs Cs carriers = Data.unaryList (hsL ++ (xs ++ [tg])) := rfl
  have hhs : hsL.length = 16 := ThrData.hashNums_length _ _ _ _ _ _
  have hxl : xs.length = carriers.length := List.length_map _
  have hPc1 : 1 ≤ Pa.cap := by
    rw [hPa, HashCall.auxP_cap]
    have : 1 ≤ (carriers.length + 1) * 4096 := by nlinarith
    nlinarith
  -- part A
  obtain ⟨τA, cA, eA, cAle, hCA⟩ := cA_run cap (cX T N) cr P hrP (cw ha' Cs carriers translation) V
    (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) (RepairRepresentation.natListWord translation) hw
    hsL xs tg hhs (by rw [hxl]; exact hnc) (by rw [hxl]; rfl) Pa rfl
    (by rw [hPa, HashCall.auxP_cap, hxl]; rfl) (by rw [hPa, HashCall.auxP_err, ← HashCall.hashNums_ee]) hPc1
    hfit.c1 hfit.c2 hfit.c3 hfit.cl hfit.cs (by rw [hxl]; exact hfit.cD1) hfit.cG1 hfit.cG2 hfit.cG3 hfit.cG4
    hfit.cG5 (by rw [HashCall.hashNums_M]; exact hfit.cD3) hfit.ckh
  rw [← hu] at eA
  have hin := caout_dockin T N cap τA _ V _ _ _ _ _ _ _ _ hCA
  rw [hxl, HashCall.hashNums_cap] at hin
  rw [hw] at hin
  -- the docks
  obtain ⟨τD, sD, hDO⟩ := docks_run T N cap τA P Cs (carriers.map Stars.Carrier.code)
    (RepairRepresentation.natListWord translation) V carriers.length (I.filterParams .thr n).cap hin hn1 ha' hd hnc
    hcapT hok hneed
  have hvD : τD.val = τA.val := hDO.val
  -- part B
  obtain ⟨τB, cB, eB, cBle, stB, shB, clB, b53, b3, b4, b0, zB, bdB⟩ := cB_run cap (cX T N) τD v.nG v.dig Pa.len
    Pa.cap a' v.Bs (hDO.sNum 0) (hDO.hd 139 (by decide)) (hDO.sNum 5) (hDO.hd 144 (by decide)) (hDO.sNum 8)
    (hDO.hd 147 (by decide)) (by rw [hvD]; exact hCA.g1) (by rw [hvD]; exact hCA.g0)
    (by rw [hvD]; exact hCA.low) (by rw [hvD]; exact hCA.bd) (bs_eq alg I hs Cs carriers) hPc1 hfit.cB
  -- the populations
  have oth : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 2 → (k.val < 130 ∨ (137 ≤ k.val ∧ k.val ≤ 138) ∨ 154 < k.val) →
      τB.st (sk (cX T N) k) = τA.st (sk (cX T N) k) ∧ τB.sh (sk (cX T N) k) = τA.sh (sk (cX T N) k) := by
    intro k a b c
    refine ⟨by rw [stB]; exact (hDO.other k a b c).1, ?_⟩
    rw [shB _ (skne _ k 139 (by omega)) (skne _ k 144 (by omega)) (skne _ k 147 (by omega))]
    exact (hDO.other k a b c).2
  have hA_bl : ∀ k : Fin 161, k.val = 137 ∨ k.val = 138 → τA.st (sk (cX T N) k) = [] := by
    intro k hk
    rw [hCA.st]
    rw [Function.update_of_ne (skne _ k 157 (by omega)), Function.update_of_ne (skne _ k 155 (by omega)),
      Function.update_of_ne (skne _ k 156 (by omega)), Function.update_of_ne (skne _ k 154 (by omega)),
      Function.update_of_ne (skne _ k 153 (by omega))]
    exact bcD_st _ _ V _ k (by omega) (by omega) (by omega) (by omega)
  obtain ⟨τF, eP, sO, sOth, clF⟩ := cP_run alg I hs Cs carriers cap (cX T N) τB ha'
    (fun i => by rw [stB]; exact hDO.sPay i)
    (fun i => by
      have hi := i.isLt
      rw [shB _ (skne _ _ 139 (by simp; omega)) (skne _ _ 144 (by simp; omega)) (skne _ _ 147 (by simp; omega))]
      exact hDO.hd _ (by simp; omega))
    b0 b3 (by rw [b4, Records.thrOff_eq]; rfl) (by rw [b53, hng_eq alg I hs Cs carriers]) zB
    (by rw [stB]; exact hDO.sPr) (by rw [shB _ (skne _ 130 139 (by decide)) (skne _ 130 144 (by decide))
      (skne _ 130 147 (by decide))]; exact hDO.hd 130 (by decide))
    (by rw [(oth 138 (by decide) (by decide) (by decide)).1]; exact hA_bl 138 (by decide))
    (by rw [(oth 138 (by decide) (by decide) (by decide)).2]; exact hCA.sh _ (skne _ 138 113 (by decide)))
    (by rw [(oth 137 (by decide) (by decide) (by decide)).1]; exact hA_bl 137 (by decide))
    (by rw [(oth 137 (by decide) (by decide) (by decide)).2]; exact hCA.sh _ (skne _ 137 113 (by decide)))
    Bm Sm hfit.cneed hfit.cBm hfit.cSm hfit.cn hfit.cc hfit.cP hfit.cG
  -- the cell
  obtain ⟨m, hm⟩ := cell_step T N cr (cw ha' Cs carriers translation) (cu alg I hs Cs carriers) V W τA τD τF cA
    (T.cost V + 1 + N.cost (n + V + (I.filterParams .thr n).cap)) (cB + 1 + popsCost alg I hs Cs Bm Sm) eA sD
    (WExec.seq eB eP)
  have hF : ∀ k : Fin 161, k.val ≠ 137 → k.val ≠ 138 → τF.st (sk (cX T N) k) = τB.st (sk (cX T N) k) :=
    fun k a b => sOth _ (skne _ k 138 b) (skne _ k 137 a)
  have hFD : ∀ k : Fin 161, k.val ≠ 137 → k.val ≠ 138 → τF.st (sk (cX T N) k) = τD.st (sk (cX T N) k) :=
    fun k a b => by rw [hF k a b, stB]
  have hAst : ∀ k : Fin 161, 154 < k.val → τF.st (sk (cX T N) k) = τA.st (sk (cX T N) k) :=
    fun k hk => by rw [hFD k (by omega) (by omega)]; exact (hDO.other k (by omega) (by omega) (by omega)).1
  have hMP := mp_eq alg I hs Cs carriers
  refine ⟨τF, m, hm.enlarge ?_, ?_, ?_, ?_, ?_⟩
  · unfold callCost cellCost
    have h1 : cA ≤ cACost (2 * W + 2) n (cw ha' Cs carriers translation).length cr := cAle
    have h2 : cB ≤ cBCost (2 * W + 2) := cBle
    omega
  · rw [hFD 0 (by decide) (by decide), hDO.s0, hw] <;> rfl
  · rw [hFD 113 (by decide) (by decide), (hDO.other 113 (by decide) (by decide) (by decide)).1, hCA.st]
    rw [Function.update_of_ne (skne _ 113 157 (by decide)), Function.update_of_ne (skne _ 113 155 (by decide)),
      Function.update_of_ne (skne _ 113 156 (by decide)), Function.update_of_ne (skne _ 113 154 (by decide)),
      Function.update_of_ne (skne _ 113 153 (by decide))]
    simp [CellLoopD.blankCellD]
    exact hu.symm
  · rw [hFD 2 (by decide) (by decide), hDO.s2]
  · intro c i h0 h10
    fin_cases i
    · exact absurd rfl h0
    · show τF.st (sk (cX T N) 138) = _
      rw [sO]; rfl
    · show τF.st (sk (cX T N) 151) = _
      rw [hFD 151 (by decide) (by decide)]
      rw [show sk (cX T N) 151 = sk (cX T N) ⟨139 + (12 : Fin 14).val, by decide⟩ from rfl, hDO.sNum 12]
      show List.replicate (v.get 12) true = List.replicate (PrimT.C4H.hashDataOf alg I hs Cs carriers).MP.ell0 true
      rw [hMP]
      rfl
    · show τF.st (sk (cX T N) 152) = _
      rw [hFD 152 (by decide) (by decide)]
      rw [show sk (cX T N) 152 = sk (cX T N) ⟨139 + (13 : Fin 14).val, by decide⟩ from rfl, hDO.sNum 13]
      show List.replicate (v.get 13) true = List.replicate (PrimT.C4H.hashDataOf alg I hs Cs carriers).MP.refMod true
      rw [hMP]
      rfl
    · show τF.st (sk (cX T N) 147) = _
      rw [hFD 147 (by decide) (by decide)]
      rw [show sk (cX T N) 147 = sk (cX T N) ⟨139 + (8 : Fin 14).val, by decide⟩ from rfl, hDO.sNum 8]
      show List.replicate (v.get 8) true = List.replicate (PrimT.C4H.hashDataOf alg I hs Cs carriers).MP.Bstar true
      rw [hMP]
      rfl
    · show τF.st (sk (cX T N) 149) = _
      rw [hFD 149 (by decide) (by decide)]
      rw [show sk (cX T N) 149 = sk (cX T N) ⟨139 + (10 : Fin 14).val, by decide⟩ from rfl, hDO.sNum 10]
      show List.replicate (v.get 10) true = List.replicate (PrimT.C4H.hashDataOf alg I hs Cs carriers).MP.t true
      rw [hMP]
      rfl
    · show τF.st (sk (cX T N) 148) = _
      rw [hFD 148 (by decide) (by decide)]
      rw [show sk (cX T N) 148 = sk (cX T N) ⟨139 + (9 : Fin 14).val, by decide⟩ from rfl, hDO.sNum 9]
      show List.replicate (v.get 9) true = List.replicate (PrimT.C4H.hashDataOf alg I hs Cs carriers).MP.J true
      rw [hMP]
      rfl
    · show τF.st (sk (cX T N) 155) = _
      rw [hAst 155 (by decide), hCA.st, Function.update_of_ne (skne _ 155 157 (by decide)), Function.update_self]
      show List.replicate (2 * (carriers.map List.length).sum + hsL.getD 8 0) true =
        List.replicate (Records.thrPool P Cs carriers).length true
      have hp : 2 * (carriers.map List.length).sum + hsL.getD 8 0 = (Records.thrPool P Cs carriers).length :=
        HashCall.hash_pool alg (I.starParams n hs) Cs carriers I.D (I.filterParams .thr n).cap
      rw [hp]
    · show τF.st (sk (cX T N) 156) = _
      rw [hAst 156 (by decide), hCA.st, Function.update_of_ne (skne _ 156 157 (by decide)),
        Function.update_of_ne (skne _ 156 155 (by decide)), Function.update_self]
      rfl
    · show τF.st (sk (cX T N) 157) = _
      rw [hAst 157 (by decide), hCA.st, Function.update_self]
      simp only [PrimT.C4KW.kwIns, PrimT.C4KW.kwNum]
      rw [← card_gapSeed]
      rfl
    · exact absurd rfl h10
    · show τF.st (sk (cX T N) 146) = _
      rw [hFD 146 (by decide) (by decide)]
      rw [show sk (cX T N) 146 = sk (cX T N) ⟨139 + (7 : Fin 14).val, by decide⟩ from rfl, hDO.sNum 7]
      show List.replicate (v.get 7) true = List.replicate (PrimT.C4H.hashPopsOf alg I hs Cs carriers).length true
      rw [pops_len alg I hs Cs carriers]
      rfl

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.HashCell
