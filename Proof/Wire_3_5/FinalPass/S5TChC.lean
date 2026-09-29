import Proof.Wire_3_5.FinalPass.S5TChB

/-! # S5-THR, part 25: the THR path (P3:2150-2157, 2543-2558, 2596-2599, 3083-3086)

The THR half's THR branch on its layout, from the parse's exit: the first docks (`chainA_spec`: the fill count, the prep, W6), the next docks (`chainB_spec`: the front end, the data stage's inputs, the data stage), and the tail
(`tail_spec` on the named streams `tailSN` and registers `tailRg`): all eight THR slots written.

* `thrPathM`, `thrPathCost`, **`thrPath_spec`**.

Paper quantities of the main type: THR slots `8 … 15` (S2's call words and numbers `thrWords`, `thrNums`) at the
W6 numbers `v = thrNumVals` and the fixed hash's data `thrMP v.M v.A v.Bs v.den`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.HashSeed NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (dockS updS sTape_val)
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2InPorts tf2OutPorts TF2Ok)
open NearCubicWires.WireExponent3_5.PrimThrW.Nums3 (nums3InPorts nums3OutPorts)
open NearCubicWires.SupplierPipeline

section Path
variable (D : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (cap : ℕ)

/-- **The THR path's machine.** -/
noncomputable def thrPathM (l : Literals) (cr j0 jL j1 : ℕ) :=
  Composition.machine (Composition.machine (chainAM D (PrimThrW.TF3Cost.topFront3 alg).x alg Dexp l cr j0)
    (chainBM D alg Dexp jL j1))
    (tailW (tailSN D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) tailRg).toProg.compile

/-- The W6 numbers at the THR path's call. -/
noncomputable abbrev vOf (l : Literals) (cr : ℕ) (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ) (carriers : List (Stars.Carrier P.n)) :
    PrimThrW.Joins.ThrNumVals :=
  PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (PrimT.TS4.capTL l cr P.n)

/-- The fixed hash's parameters from the W6 numbers. -/
abbrev mpOf (v : PrimThrW.Joins.ThrNumVals) : MajorantParams := PrimThrW.Joins.thrMP v.M v.A v.Bs v.den

theorem tail_hi (k : Fin 19) (hk : 10 ≤ k.val) :
    (14 + D ≤ tailA k + tailB k * D ∧ tailA k + tailB k * D ≤ 20 + D) ∨
      (7 ≤ tailA k + tailB k * D ∧ tailA k + tailB k * D ≤ 8) := by
  fin_cases k <;> simp [tailA, tailB] at hk ⊢ <;> omega

theorem tail_hi9 (k : Fin 19) (hk : 9 ≤ k.val) :
    (14 + D ≤ tailA k + tailB k * D ∧ tailA k + tailB k * D ≤ 739 + D) ∨
      (7 ≤ tailA k + tailB k * D ∧ tailA k + tailB k * D ≤ 8) := by
  fin_cases k <;> simp [tailA, tailB] at hk ⊢ <;> omega

theorem thrPath_spec (l : Literals) (cr j0 jL j1 : ℕ) (hj0 : j0 ≤ D) (hjL : jL ≤ D) (hj1 : j1 ≤ D)
    (σ : WState (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) nrL)
    (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (tl : List Bool) (Wp L Wt : ℕ) (pre : List Bool)
    (s : Fin (2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).t * (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0) → Bool)
    (hu : PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl =
      pre ++ frame (List.ofFn s))
    (hIn : σ.st (sIn D _ _) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
      (carriers.map Stars.Carrier.code) tl))
    (hT : σ.st (sTm D _ _) = sent ((pre ++ frame (List.ofFn s)).length + 1))
    (hx0 : σ.st (xsN D _ _ j0) = sent Wp) (hxL : σ.st (xsN D _ _ jL) = sent L)
    (hxW : σ.st (xsN D _ _ j1) = sent Wt)
    (hbl : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1),
      (1 ≤ i.val ∧ i.val ≤ 8) ∨ (13 + D ≤ i.val ∧ i.val ≠ 21 + D) → σ.st i = [])
    (hsh : ∀ i, σ.sh i = 0) (hn2 : σ.val (pR 2) = P.n) (ha3 : σ.val (pR 3) = a')
    (hz : ∀ r : Fin nrL, 10 ≤ r.val → r.val < 53 → σ.val r = 0) (hval : ∀ r, σ.val r ≤ cap)
    (hKb : ∀ c ∈ PrimAsm.ReqBridge.thrCodes Cs, natBitLength c ≤ Wp) (ha : a' ≤ 4) (hnc : carriers.length ≤ 2)
    (hN : PrimT.TS4.needT l cr P.n ≤ 2 * Wp + 2) (hn : 1 ≤ P.n) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
    (hcap1 : 1 ≤ PrimT.TS4.capTL l cr P.n)
    (hok : TF2Ok Cs (carriers.map Stars.Carrier.code) (Wp + (P.n + 1) ^ 26))
    (hneed : (PrimT.W6.numsW6 alg Dexp).need (P.n + PrimT.TS4.capTL l cr P.n) ≤ Wp + (P.n + 1) ^ 26)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ P.n + L) (hcN : natBitLength P.n + 1 ≤ 2 * Wt + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * Wt + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * Wt + 2)
    (hcx : ∀ x ∈ PrimAsm.ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + L ≤
      2 * Wt + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + P.n + L ≤
      2 * Wt + 2)
    (hcu : 2 * (PrimAsm.Data.unaryList (PrimAsm.ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * Wt + 2)
    (hcapn : P.n ≤ cap)
    (hc1 : 100 * ((pre ++ frame (List.ofFn s)).length + 1) + 10 * ((mpOf (vOf l cr P Cs alg Dexp carriers)).t + (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0) ≤ cap)
    (hc2 : 2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).t * (2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 + 2) + 1 + (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 + (mpOf (vOf l cr P Cs alg Dexp carriers)).t ≤ cap)
    (hc3 : (Hash4.winWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W).length ≤ cap) (hc4 : 2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 + 2 ≤ cap)
    (hcapS : (Hash4.seedWord (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 (Hash4.coefsRev (MajorantBits.coefVal (mpOf (vOf l cr P Cs alg Dexp carriers)) s))).length + 2 * (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 + 2 ≤ cap)
    (hcapO : (ListEval.levelWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W (ListEval.rowsOf (MajorantBits.dataBits (mpOf (vOf l cr P Cs alg Dexp carriers)) s) (mpOf (vOf l cr P Cs alg Dexp carriers)).M)).length + 1 ≤
      cap) (hM : (mpOf (vOf l cr P Cs alg Dexp carriers)).M ≤ cap) (hJ : (mpOf (vOf l cr P Cs alg Dexp carriers)).J ≤ cap) (hc5 : a' + (vOf l cr P Cs alg Dexp carriers).nG + (vOf l cr P Cs alg Dexp carriers).dig + (mpOf (vOf l cr P Cs alg Dexp carriers)).M + 4 ≤ cap) :
    ∃ σE c, Step (thrPathM D alg Dexp l cr j0 jL j1) c (wenc cap σ).H (wenc cap σ).A (wenc cap σE).H
        (wenc cap σE).A ∧
      c ≤ chainACost alg Dexp l cr P.n (PrimAsm.ReqBridge.thrCodes Cs).length (carriers.map Stars.Carrier.code).length
          Wp + 1 + (chainBCost alg Cs carriers (Wp + (P.n + 1) ^ 26) L Wt + 1 +
        tailCost (pre ++ frame (List.ofFn s)).length (mpOf (vOf l cr P Cs alg Dexp carriers)).t (mpOf (vOf l cr P Cs alg Dexp carriers)).ell0 (Hash4.winWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W).length
          (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (Hash4.coefsRev (MajorantBits.coefVal (mpOf (vOf l cr P Cs alg Dexp carriers)) s)).length
          (ListEval.levelWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W (ListEval.rowsOf (MajorantBits.dataBits (mpOf (vOf l cr P Cs alg Dexp carriers)) s) (mpOf (vOf l cr P Cs alg Dexp carriers)).M)).length a'
          (vOf l cr P Cs alg Dexp carriers).nG (vOf l cr P Cs alg Dexp carriers).dig) ∧
      σE.st (sIn D _ _) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
        (carriers.map Stars.Carrier.code) tl) ∧
      σE.st (sSlot D _ _ 0) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ (k : ℕ) (hk : k < 4), σE.st (sSlot D _ _ ⟨k + 1, by omega⟩) =
        tf2OutPorts alg (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
          tl) (Wp + (P.n + 1) ^ 26) Cs ⟨k + 2, by omega⟩) ∧
      σE.st (sSlot D _ _ 5) = PrimAsm.Data.unaryList (PrimThrW.Joins.primesList (vOf l cr P Cs alg Dexp carriers).cut) ∧
      σE.st (sSlot D _ _ 6) = ListEval.levelWord (mpOf (vOf l cr P Cs alg Dexp carriers)).M (mpOf (vOf l cr P Cs alg Dexp carriers)).J (mpOf (vOf l cr P Cs alg Dexp carriers)).W (ListEval.rowsOf (MajorantBits.dataBits (mpOf (vOf l cr P Cs alg Dexp carriers)) s) (mpOf (vOf l cr P Cs alg Dexp carriers)).M) ∧
      σE.st (sSlot D _ _ 7) = PrimAsm.Data.unaryList [a', (vOf l cr P Cs alg Dexp carriers).nG, (vOf l cr P Cs alg Dexp carriers).dig, (mpOf (vOf l cr P Cs alg Dexp carriers)).M] ∧
      σE.st (xsN D _ _ D) = σ.st (xsN D _ _ D) ∧ (∀ r, σE.val r ≤ cap) := by
  have hge := nsL_ge D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x
  have w6Bv : w6B D = 720 + D := by unfold w6B p0B; omega
  have tfBv : tfB D (PrimT.W6.numsW6 alg Dexp).x = 720 + D + (21 + (PrimT.W6.numsW6 alg Dexp).x) := by
    unfold tfB w6B p0B; omega
  have p0Bv : p0B D = 45 + D := rfl
  -- the first docks
  obtain ⟨σ3, sA, fA0, fAw, fAo, shA, valA⟩ := chainA_spec D (PrimThrW.TF3Cost.topFront3 alg).x alg Dexp cap l cr σ P Cs
    (carriers.map Stars.Carrier.code) tl j0 Wp hj0 hIn hx0 hbl hsh hKb ha (by simpa using hnc) hN hn hd hcap1 hok hneed
  have hA : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1),
      (7 ≤ i.val ∧ i.val < 13 + D) → σ3.st i = σ.st i := fun i h => fAo i (Or.inr (Or.inl h))
  have hA2 : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1),
      (13 + D < i.val ∧ i.val < 45 + D) → σ3.st i = σ.st i := fun i h => fAo i (Or.inr (Or.inr (Or.inl h)))
  -- the next docks
  obtain ⟨σ6, sB, fB0, fBs0, fBs, fBo, shB, valB⟩ := chainB_spec D alg Dexp cap jL j1 hjL hj1 σ3 P Cs carriers tl
    (Wp + (P.n + 1) ^ 26) L Wt fA0
    (by rw [show tfMap D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨1, by omega⟩ =
          w6Map D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x ⟨20, by omega⟩ from
          Fin.ext (by rw [tfMap_val, w6Map_val]; simp), fAw 20 (by decide)]
        exact PrimThrW.Nums3.nums3Out_count _ _ _ _ _)
    (by rw [hA _ ⟨by rw [xsN_val D _ _ jL hjL]; omega, by rw [xsN_val D _ _ jL hjL]; omega⟩]; exact hxL)
    (by rw [hA _ ⟨by rw [xsN_val D _ _ j1 hj1]; omega, by rw [xsN_val D _ _ j1 hj1]; omega⟩]; exact hxW)
    (fun i hi => by
      rcases hi with hi | hi
      · rw [fAo i (Or.inl hi)]; exact hbl i (Or.inl ⟨hi.1, by omega⟩)
      · rw [fAo i (Or.inr (Or.inr (Or.inr (by rw [tfBv] at hi; rw [w6Bv]; omega))))]
        exact hbl i (Or.inr ⟨by rw [tfBv] at hi; omega, by rw [tfBv] at hi; omega⟩))
    shA (by rw [valA]; exact hn2) (by rw [valA]; exact hz _ (by decide) (by decide))
    (by rw [valA]; exact hz _ (by decide) (by decide)) (by rw [valA]; exact hz _ (by decide) (by decide))
    hn ha hd hok hnc hL hLX h2 hcN hcA hcK hcx hcy hcu hcapn
  -- the tail
  have tv : ∀ k : Fin 19, (tailSN D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x k).val =
      tailA k + tailB k * D := fun k => rfl
  have wport : ∀ (k : Fin 19) (j : ℕ) (hj : j < 21), tailA k + tailB k * D = w6B D + j → j ≠ 0 → j ≠ 1 → j ≠ 2 →
      j ≠ 17 → j ≠ 20 → σ6.st (tailSN D _ _ k) = nums3OutPorts (PrimAsm.Data.reqW P.n true
        (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) (carriers.map Stars.Carrier.code).length
        (PrimT.TS4.capTL l cr P.n) (Wp + (P.n + 1) ^ 26) (vOf l cr P Cs alg Dexp carriers) ⟨j, hj⟩ := by
    intro k j hj hk h0 h1 h2 h17 h20
    rw [fBo _ (by rw [tv, hk, w6Bv]; omega) (by rw [tv, hk, tfBv, w6Bv]; omega) (by rw [tv, hk, w6Bv, p0Bv]; omega),
      show tailSN D _ _ k = w6Map D _ _ ⟨j, by omega⟩ from
        Fin.ext (by rw [tv, hk, w6Map_val]; simp [h0, h1, h2, h17, h20]),
      fAw j hj]
    simp only [List.length_map]
  have tval : ∀ k : Fin 40, k.val < 39 → (tailRg k).val = 10 + k.val := fun k hk => by rw [tailRg_val, if_pos hk]
  obtain ⟨τ, cT, eT, hcT, fT17, fT18, fTo⟩ := tail_spec cap (tailSN D _ _) tailRg σ6 (mpOf (vOf l cr P Cs alg Dexp carriers)) s pre a' (vOf l cr P Cs alg Dexp carriers).nG (vOf l cr P Cs alg Dexp carriers).dig
    (by rw [show tailSN D _ _ 0 = sIn D _ _ from Fin.ext (by rw [tv]; simp [tailA, tailB, sIn]), fB0, hu])
    (by
      rw [fBo _ (by rw [tv]; simp [tailA, tailB]) (by rw [tv, tfBv]; simp [tailA, tailB]; omega)
          (by rw [tv, p0Bv]; simp [tailA, tailB]; omega),
        hA _ ⟨by rw [tv]; simp [tailA, tailB], by rw [tv]; simp [tailA, tailB]; omega⟩,
        show tailSN D _ _ 1 = sTm D _ _ from Fin.ext (by rw [tv]; simp [tailA, tailB, sTm]), hT])
    (by rw [wport 2 3 (by decide) (by rw [w6Bv]; simp [tailA, tailB]; omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact PrimThrW.Nums3.nums3Out_val _ _ _ _ _ 0)
    (by rw [wport 3 8 (by decide) (by rw [w6Bv]; simp [tailA, tailB]; omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact PrimThrW.Nums3.nums3Out_val _ _ _ _ _ 5)
    (by rw [wport 4 9 (by decide) (by rw [w6Bv]; simp [tailA, tailB]; omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact PrimThrW.Nums3.nums3Out_val _ _ _ _ _ 6)
    (by rw [wport 5 12 (by decide) (by rw [w6Bv]; simp [tailA, tailB]; omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact PrimThrW.Nums3.nums3Out_val _ _ _ _ _ 9)
    (by rw [wport 6 13 (by decide) (by rw [w6Bv]; simp [tailA, tailB]; omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact PrimThrW.Nums3.nums3Out_val _ _ _ _ _ 10)
    (by rw [wport 7 15 (by decide) (by rw [w6Bv]; simp [tailA, tailB]; omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; exact PrimThrW.Nums3.nums3Out_val _ _ _ _ _ 12)
    (by rw [wport 8 18 (by decide) (by rw [w6Bv]; simp [tailA, tailB]; omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; rfl)
    (by rw [wport 9 19 (by decide) (by rw [w6Bv]; simp [tailA, tailB]; omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)]; rfl)
    (fun k hk => by
      rcases tail_hi D k hk with h | h
      · rw [fBo _ (by rw [tv]; omega) (by rw [tv, tfBv]; omega) (by rw [tv, p0Bv]; omega),
          hA2 _ ⟨by rw [tv]; omega, by rw [tv]; omega⟩]
        exact hbl _ (Or.inr ⟨by rw [tv]; omega, by rw [tv]; omega⟩)
      · rw [fBo _ (by rw [tv]; omega) (by rw [tv, tfBv]; omega) (by rw [tv, p0Bv]; omega),
          hA _ ⟨by rw [tv]; omega, by rw [tv]; omega⟩]
        exact hbl _ (Or.inl ⟨by rw [tv]; omega, by rw [tv]; omega⟩))
    shB
    (fun k hk => by rw [valB, valA]; exact hz _ (by rw [tval k hk]; omega) (by rw [tval k hk]; omega))
    (by rw [valB, valA, show tailRg 39 = pR 3 from Fin.ext rfl]; exact ha3)
    hc1 hc2 hc3 hc4 hcapS hcapO hM hJ hc5
  have keep : ∀ i : Fin (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 1),
      (i.val ≤ 6 ∨ i.val = 12 + D) → τ.st i = σ6.st i := fun i hi =>
    fTo i (fun k hk h => by
      have hv := congrArg Fin.val h; rw [tv] at hv
      rcases tail_hi9 D k hk with h' | h' <;> omega)
  refine ⟨τ, _, Step.seq (Step.seq sA sB) (Exec.step (WExec.exec cap eT)), by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keep _ (Or.inl (by simp [sIn])), fB0]
  · rw [keep _ (Or.inl (by simp [sSlot])), fBs0]
  · intro k hk; rw [keep _ (Or.inl (by simp [sSlot]; omega)), fBs k hk]
  · rw [keep _ (Or.inl (by simp [sSlot])), fBo _ (by simp [sSlot]) (by simp [sSlot]; rw [tfBv]; omega)
      (by simp [sSlot, p0Bv]),
      show sSlot D _ _ 5 = w6Map D _ _ ⟨17, by omega⟩ from Fin.ext (by rw [w6Map_val]; simp [sSlot]), fAw 17 (by decide),
      PrimThrW.Nums3.nums3Out_low _ _ _ _ _ ⟨17, by decide⟩]
    rfl
  · rw [show sSlot D _ _ 6 = tailSN D _ _ 17 from Fin.ext (by rw [tv]; simp [tailA, tailB, sSlot])]; exact fT17
  · rw [show sSlot D _ _ 7 = tailSN D _ _ 18 from Fin.ext (by rw [tv]; simp [tailA, tailB, sSlot])]; exact fT18
  · rw [keep _ (Or.inr (xsN_val D _ _ D le_rfl)), fBo _ (by rw [xsN_val D _ _ D le_rfl]; omega)
      (by rw [xsN_val D _ _ D le_rfl, tfBv]; omega) (by rw [xsN_val D _ _ D le_rfl, p0Bv]; omega),
      hA _ ⟨by rw [xsN_val D _ _ D le_rfl]; omega, by rw [xsN_val D _ _ D le_rfl]; omega⟩]
  · exact WExec.val_le cap eT (fun r => by rw [valB, valA]; exact hval r)

end Path

end NearCubicWires.WireExponent3_5.FinalPass.S5T
