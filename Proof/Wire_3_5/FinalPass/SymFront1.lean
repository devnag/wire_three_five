import Proof.Wire_3_5.UnionMachine.NumsA9
import Proof.Wire_3_5.Foundations.OutMachineDataDockW2

/-! # The SYM front, part 1: the data stage with its tapes exported (build once)

`NumsA.dockPost` (the per-call data stage docked on NW's bank `tmapA`, then the counts unframed onto stream
`113`) with `DataW.dataDock_stepW` in place of `DataDock.dataDock_step`, so the data stage's output tapes are
EXPORTED: every filled SYM slot's scan word (`scanWord C_i = natWord C.bottomCount ++ frame (ofFn C.top) ++ tabSeg`,
the top table for SWt) and gate table (`gatesW (tabH G_i) G_i`, for SWg). The proof is the reference one, the request explicit.

* **`dataPostW`**.

Paper quantity of the main type: the SYM call's slices (the circuits' top tables and gate tables, P3:3049-3050) on the
bank's data tapes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g)
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.NumsA

section Gate
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The data stage and the counts onto stream `113`**, the scan words exported (`NumsA.dockPost` with `dataDock_stepW`): at a SYM request, from `PreDock` at `L = W = wOf |fpIn| n`. -/
theorem dataPostW (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (w : List Bool) (hw : w = fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)
    (W : ℕ) (hW : W = wOf w.length n)
    (cap e T : ℕ) (σ : St x)
    (hσ : PreDock x hx w n W e T σ)
    (hc : 2 * W + 2 ≤ cap) :
    ∃ (tout : Fin DataDock.DT → List Bool) (ρ : St x) (c : ℕ),
      Step (DataDock.dataDockM (nr := LNR) (tmapA x hx))
        (Data.symCc * (3 * W + 1) ^ Data.symDc)
        (wenc cap σ).H (wenc cap σ).A
        (wenc cap (DockW.updS (tmapA x hx) σ (fun _ => 0) tout)).H
        (wenc cap (DockW.updS (tmapA x hx) σ (fun _ => 0) tout)).A ∧
      WExec cap (unframeW (tOUT x hx) (sk x 113) (g 0) (g 1)) (DockW.updS (tmapA x hx) σ (fun _ => 0) tout) ρ c ∧
      NumsIn x w (Data.unaryList (countsOf ⟨n, .sym, a', ha', Cs, carriers, translation⟩)) ρ ∧
      ρ.st (sNs x hx) = List.replicate n true ∧ ρ.st (sEs x hx) = List.replicate e true ∧
      ρ.st (sTs x hx) = List.replicate T true ∧ ρ.st (sW0 x) = [] ∧ ρ.st (sW1 x) = [] ∧
      (∀ i, i ≠ sIn x → (ρ.st i).length ≤
        Data.symCc * (3 * W + 1) ^ Data.symDc +
          3 * W + n + e + T + 2) ∧
      (∀ (i : Fin 4) (h : i.val < a'), ρ.st (tmapA x hx (DataDock.iOf (Data.sSym i (PrimT.SymTab.scanSl 0)))) =
        Out.DataW.scanWord (Cs ⟨i.val, h⟩)) ∧
      (∀ (i : Fin 4) (h : i.val < a'), ρ.st (tmapA x hx (DataDock.iSym i)) =
        FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))) ∧
      (∀ i : Fin 4, a' ≤ i.val → ρ.st (tmapA x hx (DataDock.iOf (Data.sSym i (PrimT.SymTab.scanSl 0)))) = []) ∧
      (∀ i, (∀ j, tmapA x hx j ≠ i) → i ≠ sk x 113 → ρ.st i = σ.st i) ∧
      c ≤ 40 * W + 20 := by
  obtain ⟨hk2, hdesc, henv⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation
    hcall
  have hnw0 := FinalPass.FpInLen.n_le_fpIn (l := l) (F := F) (kclk := kclk) (coef := coef) (A := A) (a := a) (ha := ha)
    ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  have hwd : w = fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ := hw
  rw [← hwd] at hnw0
  have hnw : n ≤ w.length := hnw0
  have hWd : W = wOf w.length n := hW
  obtain ⟨P, hPd⟩ : ∃ v, v = (n + 1) ^ 26 := ⟨_, rfl⟩
  have hWe : W = 3 * w.length + 8 * P + 16 := by rw [hWd, hPd]; rfl
  have hP1 : 1 ≤ P := by rw [hPd]; exact Nat.one_le_pow _ _ (by omega)
  -- the request's word
  obtain ⟨tl, htl⟩ : ∃ v, v = RepairRepresentation.natListWord translation ++
      seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .sym, a', ha', Cs, carriers, translation⟩ :=
    ⟨_, rfl⟩
  have a_hw : w = Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl := by
    rw [hwd, htl]; exact (ReqBridge.reqW_word ⟨n, .sym, a', ha', Cs, carriers, translation⟩ _).symm
  have hcodes : ∀ c ∈ Data.symCodes a' Cs, (RepairRepresentation.natWord c).length ≤ w.length := by
    intro c hc'
    have h1 := flat_len RepairRepresentation.natWord _ c hc'
    rw [a_hw]; unfold Data.reqW; simp only [List.length_append]; omega
  have hcc : ∀ y ∈ carriers.map Stars.Carrier.code, (RepairRepresentation.natWord y).length ≤ w.length := by
    intro y hy
    have h1 := flat_len RepairRepresentation.natWord _ y hy
    rw [a_hw]; unfold Data.reqW; simp only [List.length_append, RepairRepresentation.natListWord]; omega
  -- the data stage's hypotheses
  have hL : ∀ i, (Cs i).descriptionBits ≤ W := fun i => by have := hdesc i; rw [← hPd] at this; omega
  have hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ W := fun X hX g hg => by
    have := (henv X hX).2 g hg; rw [← hPd] at this; omega
  have hcx : ∀ c ∈ Data.symCodes a' Cs, 2 * (RepairRepresentation.natWord c).length + 2 + n + W ≤ 2 * W + 2 :=
    fun c hc' => by have := hcodes c hc'; omega
  have hcy : ∀ y ∈ carriers.map Stars.Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + n + W ≤ 2 * W + 2 := fun y hy => by have := hcc y hy; omega
  have hnb := PrimAsm.CopyNat.natBitLength_le_self_succ n
  have hcN : natBitLength n + 1 ≤ 2 * W + 2 := by omega
  have hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2 := by have := PrimT.C4GateSym.nbl_small a' ha'; omega
  have hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2 := by
    have := PrimT.C4GateSym.nbl_small carriers.length (by omega); omega
  have hcx0 : ∀ c ∈ carriers.map (·.length), c ≤ P := by
    intro c hc'
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hc'
    have := (henv X hX).1; rw [← hPd] at this; exact this
  have hxs : (carriers.map (·.length)).sum ≤ 2 * P := by
    have h1 := List.sum_le_card_nsmul (carriers.map (·.length)) P hcx0
    rw [List.length_map, smul_eq_mul] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ hk2)
  have hcy0 : ∀ c ∈ List.ofFn (fun i => (Stars.symGates (Cs i)).length), c ≤ P := by
    intro c hc'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc'
    exact Data.symGates_len_le (Cs i) _ (by rw [hPd]; exact hdesc i)
  have hys : (List.ofFn (fun i => (Stars.symGates (Cs i)).length)).sum ≤ 4 * P := by
    have h1 := List.sum_le_card_nsmul _ P hcy0
    rw [List.length_ofFn, smul_eq_mul] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ ha')
  have hu1 : (Data.unaryList (carriers.map (·.length))).length ≤ 2 * P + 2 := by
    rw [SymDec.unaryList_length_le, List.length_map]; omega
  have hu2 : (Data.unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length ≤ 4 * P + 4 := by
    rw [SymDec.unaryList_length_le, List.length_ofFn]; omega
  have hcu : 2 * (Data.unaryList (carriers.map (·.length))).length +
      2 * (Data.unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2 := by omega
  have eu : countsOf ⟨n, .sym, a', ha', Cs, carriers, translation⟩ =
      carriers.map (·.length) ++ List.ofFn fun i => (Stars.symGates (Cs i)).length := rfl
  have hu : (Data.unaryList (countsOf ⟨n, .sym, a', ha', Cs, carriers, translation⟩)).length ≤ W := by
    rw [eu, SymDec.unaryList_length_le, List.sum_append, List.length_append, List.length_map, List.length_ofFn]
    omega
  -- the data stage's input on the bank
  have v0 := tNT_val x hx
  have v1 := tLT_val x hx
  have v2 := tCT_val x hx
  have vD := DT_val
  have k113 : (sk x 113).val = 113 := rfl
  have k150 : (sk x 150).val = 150 := rfl
  have k1 : (sk x 1).val = 1 := rfl
  have kW0 : (sW0 x).val = 151 := rfl
  have kW1 : (sW1 x).val = 152 := rfl
  have hin : ∀ j, σ.st (tmapA x hx j) =
      DataDock.dataIn (Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n W W j := by
    intro j
    rw [← a_hw]
    by_cases h0 : j.val = 0
    · have hj : j = DataDock.iIN := Fin.ext h0
      subst hj
      have e0 : tmapA x hx DataDock.iIN = sIn x := by unfold tmapA DataDock.nwTmap; rw [if_pos rfl]
      rw [dataIn_iIN, e0, hσ.hin]
    · by_cases h2 : j.val = 2
      · have hj : j = DataDock.iOf Data.sNT := Fin.ext (by rw [h2]; rfl)
        subst hj; rw [dataIn_NT]; exact hσ.hNT
      · by_cases h3 : j.val = 3
        · have hj : j = DataDock.iOf Data.sLT := Fin.ext (by rw [h3]; rfl)
          subst hj; rw [dataIn_LT]; exact hσ.hLT
        · by_cases h4 : j.val = 4
          · have hj : j = DataDock.iOf Data.sCT := Fin.ext (by rw [h4]; rfl)
            subst hj; rw [dataIn_CT]; exact hσ.hCT
          · rw [dataIn_other _ _ _ _ j h0 h2 h3 h4]
            have hjI : j ≠ DataDock.iIN := fun e => h0 (by rw [e]; rfl)
            have hv := tmapA_val x hx j hjI
            have hj := j.isLt
            apply hσ.blank <;> omega
  obtain ⟨tout, hstep, hout, hinw, hsym, -, hlen, hscan, hscan0⟩ := Out.DataW.dataDock_stepW' a' Cs carriers cap (tmapA x hx)
    (tmapA_inj x hx) σ tl W W ha' hk2 hL hLX (by omega) hcN hcA hcK hcx hcy hcu hin (fun j => hσ.heads _)
  -- its steps
  have hK : ∀ i, natBitLength (encodeNormalizedSymmetricThresholdCircuit (Cs i)) ≤ w.length := fun i => by
    have h := hcodes _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [ParseNat.natWord_length] at h; omega
  have hKX : ∀ X ∈ carriers, natBitLength X.code ≤ w.length := fun X hX => by
    have h := hcc X.code (List.mem_map.mpr ⟨X, hX, rfl⟩)
    rw [ParseNat.natWord_length] at h; omega
  have hpoly : 2 * Data.coreCost a' Cs carriers W W + 2 ≤
      Data.symCc * (w.length + n + W + W + 1) ^ Data.symDc :=
    Data.coreCost_poly Cs carriers W W w.length ha' hk2 hL hLX hK hKX (by omega)
  have hmono : (w.length + n + W + W + 1) ^ Data.symDc ≤ (3 * W + 1) ^ Data.symDc :=
    Nat.pow_le_pow_left (by omega) _
  have hstep' := hstep.enlarge (le_trans hpoly (Nat.mul_le_mul_left _ hmono))
  -- the counts onto stream `113`
  have hIm : ∀ i : Fin (LNS x + 1), (∀ j, tmapA x hx j ≠ i) →
      (DockW.updS (tmapA x hx) σ (fun _ => 0) tout).st i = σ.st i :=
    fun i hi => FinalPass.S5T.updS_st_out (tmapA x hx) σ (fun _ => 0) tout i hi
  have hsh0 := FinalPass.S5T.updS_sh0 (tmapA x hx) (tmapA_inj x hx) σ tout hσ.heads
  have n113 : ∀ j, tmapA x hx j ≠ sk x 113 := tmapA_ne x hx _ (by omega) (Or.inl (by omega))
  have hO : (DockW.updS (tmapA x hx) σ (fun _ => 0) tout).st (tOUT x hx) =
      false :: frame (Data.unaryList (countsOf ⟨n, .sym, a', ha', Cs, carriers, translation⟩)) := by
    unfold tOUT
    rw [FinalPass.S5T.updS_st_in (tmapA x hx) (tmapA_inj x hx), hout]
    rfl
  have hC : (DockW.updS (tmapA x hx) σ (fun _ => 0) tout).st (sk x 113) = [] := by
    rw [hIm _ n113]; exact hσ.blank _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  have hOC : tOUT x hx ≠ sk x 113 := fne (by rw [tOUT_val]; omega)
  have eU := unframe_spec cap (tOUT x hx) (sk x 113) (g 0) (g 1) hOC (by decide)
    (Data.unaryList (countsOf ⟨n, .sym, a', ha', Cs, carriers, translation⟩)) _ hO (hsh0 _) hC (hsh0 _)
    (hσ.regs _) (hσ.regs _) (by omega)
  have hsc : ∀ (i : Fin 4) (h : i.val < a'), tmapA x hx (DataDock.iOf (Data.sSym i (PrimT.SymTab.scanSl 0))) ≠ sk x 113 :=
    fun i h => n113 _
  have hsy : ∀ (i : Fin 4), tmapA x hx (DataDock.iSym i) ≠ sk x 113 := fun i => n113 _
  refine ⟨tout, _, _, hstep', eU, ⟨?_, ?_, ?_, ?_, fun i => ?_, fun q => hσ.regs q, hσ.cell⟩, ?_, ?_, ?_, ?_, ?_,
    fun i hi => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i hi h113 => ?_, by omega⟩
  · have n150 : sk x 150 ≠ sk x 113 := fne (by omega)
    have e0 : sk x 150 = tmapA x hx DataDock.iIN := by unfold tmapA DataDock.nwTmap; rw [if_pos rfl]; rfl
    rw [WState.sets_st, Function.update_of_ne n150, e0,
      FinalPass.S5T.updS_st_in (tmapA x hx) (tmapA_inj x hx), hinw, ← a_hw]
  · have n1 : sk x 1 ≠ sk x 113 := fne (by omega)
    rw [WState.sets_st, Function.update_of_ne n1, hIm _ (tmapA_ne x hx _ (by omega) (Or.inl (by omega)))]
    exact hσ.h1
  · rw [WState.sets_st, Function.update_self]
  · intro j a0 a1 a2
    have hj := j.isLt
    have nj : sk x j ≠ sk x 113 := fne (by show j.val ≠ 113; exact a2)
    rw [WState.sets_st, Function.update_of_ne nj,
      hIm _ (tmapA_ne x hx _ (by show j.val ≠ 150; exact a0) (Or.inl (by show j.val < 161; omega)))]
    exact hσ.blank _ (by show j.val ≠ 150; exact a0) (by show j.val ≠ 163; omega) (by show j.val ≠ 164; omega)
      (by show j.val ≠ 165; omega) (by show j.val ≠ 10063; omega) (by show j.val ≠ 10064; omega)
      (by show j.val ≠ 10065; omega) (by show j.val ≠ 1; exact a1)
  · rw [WState.sets_sh]; exact hsh0 i
  · have ne : sNs x hx ≠ sk x 113 := fne (by rw [sNs_val]; omega)
    rw [WState.sets_st, Function.update_of_ne ne,
      hIm _ (tmapA_ne x hx _ (by rw [sNs_val]; omega) (Or.inr (by rw [sNs_val])))]
    exact hσ.hSN
  · have ne : sEs x hx ≠ sk x 113 := fne (by rw [sEs_val]; omega)
    rw [WState.sets_st, Function.update_of_ne ne,
      hIm _ (tmapA_ne x hx _ (by rw [sEs_val]; omega) (Or.inr (by rw [sEs_val]; omega)))]
    exact hσ.hSE
  · have ne : sTs x hx ≠ sk x 113 := fne (by rw [sTs_val]; omega)
    rw [WState.sets_st, Function.update_of_ne ne,
      hIm _ (tmapA_ne x hx _ (by rw [sTs_val]; omega) (Or.inr (by rw [sTs_val]; omega)))]
    exact hσ.hST
  · have ne : sW0 x ≠ sk x 113 := fne (by omega)
    rw [WState.sets_st, Function.update_of_ne ne,
      hIm _ (tmapA_ne x hx _ (by omega) (Or.inl (by omega)))]
    exact hσ.blank _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have ne : sW1 x ≠ sk x 113 := fne (by omega)
    rw [WState.sets_st, Function.update_of_ne ne,
      hIm _ (tmapA_ne x hx _ (by omega) (Or.inl (by omega)))]
    exact hσ.blank _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · -- the residue
    have hpo : (w.length + n + W + W + 1) ^ Data.symDc ≤ (3 * W + 1) ^ Data.symDc := hmono
    by_cases h113 : i = sk x 113
    · subst h113
      rw [WState.sets_st, Function.update_self]
      omega
    · rw [WState.sets_st, Function.update_of_ne h113]
      by_cases hI : ∃ j, tmapA x hx j = i
      · obtain ⟨j, rfl⟩ := hI
        rw [FinalPass.S5T.updS_st_in (tmapA x hx) (tmapA_inj x hx)]
        have hl := hlen j
        unfold DataDock.dataB at hl
        rw [← a_hw] at hl
        have := le_trans hpoly (Nat.mul_le_mul_left Data.symCc hmono)
        omega
      · have hni : ∀ j, tmapA x hx j ≠ i := fun j e => hI ⟨j, e⟩
        rw [hIm _ hni]
        have hvI : i.val ≠ 150 := fun e => hi (Fin.ext e)
        have h163 : i.val ≠ 163 := fun e => hni (DataDock.iOf Data.sNT) (Fin.ext (by rw [e]; exact v0))
        have h164 : i.val ≠ 164 := fun e => hni (DataDock.iOf Data.sLT) (Fin.ext (by rw [e]; exact v1))
        have h165 : i.val ≠ 165 := fun e => hni (DataDock.iOf Data.sCT) (Fin.ext (by rw [e]; exact v2))
        by_cases hN : i = sNs x hx
        · subst hN; rw [hσ.hSN, List.length_replicate]; omega
        · by_cases hE : i = sEs x hx
          · subst hE; rw [hσ.hSE, List.length_replicate]; omega
          · by_cases hT : i = sTs x hx
            · subst hT; rw [hσ.hST, List.length_replicate]; omega
            · by_cases h1 : i = sk x 1
              · subst h1; rw [hσ.h1]; simp
              · rw [hσ.blank i hvI h163 h164 h165 (fun e => hN (Fin.ext (by rw [e, sNs_val, vD])))
                  (fun e => hE (Fin.ext (by rw [e, sEs_val, vD]))) (fun e => hT (Fin.ext (by rw [e, sTs_val, vD])))
                  (fun e => h1 (Fin.ext e))]
                simp
  · rw [WState.sets_st, Function.update_of_ne (hsc i h), FinalPass.S5T.updS_st_in (tmapA x hx) (tmapA_inj x hx)]
    exact hscan i h
  · rw [WState.sets_st, Function.update_of_ne (hsy i), FinalPass.S5T.updS_st_in (tmapA x hx) (tmapA_inj x hx)]
    exact hsym i h
  · rw [WState.sets_st, Function.update_of_ne (n113 _), FinalPass.S5T.updS_st_in (tmapA x hx) (tmapA_inj x hx)]
    exact hscan0 i h
  · rw [WState.sets_st, Function.update_of_ne h113]
    exact hIm i hi

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFront
