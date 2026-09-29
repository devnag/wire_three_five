import Proof.Wire_3_5.UnionMachine.NumsA9

/-! # SWg, part 1: the data stage's gate tables on NW's bank, the inactive slots fixed

The call words of kind `0` (`PrimT.S3.wordOf k 0 j`, the SYM slots `16 … 19`) are the gate tables
`Corner.gatesW (tabH G_j) G_j` of the bottom gates `G_j = gatesJ k j` (`[]` past the tuple, the word `[false]`). PA's data
stage leaves exactly these tables on its slot tapes `iSym j` for `j < a` and blank tapes past the tuple
(`data_step_blank`); a gate word starts with the marker `true`, so one test fixes the blank ones to `[false]`:

* **`dataDock_step2`** (`DataDock.dataDock_step` with the blank slots kept), `fix1`, **`fix1_spec`**, **`dockG`** (at a
  SYM request, from `PreDock`: the docked run, the tables `if j < a then gatesW … else []`, the request kept, the
  tapes' lengths).

Paper quantities of the main type: the SYM call's bottom gates' tables (P3:3049-3050; `symWords`, kind `0`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g)

section Dock
open NearCubicWires.WireExponent3_5.UnionMachine.DataDock NearCubicWires.WireExponent3_5.PrimAsm.Data
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **`dataDock`, with the blank slots**: `DataDock.dataDock_step` and the slot tapes past the tuple blank. -/
theorem dataDock_step2 {ns nr : ℕ} (cap : ℕ) (tmap : Fin DT → Fin (ns + 1)) (hinj : Function.Injective tmap)
    (σ : WState ns nr) (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2)
    (hcu : 2 * (unaryList (carriers.map (·.length))).length +
      2 * (unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2)
    (hin : ∀ j, σ.st (tmap j) = dataIn (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W j)
    (hh : ∀ j, σ.sh (tmap j) = 0) :
    ∃ tout : Fin DT → List Bool,
      Step (dataDockM (nr := nr) tmap) (2 * coreCost a' Cs carriers L W + 2) (wenc cap σ).H (wenc cap σ).A
        (wenc cap (DockW.updS tmap σ (fun _ => 0) tout)).H (wenc cap (DockW.updS tmap σ (fun _ => 0) tout)).A ∧
      tout iIN = RepairOrdinary.frame (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (iSym i) =
        FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))) ∧
      (∀ i : Fin 4, a' ≤ i.val → tout (iSym i) = []) ∧
      (∀ j, (tout j).length ≤ dataB (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W
        Cs carriers) := by
  obtain ⟨tout0, m, hs, -, hi, hS, -, hSb, -⟩ := data_step_blank a' Cs carriers tl L W ha hk hL hLX h2 hcN hcA hcK
    hcx hcy hcu
  obtain ⟨w, hwd⟩ : ∃ v, v = reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl := ⟨_, rfl⟩
  rw [← hwd] at hs hi hin ⊢
  have e1 : (fun j => σ.sh (tmap j)) = fun _ => 0 := funext hh
  have e2 : (fun j => σ.st (tmap j)) = dataIn w n L W := funext hin
  have hs' : Step dataM (2 * coreCost a' Cs carriers L W + 2) (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j))
      (fun _ => 0) (Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false)) := by
    rw [e1, e2]; exact hs
  refine ⟨Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false), DockW.dockS cap tmap hinj σ hs', ?_,
    fun i h => ?_, fun i h => ?_, ?_⟩
  · unfold iIN iOf; beta_reduce; rw [Fin.addCases_left]; exact hi
  · unfold iSym iOf; beta_reduce; rw [Fin.addCases_left]; exact hS i h
  · unfold iSym iOf; beta_reduce; rw [Fin.addCases_left]; exact hSb i h
  · intro j
    have hl := Shell.Step.len hs j (2 * w.length + n + L + W + 1) (Nat.zero_le _)
      (by have := dataIn_len w n L W j; unfold dataIn at this; exact this)
    unfold dataB
    beta_reduce
    omega

end Dock

section Fix
variable {ns nr : ℕ} (cap : ℕ)

/-- A blank slot tape to `[false]` (a gate word starts with the marker `true`). -/
def fix1 (O : Fin (ns + 1)) : WM ns nr := .ifs O .skip (.wr O false)

theorem fix1_spec (O : Fin (ns + 1)) (σ : WState ns nr) (hh : σ.sh O = 0) (h : ℕ) {n : ℕ}
    (G : List (NormalizedThresholdGate n))
    (hO : σ.st O = FinalPass.Corner.gatesW h G ∨ (σ.st O = [] ∧ G = [])) :
    WExec cap (fix1 O) σ (σ.sets O (FinalPass.Corner.gatesW h G)) 2 := by
  cases G with
  | nil =>
    have hw : FinalPass.Corner.gatesW h ([] : List (NormalizedThresholdGate n)) = [false] := rfl
    have hb : wbit σ O = false := by
      unfold wbit; rw [hh]
      rcases hO with h1 | ⟨h1, -⟩ <;> rw [h1] <;> [rw [hw]; skip] <;> rfl
    have e := WExec.wr (cap := cap) O false σ
    have hst : writeTapeBit (σ.st O) (σ.sh O) false = [false] := by
      rw [hh]; rcases hO with h1 | ⟨h1, -⟩ <;> rw [h1] <;> [rw [hw]; skip] <;> rfl
    rw [hst] at e
    rw [hw]
    exact WExec.ifsF hb e
  | cons g G =>
    have h1 : σ.st O = FinalPass.Corner.gatesW h (g :: G) := by
      rcases hO with h1 | ⟨-, h2⟩
      · exact h1
      · exact absurd h2 (List.cons_ne_nil g G)
    have hb : wbit σ O = true := by
      unfold wbit; rw [hh, h1]; rfl
    rw [← h1, wsets_same]
    exact WExec.mono (WExec.ifsT hb (WExec.skip σ)) (by omega)

end Fix

section Gate
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The data stage's tables at a SYM request**, from `PreDock` at `L = W = wOf |fpIn| n`. -/
theorem dockG (x : ℕ) (hx : DataDock.DT + 3 ≤ x) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (cap e T : ℕ) (σ : St x)
    (hσ : PreDock x hx (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) n (wOf (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length n) e T σ) :
    ∃ tout : Fin DataDock.DT → List Bool,
      Step (DataDock.dataDockM (nr := LNR) (tmapA x hx))
        (Data.symCc * (3 * wOf (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length n + 1) ^ Data.symDc)
        (wenc cap σ).H (wenc cap σ).A
        (wenc cap (DockW.updS (tmapA x hx) σ (fun _ => 0) tout)).H
        (wenc cap (DockW.updS (tmapA x hx) σ (fun _ => 0) tout)).A ∧
      tout DataDock.iIN = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) ∧
      (∀ j : Fin 4, ∀ h : j.val < a', tout (DataDock.iSym j) =
        FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨j.val, h⟩))) (Stars.symGates (Cs ⟨j.val, h⟩))) ∧
      (∀ j : Fin 4, a' ≤ j.val → tout (DataDock.iSym j) = []) ∧
      (∀ j, (tout j).length ≤ Data.symCc * (3 * wOf (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length n + 1) ^ Data.symDc +
        3 * wOf (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length n) := by
  obtain ⟨hk2, hdesc, henv⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation
    hcall
  have hnw0 := FinalPass.FpInLen.n_le_fpIn (l := l) (F := F) (kclk := kclk) (coef := coef) (A := A) (a := a) (ha := ha)
    ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  obtain ⟨w, hwd⟩ : ∃ v, v = fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ :=
    ⟨_, rfl⟩
  rw [← hwd] at hσ hnw0 ⊢
  have hnw : n ≤ w.length := hnw0
  obtain ⟨W, hWd⟩ : ∃ v, v = wOf w.length n := ⟨_, rfl⟩
  rw [← hWd] at hσ ⊢
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
  obtain ⟨tout, hstep, hinw, hS, hSb, hlen⟩ := dataDock_step2 a' Cs carriers cap (tmapA x hx)
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
  refine ⟨tout, hstep', by rw [hinw, ← a_hw], hS, hSb, fun j => ?_⟩
  have hl := hlen j
  unfold DataDock.dataB at hl
  rw [← a_hw] at hl
  have := le_trans hpoly (Nat.mul_le_mul_left Data.symCc hmono)
  omega

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
