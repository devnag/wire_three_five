import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymS

/-! # G2, the SYM gate-frame writer, part 3: the run (P3:1655-1664, 3119-3120)

"For a common pool over all `2^k` rows and polynomially many original atoms" (P3:1662-1663): the SYM call's pool is
`Records.symPool Cs carriers` (each carrier's doubled atoms, then each circuit's bottoms). This part
runs part 2's stages from the request word:

* the six slots `gsG` (a blank slot for an absent carrier or circuit), their widths `gsH`, the bound `gsHs`;
  **`symPool_eq`**: the pool is the slots' concatenation; `mask_GB` (a carrier's width bounds its negated atoms);
  `slot_T`, `slot_H` (the data stage's tables meet the converter's hypotheses);
* `writerRun_of_step` (a zero-head step to a writer's run, residues by `one_tape_support`);
* **`gs_run`**: `WriterRun (gsM Dv Cv) Bud (gsIn Dv) (gsOut Dv) w (C4Geo.gateField (Records.symPool Cs carriers))`
  for `w = Data.reqW n false (symCodes a' Cs) (carriers.map code) tl` under the data stage's hypotheses at
  `L = W = UnaryCalc.value Dv Cv n` and `2·gsCost + 2 ≤ Bud`.

Paper quantity of the main type: C3a's gate field of the call's pool. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4GateSym
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront NearCubicWires.SupplierPipeline

/-! ## Lists -/

theorem flat2 {α : Type} (l : List (List α)) (h : l.length ≤ 2) : l.flatten = l.getD 0 [] ++ l.getD 1 [] := by
  match l, h with
  | [], _ => rfl
  | [a], _ => simp
  | [a, b], _ => simp
  | _ :: _ :: _ :: l, h => simp only [List.length_cons] at h; omega

theorem flat4 {α : Type} (l : List (List α)) (h : l.length ≤ 4) :
    l.flatten = l.getD 0 [] ++ l.getD 1 [] ++ l.getD 2 [] ++ l.getD 3 [] := by
  match l, h with
  | [], _ => rfl
  | [a], _ => simp
  | [a, b], _ => simp
  | [a, b, c], _ => simp
  | [a, b, c, d], _ => simp [List.append_assoc]
  | _ :: _ :: _ :: _ :: _ :: l, h => simp only [List.length_cons] at h; omega

theorem allJ_flatMap {β : Type} (f : Fin 6 → List β) : allJ.flatMap f = f 0 ++ f 1 ++ f 2 ++ f 3 ++ f 4 ++ f 5 := by
  simp [allJ, List.append_assoc]

/-! ## The slots -/

section Slots
variable {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **The converter's slot `j`**: the carriers' doubled atoms (slots `0, 1`), then the circuits' bottoms (`2 … 5`);
blank when the carrier or circuit is absent. -/
def gsG (j : Fin 6) : List (NormalizedThresholdGate n) :=
  if j.val < 2 then (carriers.map FinalPass.Corner.maskGates).getD j.val []
  else (List.ofFn fun i => Stars.symGates (Cs i)).getD (j.val - 2) []

/-- The slot's table width (`1` for a blank slot). -/
def gsH (j : Fin 6) : ℕ :=
  if j.val < 2 then (carriers.map fun X => max 1 (PrimT.tabH X)).getD j.val 1
  else (List.ofFn fun i => max 1 (PrimT.tabH (Stars.symGates (Cs i)))).getD (j.val - 2) 1

/-- A bound for every slot's width: their sum. -/
def gsHs : ℕ :=
  gsH Cs carriers 0 + gsH Cs carriers 1 + gsH Cs carriers 2 + gsH Cs carriers 3 + gsH Cs carriers 4 +
    gsH Cs carriers 5

theorem gsG_car (j : Fin 6) (h : j.val < 2) (hk : j.val < carriers.length) :
    gsG Cs carriers j = FinalPass.Corner.maskGates (carriers.get ⟨j.val, hk⟩) := by
  unfold gsG
  rw [if_pos h, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map]
  rfl

theorem gsH_car (j : Fin 6) (h : j.val < 2) (hk : j.val < carriers.length) :
    gsH Cs carriers j = max 1 (PrimT.tabH (carriers.get ⟨j.val, hk⟩)) := by
  unfold gsH
  rw [if_pos h, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map]
  rfl

theorem gsG_carE (j : Fin 6) (h : j.val < 2) (hk : carriers.length ≤ j.val) : gsG Cs carriers j = [] := by
  unfold gsG
  rw [if_pos h, List.getD_eq_default _ _ (by rw [List.length_map]; exact hk)]

theorem gsH_carE (j : Fin 6) (h : j.val < 2) (hk : carriers.length ≤ j.val) : gsH Cs carriers j = 1 := by
  unfold gsH
  rw [if_pos h, List.getD_eq_default _ _ (by rw [List.length_map]; exact hk)]

theorem gsG_sym (j : Fin 6) (h : ¬j.val < 2) (hi : j.val - 2 < a') :
    gsG Cs carriers j = Stars.symGates (Cs ⟨j.val - 2, hi⟩) := by
  unfold gsG
  rw [if_neg h, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]

theorem gsH_sym (j : Fin 6) (h : ¬j.val < 2) (hi : j.val - 2 < a') :
    gsH Cs carriers j = max 1 (PrimT.tabH (Stars.symGates (Cs ⟨j.val - 2, hi⟩))) := by
  unfold gsH
  rw [if_neg h, List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]

theorem gsG_symE (j : Fin 6) (h : ¬j.val < 2) (hi : a' ≤ j.val - 2) : gsG Cs carriers j = [] := by
  unfold gsG
  rw [if_neg h, List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact hi)]

theorem gsH_symE (j : Fin 6) (h : ¬j.val < 2) (hi : a' ≤ j.val - 2) : gsH Cs carriers j = 1 := by
  unfold gsH
  rw [if_neg h, List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact hi)]

/-- **The call's pool is the six slots' concatenation.** -/
theorem symPool_eq (ha : a' ≤ 4) (hk : carriers.length ≤ 2) :
    PrimAsm.Records.symPool Cs carriers = allJ.flatMap (gsG Cs carriers) := by
  unfold PrimAsm.Records.symPool PrimAsm.Records.symSlices
  rw [List.flatten_append, flat2 _ (by rw [List.length_map]; exact hk),
    flat4 _ (by rw [List.length_ofFn]; exact ha), allJ_flatMap]
  simp only [List.append_assoc] <;> rfl

end Slots

/-! ## Widths -/

theorem tabH_pos' {n : ℕ} (G : List (NormalizedThresholdGate n)) (hG : G ≠ []) : 1 ≤ PrimT.tabH G := by
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil G hG
  exact (C4Gates.table_bounds G g hg).1

theorem mask_pos {n : ℕ} (X : Stars.Carrier n) (hX : FinalPass.Corner.maskGates X ≠ []) : 1 ≤ PrimT.tabH X := by
  apply tabH_pos'
  intro e
  apply hX
  rw [e]
  rfl

theorem gatesW_max1 {n : ℕ} (h : ℕ) (G : List (NormalizedThresholdGate n)) (hG : G ≠ [] → 1 ≤ h) :
    FinalPass.Corner.gatesW (max 1 h) G = FinalPass.Corner.gatesW h G := by
  by_cases e : G = []
  · subst e
    rfl
  · rw [max_eq_right (hG e)]

/-- **A carrier's width bounds its doubled atoms** (the negated atom `⟨−w, 1−θ⟩`, `negGate`). -/
theorem mask_GB {n : ℕ} (X : Stars.Carrier n) (g : NormalizedThresholdGate n)
    (hg : g ∈ FinalPass.Corner.maskGates X) : C4Gates.GB (PrimT.tabH X) g := by
  unfold FinalPass.Corner.maskGates at hg
  rw [List.mem_flatMap] at hg
  obtain ⟨g0, hg0, hm⟩ := hg
  obtain ⟨hw, ht, hn⟩ := PrimT.tab_nbl_le X g0 hg0
  have h1 := PrimT.one_le_nbl n
  have hlt : ∀ v : ℕ, natBitLength v + 1 ≤ PrimT.tabH X → v < 2 ^ (PrimT.tabH X - 1) := by
    intro v hv
    have a1 := CompilerMachine.Pool.lt_pow_natBitLength v
    have a2 : 2 ^ natBitLength v ≤ 2 ^ (PrimT.tabH X - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : 2 * 2 ^ (PrimT.tabH X - 1) = 2 ^ PrimT.tabH X := by
    rw [← pow_succ']
    congr 1
    omega
  have h4 : 2 ≤ 2 ^ (PrimT.tabH X - 1) := by
    have : 2 ^ 1 ≤ 2 ^ (PrimT.tabH X - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hθ := hlt _ ht
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · refine ⟨fun i => ?_, ?_, ?_⟩
    · have := hlt _ (hw i)
      omega
    · omega
    · omega
  · refine ⟨fun i => ?_, ?_, ?_⟩
    · have := hlt _ (hw i)
      show (-(g0.weight i)).natAbs < _
      omega
    · show (1 - g0.threshold - 1).natAbs + 1 < _
      omega
    · show (1 - g0.threshold).natAbs < _
      omega

section Tables
variable {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **The data stage's tables are the converter's slots** (a blank slot's table is blank). -/
theorem slot_T (tout : Fin (PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) → List Bool)
    (f1 : ∀ i : Fin 4, ∀ h : i.val < a', tout (sTape (PrimAsm.Data.sSym i 3)) =
      FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩)))
    (f2 : ∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (PrimAsm.Data.sCar k 3)) =
      FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
        (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩)))
    (f3 : ∀ i : Fin 4, a' ≤ i.val → tout (sTape (PrimAsm.Data.sSym i 3)) = [])
    (f4 : ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (PrimAsm.Data.sCar k 3)) = []) (j : Fin 6) :
    tout (sTape (tabStream j)) = FinalPass.Corner.gatesW (gsH Cs carriers j) (gsG Cs carriers j) ∨
      (tout (sTape (tabStream j)) = [] ∧ gsG Cs carriers j = []) := by
  by_cases h : j.val < 2
  · have et : tabStream j = PrimAsm.Data.sCar ⟨j.val, h⟩ 3 := by unfold tabStream; rw [dif_pos h]
    rw [et]
    by_cases hk : j.val < carriers.length
    · left
      rw [f2 ⟨j.val, h⟩ hk, gsG_car Cs carriers j h hk, gsH_car Cs carriers j h hk,
        gatesW_max1 _ _ (mask_pos _)]
    · right
      exact ⟨f4 ⟨j.val, h⟩ (by show carriers.length ≤ j.val; omega), gsG_carE Cs carriers j h (by omega)⟩
  · have et : tabStream j = PrimAsm.Data.sSym ⟨j.val - 2, by omega⟩ 3 := by unfold tabStream; rw [dif_neg h]
    rw [et]
    by_cases hi : j.val - 2 < a'
    · left
      rw [f1 ⟨j.val - 2, by omega⟩ hi, gsG_sym Cs carriers j h hi, gsH_sym Cs carriers j h hi,
        gatesW_max1 _ _ (tabH_pos' _)]
    · right
      exact ⟨f3 ⟨j.val - 2, by omega⟩ (by show a' ≤ j.val - 2; omega), gsG_symE Cs carriers j h (by omega)⟩

/-- **The widths meet the converter's bounds.** -/
theorem slot_H (j : Fin 6) : 1 ≤ gsH Cs carriers j ∧ gsH Cs carriers j ≤ gsHs Cs carriers ∧
    ∀ g ∈ gsG Cs carriers j, C4Gates.GB (gsH Cs carriers j) g := by
  have hle : gsH Cs carriers j ≤ gsHs Cs carriers := by
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by revert j; decide
    unfold gsHs
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  refine ⟨?_, hle, ?_⟩
  · by_cases h : j.val < 2
    · by_cases hk : j.val < carriers.length
      · rw [gsH_car Cs carriers j h hk]; exact le_max_left _ _
      · rw [gsH_carE Cs carriers j h (by omega)]
    · by_cases hi : j.val - 2 < a'
      · rw [gsH_sym Cs carriers j h hi]; exact le_max_left _ _
      · rw [gsH_symE Cs carriers j h (by omega)]
  · intro g hg
    by_cases h : j.val < 2
    · by_cases hk : j.val < carriers.length
      · rw [gsG_car Cs carriers j h hk] at hg
        rw [gsH_car Cs carriers j h hk, max_eq_right (mask_pos _ (List.ne_nil_of_mem hg))]
        exact mask_GB _ g hg
      · rw [gsG_carE Cs carriers j h (by omega)] at hg
        exact absurd hg List.not_mem_nil
    · by_cases hi : j.val - 2 < a'
      · rw [gsG_sym Cs carriers j h hi] at hg
        rw [gsH_sym Cs carriers j h hi, max_eq_right (tabH_pos' _ (List.ne_nil_of_mem hg))]
        exact C4Gates.GB_tabH _ g hg
      · rw [gsG_symE Cs carriers j h (by omega)] at hg
        exact absurd hg List.not_mem_nil

end Tables

/-! ## The writer's run -/

/-- **A zero-head step is a writer's run**: the request kept on `i`, the word `v` on `o`, the residues within the
step bound (`one_tape_support`). -/
theorem writerRun_of_step {t s : ℕ} {p : Machine t s} {N Bud : ℕ} {i o : Fin t} {w v : List Bool}
    {Tf : Fin t → List Bool} (h : Step p N (fun _ => 0) (PrimAsm.WriterIface.inBank i w) (fun _ => 0) Tf)
    (hi : Tf i = frame w) (ho : Tf o = v) (hio : i ≠ o) (hN : N ≤ Bud) :
    PrimAsm.WriterIfaceJ.WriterRun p Bud i o w v := by
  have hstep := h.enlarge hN
  have hlen : ∀ (t s n' : ℕ) (p : Machine t s) (hi ho : Fin t → ℕ) (ti tf : Fin t → List Bool),
      Step p n' hi ti ho tf → ∀ i k, hi i ≤ k → (ti i).length ≤ k → (tf i).length ≤ k + n' := by
    intro t s n' p hi ho ti tf h i k hh ht
    obtain ⟨r, hr, _, hT, _⟩ := h
    have := DecompositionSource.one_tape_support p n' ⟨p.start, hi, ti⟩ r i k hr hh ht
    rw [hT] at this
    omega
  refine ⟨fun j => if j = i ∨ j = o then [] else Tf j, ?_, ?_⟩
  · intro j
    by_cases hj : j = i ∨ j = o
    · simp [hj]
    · have hin : j ≠ i := fun e => hj (Or.inl e)
      have := hlen _ _ _ _ _ _ _ _ hstep j 0 (le_refl _) (by simp [PrimAsm.WriterIface.inBank, hin])
      simp only [hj, if_false]
      omega
  · have eo : Tf = PrimAsm.WriterIfaceJ.outBankJ i o w v (fun j => if j = i ∨ j = o then [] else Tf j) := by
      funext j
      unfold PrimAsm.WriterIfaceJ.outBankJ
      by_cases hj : j = i
      · subst hj
        simp [hi]
      · by_cases hjo : j = o
        · subst hjo
          simp [hj, ho]
        · simp [hj, hjo]
    rw [← eo]
    obtain ⟨r, hr, hH, hT, hs⟩ := hstep
    exact ⟨r, hr, hT, fun k => by rw [hH], hs⟩

/-- The writer's steps before the teardown: the front, the copy, the data stage (`DC` steps), the converter. -/
def gsCost (w : List Bool) (n Dv Cv DC P H : ℕ) : ℕ :=
  frontC w n Dv Cv + 1 + (2 * (UnaryCalc.value Dv Cv n * 7 + 1 + 1 + (n * 7 + 1)) + 2) + 1 + DC + 1 +
    (2 * C4Gates.convCost n P H + 2)

theorem gsA0_in {Dv : ℕ} (w : List Bool) :
    (Fin.addCases (gsA0 (Dv := Dv) w) (fun _ : Fin 1 => List.replicate 0 false) : Fin (GT Dv + 1) → List Bool) =
      PrimAsm.WriterIface.inBank (gsIn Dv) w := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun u => ?_) i
  · by_cases ha : a = gl (ws gIN)
    · subst ha
      simp [gsA0, PrimAsm.WriterIface.inBank, gsIn]
    · have hne : Fin.castAdd 1 a ≠ gsIn Dv := fun e => ha (Fin.castAdd_injective _ _ e)
      simp [gsA0, PrimAsm.WriterIface.inBank, ha, hne]
  · have hne : Fin.natAdd (GT Dv) u ≠ gsIn Dv := by
      intro e
      have := congrArg Fin.val e
      simp only [Fin.val_natAdd, gsIn, Fin.val_castAdd] at this
      have := (gl (Dv := Dv) (ws gIN)).isLt
      omega
    simp [PrimAsm.WriterIface.inBank, hne]

/-- **The SYM gate-frame writer's run**: from `frame w` (`w` the SYM request word's shape), the output port holds
C3a's gate field of the call's pool, the request kept, within `2·gsCost + 2` steps. -/
theorem gs_run (Dv Cv Bud n a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (tl : List Bool) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (W : ℕ) (hW : UnaryCalc.value Dv Cv n = W)
    (hL : ∀ i, (Cs i).descriptionBits ≤ W) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ W)
    (h2 : 2 ≤ n + W)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ PrimAsm.Data.symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + W ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + n + W ≤ 2 * W + 2)
    (hcu : 2 * (PrimAsm.Data.unaryList (carriers.map (·.length))).length +
      2 * (PrimAsm.Data.unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2)
    (hB : 2 * gsCost (PrimAsm.Data.reqW n false (PrimAsm.Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
      n Dv Cv (2 * PrimAsm.Data.coreCost a' Cs carriers W W + 2) (PrimAsm.Records.symPool Cs carriers).length
      (gsHs Cs carriers) + 2 ≤ Bud) :
    PrimAsm.WriterIfaceJ.WriterRun (gsM Dv Cv) Bud (gsIn Dv) (gsOut Dv)
      (PrimAsm.Data.reqW n false (PrimAsm.Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
      (C4Geo.gateField (PrimAsm.Records.symPool Cs carriers)) := by
  obtain ⟨w, hwd⟩ : ∃ x, x = PrimAsm.Data.reqW n false (PrimAsm.Data.symCodes a' Cs)
      (carriers.map Stars.Carrier.code) tl := ⟨_, rfl⟩
  rw [← hwd] at hB ⊢
  have hsfx : w = RepairRepresentation.natWord n ++ ([false] ++
      RepairRepresentation.natWord (PrimAsm.Data.symCodes a' Cs).length ++
      (PrimAsm.Data.symCodes a' Cs).flatMap RepairRepresentation.natWord ++
      RepairRepresentation.natListWord (carriers.map Stars.Carrier.code) ++ tl) := by
    rw [hwd]
    unfold PrimAsm.Data.reqW
    simp only [List.append_assoc]
  have hG : 16 ≤ GLt Dv := by show 16 ≤ 78 + (14 + (14 + 2 * Dv)); omega
  have hDT : DT = 9902 := rfl
  -- 1: the front
  obtain ⟨E1, s1, e1in, e1nt, e1ct, e1z⟩ := front_stage (Dv := Dv) Cv n w _ hsfx
  rw [hW] at e1ct
  -- 2: the copy
  obtain ⟨K', s2, e2lt, e2ns, e2ct, e2nt⟩ := copy_step E1 n W e1ct e1nt
    (e1z _ (by rw [dReg_val]; omega)) (e1z _ (by rw [cReg_val]; omega)) (fun c => e1z _ (by rw [kReg_val]; omega))
  have e2in : install kS E1 K' (gl (ws gIN)) = frame w := by
    rw [install_other _ _ _ _ (kS_ne _ (by rw [gl_val, ws_IN]; omega) (by rw [gl_val, ws_IN]; omega)
      (by rw [gl_val, ws_IN]; omega) (Or.inl (by rw [gl_val, ws_IN]; omega)) (by rw [gl_val, ws_IN]; omega)), e1in]
  have e2z : ∀ d : Fin DT, d.val ≠ 3 → install kS E1 K' (dReg d) = [] := by
    intro d hd
    have := d.isLt
    rw [install_other _ _ _ _ (kS_ne _ (by rw [dReg_val]; omega) (by rw [dReg_val]; omega)
      (by rw [dReg_val]; omega) (Or.inl (by rw [dReg_val]; omega)) (by rw [dReg_val]; omega)),
      e1z _ (by rw [dReg_val]; omega)]
  have e2c : ∀ x : Fin 34, x.val ≠ 11 → install kS E1 K' (cReg x) = [] := by
    intro x hx
    rw [install_other _ _ _ _ (kS_ne _ (by rw [cReg_val]; omega) (by rw [cReg_val]; omega)
      (by rw [cReg_val]; omega) (Or.inr (by rw [cReg_val]; omega)) (by rw [cReg_val]; omega)),
      e1z _ (by rw [cReg_val]; omega)]
  -- 3: the data stage
  obtain ⟨tout, m, sD, _, t_in, f1, f2, f3, f4⟩ := PrimAsm.Data.data_step_blank a' Cs carriers tl W W ha hk hL hLX h2
    hcN hcA hcK hcx hcy hcu
  rw [← hwd] at sD t_in
  have s3 := data_stage (install kS E1 K') w n W _ m tout sD e2in e2nt e2lt e2ct e2z
  obtain ⟨a1, a2, a3⟩ := data_after (install kS E1 K') (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false))
  -- 4: the converter
  obtain ⟨E4, s4, e4o, e4k⟩ := conv_stage
    (install dS (install kS E1 K') (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false))) n
    (gsHs Cs carriers) (gsG Cs carriers) (gsH Cs carriers)
    (by rw [a3, e2ns]) (fun x hx => by rw [a3]; exact e2c x hx)
    (fun j => by rw [a2, addCases_dPos]; exact slot_T Cs carriers tout f1 f2 f3 f4 j)
    (fun j => slot_H Cs carriers j)
  rw [← symPool_eq Cs carriers ha hk] at s4 e4o
  -- the whole writer
  have si := ((s1.seq s2).seq s3).seq s4
  obtain ⟨mm, sm⟩ := ListMachine.Row.maskBlank si (fun _ => true) (fun _ _ => rfl) 0
  have eh1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (GT Dv + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh3 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (fun _ => 0 : Fin (GT Dv) → ℕ) i)
      (fun _ : Fin 1 => 0) : Fin (GT Dv + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have hstep := (sm.congr_in eh1 (gsA0_in w)).congr eh3 rfl
  unfold gsCost at hB
  rw [hW] at hB
  refine writerRun_of_step hstep ?_ ?_ (gsIn_ne_out Dv) (by omega)
  · show Fin.addCases E4 (fun _ : Fin 1 => List.replicate mm false) (Fin.castAdd 1 (gl (ws gIN))) = frame w
    rw [Fin.addCases_left, e4k _ (by rw [gl_val, ws_IN]; omega), a1, addCases_dPos, t_in]
  · show Fin.addCases E4 (fun _ : Fin 1 => List.replicate mm false) (Fin.castAdd 1 (cReg 0)) =
      C4Geo.gateField (PrimAsm.Records.symPool Cs carriers)
    rw [Fin.addCases_left, e4o]

end NearCubicWires.WireExponent3_5.PrimT.C4GateSym
