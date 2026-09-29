import Proof.Wire_3_5.Primitive.SeedFix.C4GatesZ

/-! # G1, the gate converter, part 8: any table width (P3:1655-1664)

A carrier slot's table is `gatesW (tabH X) (maskGates X)`: its width is the CARRIER's (`tabH X`), while its gates are
the doubled atoms. This part restates the listed slots' run for per-slot widths `hs j` bounding the slot's numbers
(`GB`): `tab_step2`, `WS_length_le2`, `tabsW_spec2`, `WS_flat_le2`, **`convAll_spec2`** (the same program `convAll`,
the same output `C4Geo.gateField (js.flatMap Gs)`).

Paper quantity of the main type: C3a's gate field of the call's pool, `gateField (js.flatMap Gs)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Gates
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT

/-- **A table width bounds a gate's numbers.** -/
def GB (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) : Prop :=
  (∀ i, (g.weight i).natAbs < 2 ^ h) ∧ (g.threshold - 1).natAbs + 1 < 2 ^ h ∧ g.threshold.natAbs < 2 ^ h

theorem GB_tabH {n : ℕ} (G : List (NormalizedThresholdGate n)) (g : NormalizedThresholdGate n) (hg : g ∈ G) :
    GB (tabH G) g := (table_bounds G g hg).2

/-- One slot's table at width `h`, or a blank one. -/
theorem tab_step2 (cap : ℕ) (hcap : 1 ≤ cap) (j : Fin 6) {n : ℕ} (H h : ℕ) (G : List (NormalizedThresholdGate n))
    (σ : CS) (hh1 : 1 ≤ h) (hGB : ∀ g ∈ G, GB h g)
    (hT : σ.st (tbl j) = gatesW h G ∨ (σ.st (tbl j) = [] ∧ G = [])) (hsh : σ.sh (tbl j) = 0)
    (hH : h ≤ H) (hR : Ready σ n)
    (hcS : σ.val rOs + G.length * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8) ≤ cap) (hc2 : 2 * H + 2 ≤ cap)
    (hcn : n + 4 * natBitLength n + 4 ≤ cap) (hcC : σ.val rCNT + G.length ≤ cap) :
    ∃ p, WExec cap (tabW (tbl j)) σ (ust (tbl j) σ p (WT G) (WS G) (σ.val rCNT + G.length))
      (G.length * (gateCost H n + 4) + 1) := by
  by_cases hG : G = []
  · subst hG
    refine ⟨σ.sh (tbl j), ?_⟩
    have hr : wbit σ (tbl j) = false := by
      rcases hT with h1 | ⟨h1, _⟩ <;> simp [wbit, h1, hsh, gatesW, readTapeBit]
    have e := ust_self j σ
    simp only [WT, WS, List.flatMap_nil, List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    rw [e]
    exact WExec.whsF hr
  · have hT' : σ.st (tbl j) = [] ++ (G.flatMap (gateW h) ++ false :: []) := by
      rcases hT with h1 | ⟨_, h2⟩
      · rw [h1]; simp [gatesW]
      · exact absurd h2 hG
    have hB : (8 * h + 8) * (n + 2) ≤ (8 * H + 8) * (n + 2) := Nat.mul_le_mul_right _ (by omega)
    have hB' : G.length * ((8 * h + 8) * (n + 2) + 8 * natBitLength n + 8) ≤
        G.length * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8) := Nat.mul_le_mul_left _ (by omega)
    have s := tabLoop_spec cap hcap j h hh1 G [] [] σ hGB hT' (by simp [hsh]) hR (by omega) (by omega) hcn hcC
    refine ⟨_, WExec.mono s ?_⟩
    have := gateCost_mono n hH
    have := Nat.mul_le_mul_left G.length (Nat.add_le_add_right this 4)
    omega

theorem WS_length_le2 {n : ℕ} (H h : ℕ) (G : List (NormalizedThresholdGate n)) (hh1 : 1 ≤ h)
    (hGB : ∀ g ∈ G, GB h g) (hH : h ≤ H) :
    (WS G).length ≤ G.length * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8) := by
  have key : ∀ (L : List (NormalizedThresholdGate n)), (∀ g ∈ L, g ∈ G) →
      (WS L).length ≤ L.length * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8) := by
    intro L
    induction L with
    | nil => intro _; simp [WS]
    | cons g L ih =>
      intro hL
      have hg := hL g (by simp)
      obtain ⟨hw, ht, _⟩ := hGB g hg
      have h1 := gateWord_le h hh1 g hw ht
      have h2 : (8 * h + 8) * (n + 2) ≤ (8 * H + 8) * (n + 2) := Nat.mul_le_mul_right _ (by omega)
      have h3 := ih (fun x hx => hL x (by simp [hx]))
      simp only [WS, List.flatMap_cons, List.length_append, List.length_cons] at h1 h3 ⊢
      rw [Nat.add_mul, Nat.one_mul]
      omega
  exact key G (fun g hg => hg)

theorem WS_flat_le2 {n : ℕ} (H : ℕ) (Gs : Fin 6 → List (NormalizedThresholdGate n)) (hs : Fin 6 → ℕ) :
    ∀ (js : List (Fin 6)), (∀ j ∈ js, 1 ≤ hs j ∧ hs j ≤ H ∧ ∀ g ∈ Gs j, GB (hs j) g) →
      (WS (js.flatMap Gs)).length ≤ (js.flatMap Gs).length * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8)
  | [], _ => by simp [WS]
  | j :: js, hH => by
    have h1 := WS_length_le2 H (hs j) (Gs j) (hH j (by simp)).1 (hH j (by simp)).2.2 (hH j (by simp)).2.1
    have h2 := WS_flat_le2 H Gs hs js (fun x hx => hH x (by simp [hx]))
    rw [List.flatMap_cons, WS_append, List.length_append, List.length_append, Nat.add_mul]
    omega

/-- **The listed slots' tables in order.** -/
theorem tabsW_spec2 (cap : ℕ) (hcap : 1 ≤ cap) {n : ℕ} (H : ℕ) (Gs : Fin 6 → List (NormalizedThresholdGate n))
    (hs : Fin 6 → ℕ) :
    ∀ (js : List (Fin 6)) (σ : CS), js.Nodup →
      (∀ j ∈ js, σ.st (tbl j) = gatesW (hs j) (Gs j) ∨ (σ.st (tbl j) = [] ∧ Gs j = [])) →
      (∀ j ∈ js, σ.sh (tbl j) = 0) → (∀ j ∈ js, 1 ≤ hs j ∧ hs j ≤ H ∧ ∀ g ∈ Gs j, GB (hs j) g) → Ready σ n →
      σ.val rOs + (js.flatMap Gs).length * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8) ≤ cap →
      2 * H + 2 ≤ cap → n + 4 * natBitLength n + 4 ≤ cap → σ.val rCNT + (js.flatMap Gs).length ≤ cap →
      ∃ τ, WExec cap (tabsW js) σ τ (((js.flatMap Gs).length + js.length) * (gateCost H n + 4) + 2 * js.length) ∧
        Ready τ n ∧ τ.st sS = σ.st sS ++ WS (js.flatMap Gs) ∧
        τ.val rOs = σ.val rOs + (WS (js.flatMap Gs)).length ∧ τ.val rCNT = σ.val rCNT + (js.flatMap Gs).length ∧
        τ.st sO = σ.st sO ∧ τ.sh sO = σ.sh sO ∧ τ.val rOo = σ.val rOo
  | [], σ, _, _, _, _, hR, _, _, _, _ => by
    refine ⟨σ, ?_, hR, by simp [WS], by simp [WS], by simp, rfl, rfl, rfl⟩
    exact WExec.mono (WExec.skip σ) (by simp)
  | j :: js, σ, hnd, hT, hsh, hH, hR, hcS, hc2, hcn, hcC => by
    rw [List.nodup_cons] at hnd
    simp only [List.flatMap_cons, List.length_append] at hcS hcC
    have hWS := WS_length_le2 H (hs j) (Gs j) (hH j (by simp)).1 (hH j (by simp)).2.2 (hH j (by simp)).2.1
    have hsplit := Nat.add_mul (Gs j).length (js.flatMap Gs).length
      ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8)
    obtain ⟨p, s1⟩ := tab_step2 cap hcap j H (hs j) (Gs j) σ (hH j (by simp)).1 (hH j (by simp)).2.2
      (hT j (by simp)) (hsh j (by simp)) (hH j (by simp)).2.1 hR
      (by omega) hc2 hcn (by omega)
    set σ1 := ust (tbl j) σ p (WT (Gs j)) (WS (Gs j)) (σ.val rCNT + (Gs j).length) with hσ1
    have hne : tbl j ≠ sS := tbl_ne j sS (by decide)
    have hneT : tbl j ≠ sTS := tbl_ne j sTS (by decide)
    have hneO : tbl j ≠ sO := tbl_ne j sO (by decide)
    have htbl : ∀ j' ∈ js, tbl j' ≠ tbl j := fun j' hj' e => hnd.1 (by
      have := congrArg Fin.val e; simp only [tbl_val] at this; rw [show j' = j from Fin.ext (by omega)] at hj'
      exact hj')
    have hv1 : σ1.val rOs = σ.val rOs + (WS (Gs j)).length := by
      simp +decide [σ1, ust, appTS, Function.update_apply]
    have hc1 : σ1.val rCNT = σ.val rCNT + (Gs j).length := by simp +decide [σ1, ust, appTS, Function.update_apply]
    obtain ⟨τ, s2, hR2, hS2, hv2, hc2', hO2, hOh2, hOo2⟩ := tabsW_spec2 cap hcap H Gs hs js σ1 hnd.2
      (fun j' hj' => by
        have := htbl j' hj'
        simp only [σ1, ust, appTS, WState.setv_st, WState.seth_st, WState.sets_st, PrimAsm.WriteNat.appendO_st,
          Function.update_apply, if_neg (tbl_ne j' sS (by decide)), if_neg (tbl_ne j' sTS (by decide))]
        exact hT j' (by simp [hj']))
      (fun j' hj' => by
        have := htbl j' hj'
        simp only [σ1, ust, appTS, WState.setv_sh, WState.seth_sh, WState.sets_sh, PrimAsm.WriteNat.appendO_sh,
          Function.update_apply, if_neg this, if_neg (tbl_ne j' sS (by decide)), if_neg (tbl_ne j' sTS (by decide))]
        exact hsh j' (by simp [hj']))
      (fun j' hj' => hH j' (by simp [hj']))
      (ready_ust j σ hR _ _ _ _)
      (by rw [hv1]; omega) hc2 hcn (by rw [hc1]; omega)
    refine ⟨τ, ?_, hR2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine WExec.mono (WExec.seq s1 s2) ?_
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have e : ((Gs j).length + (js.flatMap Gs).length + (js.length + 1)) * (gateCost H n + 4) =
          (Gs j).length * (gateCost H n + 4) + ((js.flatMap Gs).length + js.length) * (gateCost H n + 4) +
            (gateCost H n + 4) := by ring
      omega
    · rw [hS2]
      simp +decide [σ1, ust, appTS, Function.update_apply, WS_append, List.append_assoc]
    · rw [hv2, hv1, List.flatMap_cons, WS_append, List.length_append]; omega
    · rw [hc2', hc1, List.flatMap_cons, List.length_append]; omega
    · rw [hO2]; simp +decide [σ1, ust, appTS, Function.update_apply, hneO.symm]
    · rw [hOh2]; simp +decide [σ1, ust, appTS, Function.update_apply, hneO.symm]
    · rw [hOo2]; simp +decide [σ1, ust, appTS, Function.update_apply]

/-- **The gate converter's run**: from `1^n` and the listed slots' tables (blank for unfilled slots), every other
stream blank and every register `0`, the output stream ends as C3a's gate field of the pool `js.flatMap Gs`. -/
theorem convAll_spec2 (cap : ℕ) (hcap : 1 ≤ cap) {n : ℕ} (H : ℕ) (Gs : Fin 6 → List (NormalizedThresholdGate n))
    (hs : Fin 6 → ℕ)
    (js : List (Fin 6)) (hnd : js.Nodup) (σ : CS) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0)
    (hNS : σ.st sNS = List.replicate n true) (hO : σ.st sO = []) (hS : σ.st sS = []) (hNQ : σ.st sNQ = [])
    (hTS : σ.st sTS = [])
    (hT : ∀ j ∈ js, σ.st (tbl j) = gatesW (hs j) (Gs j) ∨ (σ.st (tbl j) = [] ∧ Gs j = []))
    (hH : ∀ j ∈ js, 1 ≤ hs j ∧ hs j ≤ H ∧ ∀ g ∈ Gs j, GB (hs j) g)
    (hbig : 2 * (((js.flatMap Gs).length + 1) * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8)) +
      8 * n + 8 * natBitLength n + 8 * natBitLength (js.flatMap Gs).length + 2 * H + 100 ≤ cap) :
    ∃ τ c, WExec cap (convAll js) σ τ c ∧ c ≤ convCost n (js.flatMap Gs).length H ∧
      τ.st sO = C4Geo.gateField (js.flatMap Gs) := by
  rw [C4Gates.gateField_eq]
  generalize hP : (js.flatMap Gs).length = P at hbig ⊢
  have hPB := Nat.add_mul P 1 ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8)
  have hP1 : P + 1 ≤ (P + 1) * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hBn : 8 * n + 8 ≤ (8 * H + 8) * (n + 2) + 8 * natBitLength n + 8 := by
    have : 8 * (n + 2) ≤ (8 * H + 8) * (n + 2) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hnbP : natBitLength P ≤ P + 1 := by
    have h1 : P < 2 ^ P := Nat.lt_two_pow_self
    have h2 : 2 ^ P ≤ 2 ^ (P + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := CompilerMachine.Pool.natBitLength_le P (P + 1) (by omega) (by omega)
    omega
  have hjs : js.length ≤ 6 := by simpa using hnd.length_le_card
  have hql : (Streaming.marks (natWord n)).length = 4 * natBitLength n + 2 := by
    rw [Streaming.marks_length, natWord_length']; ring
  have hmP : (Streaming.marks (natWord P)).length = 4 * natBitLength P + 2 := by
    rw [Streaming.marks_length, natWord_length']; ring
  -- 1: n into rN
  have s1 := C4Arm.ucount_spec cap sNS rN n [] rfl n 0 σ (by omega) (by rw [hNS]; simp) (hsh sNS) (hv rN) (by omega)
  set σ1 := (σ.setv rN n).seth sNS n with hσ1
  -- 2: the arity's word on NQ
  have s2 := PrimAsm.WriteNat.writeNatM_spec cap sNQ RQ σ1 (by wv [σ1, RQ0, RQ1, RQ2, RQ3, RQ4, RQ5, RQ6, hv]) (by wv [σ1, RQ0, RQ1, RQ2, RQ3, RQ4, RQ5, RQ6, hv])
    (by wv [σ1, RQ0, RQ1, RQ2, RQ3, RQ4, RQ5, RQ6, hv]) (by wv [σ1, RQ0, RQ1, RQ2, RQ3, RQ4, RQ5, RQ6, hv]) (by wv [σ1, RQ0, RQ1, RQ2, RQ3, RQ4, RQ5, RQ6, hv]) (by wv [σ1, RQ0, RQ1, RQ2, RQ3, RQ4, RQ5, RQ6, hv])
    (by wv [σ1, hsh, hNQ] <;> rfl)
    (by wv [σ1, RQ0, RQ1, RQ2, RQ3, RQ4, RQ5, RQ6, hv]; omega)
  have hσ1N : σ1.val (RQ 0) = n := by wv [σ1, RQ0, RQ1, RQ2, RQ3, RQ4, RQ5, RQ6]
  rw [hσ1N, show RQ 7 = rOq from rfl] at s2
  set σ2 := PrimAsm.WriteNat.appendO σ1 sNQ rOq (Streaming.marks (natWord n)) with hσ2
  -- 3, 4: rewind NQ
  have hσ2q : σ2.val rOq = (Streaming.marks (natWord n)).length := by wv [σ2, σ1, hv]; omega
  have s3 := FinalPass.Hash4.wcopyR_spec cap rOq rX rT (by decide) (by decide) (by decide) σ2
    (by wv [σ2, σ1, hv]) (by wv [σ2, σ1, hv]) (by rw [hσ2q]; omega)
  rw [hσ2q] at s3
  have s4 := rewW_spec cap sNQ rX (Streaming.marks (natWord n)).length
    (σ2.setv rX (Streaming.marks (natWord n)).length) (by wv [ite_true]) (by wv [σ2, σ1, hsh, hNQ]; simp) (by omega)
  set σ4 := ((σ2.setv rX (Streaming.marks (natWord n)).length).seth sNQ
    ((σ2.setv rX (Streaming.marks (natWord n)).length).sh sNQ - (Streaming.marks (natWord n)).length)).setv rX 0
    with hσ4
  have hR4 : Ready σ4 n := by
    constructor
    all_goals first
      | (wv [σ4, σ2, σ1, hv, hsh, hNQ, hS, hTS]; done)
      | (wv [σ4, σ2, σ1, hv, hsh, hNQ, hS, hTS] <;> simp <;> omega)
  -- 5: the tables
  obtain ⟨τ5, s5, hR5, hS5, hv5, hc5, hO5, hOh5, hOo5⟩ := tabsW_spec2 cap hcap H Gs hs js σ4 hnd
    (fun j hj => by
      have h1 := tbl_ne j sNQ (by decide); have h2 := tbl_ne j sNS (by decide)
      wv [σ4, σ2, σ1, h1, h2]; exact hT j hj)
    (fun j hj => by
      have h1 := tbl_ne j sNQ (by decide); have h2 := tbl_ne j sNS (by decide)
      wv [σ4, σ2, σ1, h1, h2, hsh])
    hH hR4 (by wv [σ4, σ2, σ1, hv]; rw [hP]; omega) (by omega) (by omega) (by wv [σ4, σ2, σ1, hv]; rw [hP]; omega)
  have h4Os : σ4.val rOs = 0 := by wv [σ4, σ2, σ1, hv]
  have h4C : σ4.val rCNT = 0 := by wv [σ4, σ2, σ1, hv]
  have h4O : σ4.st sO = [] := by wv [σ4, σ2, σ1, hO]
  have h4Oh : σ4.sh sO = 0 := by wv [σ4, σ2, σ1, hsh]
  have h4Oo : σ4.val rOo = 0 := by wv [σ4, σ2, σ1, hv]
  have h4S : σ4.st sS = [] := by wv [σ4, σ2, σ1, hS]
  rw [h4Os, Nat.zero_add] at hv5
  rw [h4C, Nat.zero_add, hP] at hc5
  rw [h4O] at hO5
  rw [h4Oh] at hOh5
  rw [h4Oo] at hOo5
  rw [h4S, List.nil_append] at hS5
  have hWle : (WS (js.flatMap Gs)).length ≤ P * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8) := by rw [← hP]; exact WS_flat_le2 H Gs hs js hH
  generalize hW : (WS (js.flatMap Gs)).length = W at hv5 hWle
  -- 6: the count field
  have s6 := PrimAsm.WriteNat.writeNatM_spec cap sO RO τ5 (by wv [RO0, RO1, RO2, RO3, RO4, RO5, RO6, hR5.L])
    (by wv [RO0, RO1, RO2, RO3, RO4, RO5, RO6, hR5.L2]) (by wv [RO0, RO1, RO2, RO3, RO4, RO5, RO6, hR5.Z]) (by wv [RO0, RO1, RO2, RO3, RO4, RO5, RO6, hR5.F])
    (by wv [RO0, RO1, RO2, RO3, RO4, RO5, RO6, hR5.H]) (by wv [RO0, RO1, RO2, RO3, RO4, RO5, RO6, hR5.X]) (by rw [hOh5, hO5]; rfl)
    (by wv [RO0, RO1, RO2, RO3, RO4, RO5, RO6, RO7, hc5, hOo5]; omega)
  rw [show τ5.val (RO 0) = P by wv [RO0, RO1, RO2, RO3, RO4, RO5, RO6, hc5], show RO 7 = rOo from rfl] at s6
  set τ6 := PrimAsm.WriteNat.appendO τ5 sO rOo (Streaming.marks (natWord P)) with hτ6
  -- 7: K := n
  have s7 := FinalPass.Hash4.wcopyR_spec cap rN rK rT (by decide) (by decide) (by decide) τ6
    (by wv [τ6, hR5.K]) (by wv [τ6, hR5.T]) (by wv [τ6, hR5.N]; omega)
  rw [show τ6.val rN = n by wv [τ6, hR5.N]] at s7
  set τ7 := τ6.setv rK n with hτ7
  -- 8, 9: the arity twice framed
  have s8 := headLoop_spec cap sO (OP := rOo) (L := rK) (L2 := rX) (by decide) (by decide) (by decide) n 0 τ7
    (by wv [τ7]) (by wv [τ7, τ6, hR5.X]) (by wv [τ7, τ6, hOh5, hO5]; simp only [List.length_append, List.length_nil, List.nil_append, List.length_cons] <;> omega)
    (by wv [τ7, τ6, hOo5]; omega) (by omega)
  set τ8 := ((PrimAsm.WriteNat.appendO τ7 sO rOo (quad (List.replicate n true))).setv rK 0).setv rX (0 + n) with hτ8
  have s9 := wclear_spec cap rX (0 + n) τ8 (by wv [τ8]) (by wv [τ8]; omega)
  set τ9 := τ8.setv rX 0 with hτ9
  -- 10: the arity's frame end
  have hq1 : (quad (List.replicate n true)).length = 4 * n := by rw [quad_length, List.length_replicate]
  have s10 := PrimAsm.Emit.emitW_spec cap sO rOo [true, false] τ9
    (by wv [τ9, τ8, τ7, τ6, hOh5, hO5]; simp only [List.length_append, List.length_nil, List.nil_append, List.length_cons] <;> omega)
    (by wv [τ9, τ8, τ7, τ6, hOo5]; rw [hmP, hq1]; simp; omega)
  set τ10 := PrimAsm.WriteNat.appendO τ9 sO rOo [true, false] with hτ10
  -- 11, 12: rewind S
  have hτ10s : τ10.val rOs = W := by wv [τ10, τ9, τ8, τ7, τ6, hv5]
  have s11 := FinalPass.Hash4.wcopyR_spec cap rOs rX rT (by decide) (by decide) (by decide) τ10
    (by wv [τ10, τ9, τ8, τ7, τ6]) (by wv [τ10, τ9, τ8, τ7, τ6, hR5.T]) (by rw [hτ10s]; omega)
  rw [hτ10s] at s11
  have hSh : τ10.sh sS = W := by wv [τ10, τ9, τ8, τ7, τ6, hR5.S, hS5]; rw [← hW]
  have s12 := rewW_spec cap sS rX W (τ10.setv rX W) (by wv [ite_true]) (by wv [hSh]; omega) (by omega)
  set τ12 := ((τ10.setv rX W).seth sS ((τ10.setv rX W).sh sS - W)).setv rX 0 with hτ12
  -- 13: copy S onto the output
  have s13 := copyL_spec cap sS sO rOo rOs (fun b => [b]) (by decide) (by decide) (fun b => by simp)
    (WS (js.flatMap Gs)) [] [] τ12
    (by wv [τ12, τ10, τ9, τ8, τ7, τ6, hS5]; simp)
    (by wv [τ12, hSh]; simp only [List.length_append, List.length_nil, List.nil_append, List.length_cons] <;> omega)
    (by wv [τ12, τ10, τ9, τ8, τ7, τ6, hv5]; rw [hW])
    (by wv [τ12, τ10, τ9, τ8, τ7, τ6, hOh5, hO5]; simp only [List.length_append, List.length_nil, List.nil_append, List.length_cons] <;> omega)
    (by wv [τ12, τ10, τ9, τ8, τ7, τ6, hOo5]; rw [hmP, hq1, hW]; simp; omega) (by rw [hW]; omega)
  set τ13 := ((PrimAsm.WriteNat.appendO τ12 sO rOo ((WS (js.flatMap Gs)).flatMap fun b => [b])).seth sS
    (([] : List Bool).length + (WS (js.flatMap Gs)).length)).setv rOs 0 with hτ13
  -- 14: the end
  have s14 := PrimAsm.Emit.emitW_spec cap sO rOo [false] τ13
    (by wv [τ13, τ12, τ10, τ9, τ8, τ7, τ6, hOh5, hO5]; simp only [List.length_append, List.length_nil, List.nil_append, List.length_cons] <;> omega)
    (by wv [τ13, τ12, τ10, τ9, τ8, τ7, τ6, hOo5]; rw [hmP, hq1, flatMap_single, hW]; simp; omega)
  refine ⟨_, _, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 (WExec.seq s7
    (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 (WExec.seq s12 (WExec.seq s13 s14)))))))))))), ?_, ?_⟩
  · unfold convCost
    rw [hP] at *
    have e1 : (P + 6) * (gateCost H n + 4) =
        (P + js.length) * (gateCost H n + 4) + (6 - js.length) * (gateCost H n + 4) := by
      rw [← Nat.add_mul]; congr 1; omega
    rw [hql, hW]
    simp only [List.length_cons, List.length_nil]
    omega
  · wv [τ13, τ12, τ10, τ9, τ8, τ7, τ6, hO5]
    rw [flatMap_single]
    simp [List.append_assoc]

end NearCubicWires.WireExponent3_5.PrimT.C4Gates
