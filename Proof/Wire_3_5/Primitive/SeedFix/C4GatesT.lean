import Proof.Wire_3_5.Primitive.SeedFix.C4GatesB

/-! # G1, the gate converter, part 5: one table (P3:1655-1664)

A slot's table `gatesW h G` (the per-point evaluators' format) is its gates, each after a marker, then `false`. The
table loop `tabW` runs the gate body (`gateB_spec`) on each: the gate scratch `S` receives
`G.flatMap (quad (tabGW g) ++ [T, F])` (each pool gate's native word framed once more), the gate count grows by
`|G|` (**`tabLoop_spec`**). Blank tables read `false` at once and contribute nothing.

Paper quantity of the main type: the pool gates' native words `tabGW g` of one slot. -/

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

/-- The gate scratch's words of a gate list. -/
def WS {n : ℕ} (G : List (NormalizedThresholdGate n)) : List Bool := G.flatMap fun g => quad (tabGW g) ++ [true, false]

/-- The threshold scratch's words of a gate list. -/
def WT {n : ℕ} (G : List (NormalizedThresholdGate n)) : List Bool := G.flatMap fun g => quad (intWord (g.threshold - 1))

/-- The table loop's state: the scratches appended, the count at `c`, the table's head at `p`. -/
def ust (T : Fin 12) (σ : CS) (p : ℕ) (wt ws : List Bool) (c : ℕ) : CS :=
  ((PrimAsm.WriteNat.appendO (appTS σ wt) sS rOs ws).setv rCNT c).seth T p

theorem ust_ust (j : Fin 6) (σ : CS) (p p' c c' : ℕ) (wt ws wt' ws' : List Bool) :
    ust (tbl j) (ust (tbl j) σ p wt ws c) p' wt' ws' c' = ust (tbl j) σ p' (wt ++ wt') (ws ++ ws') c' := by
  have hne : tbl j ≠ sS := tbl_ne j sS (by decide)
  have hneT : tbl j ≠ sTS := tbl_ne j sTS (by decide)
  apply WState.eq
  · funext i
    simp only [ust, appTS, WState.setv_sh, WState.seth_sh, WState.sets_sh, PrimAsm.WriteNat.appendO_sh,
      Function.update_apply]
    by_cases h1 : i = tbl j
    · subst h1; simp [hne, hneT]
    · by_cases h2 : i = sS
      · subst h2; simp +decide [h1]; omega
      · by_cases h3 : i = sTS
        · subst h3; simp +decide [h1]; omega
        · simp [h1, h2, h3]
  · funext i
    simp only [ust, appTS, WState.setv_st, WState.seth_st, WState.sets_st, PrimAsm.WriteNat.appendO_st,
      Function.update_apply]
    by_cases h2 : i = sS
    · subst h2; simp +decide
    · by_cases h3 : i = sTS
      · subst h3; simp +decide
      · simp [h2, h3]
  · funext r
    simp only [ust, appTS, WState.setv_val, WState.seth_val, WState.sets_val, PrimAsm.WriteNat.appendO_val,
      Function.update_apply]
    by_cases h1 : r = rCNT
    · subst h1; simp +decide
    · by_cases h2 : r = rOs
      · subst h2; simp +decide; omega
      · simp [h1, h2]
  · rfl

theorem ust_self (j : Fin 6) (σ : CS) : ust (tbl j) σ (σ.sh (tbl j)) [] [] (σ.val rCNT) = σ := by
  apply WState.eq
  · funext i
    simp only [ust, appTS, WState.setv_sh, WState.seth_sh, WState.sets_sh, PrimAsm.WriteNat.appendO_sh,
      Function.update_apply]
    split_ifs <;> simp_all
  · funext i
    simp only [ust, appTS, WState.setv_st, WState.seth_st, WState.sets_st, PrimAsm.WriteNat.appendO_st,
      Function.update_apply]
    split_ifs <;> simp_all
  · funext r
    simp only [ust, appTS, WState.setv_val, WState.seth_val, WState.sets_val, PrimAsm.WriteNat.appendO_val,
      Function.update_apply]
    split_ifs <;> simp_all
  · rfl

theorem ust_seth (j : Fin 6) (σ : CS) (x p : ℕ) (wt ws : List Bool) (c : ℕ) :
    ust (tbl j) (σ.seth (tbl j) x) p wt ws c = ust (tbl j) σ p wt ws c := by
  have hne : tbl j ≠ sS := tbl_ne j sS (by decide)
  have hneT : tbl j ≠ sTS := tbl_ne j sTS (by decide)
  apply WState.eq
  · funext i
    simp only [ust, appTS, WState.setv_sh, WState.seth_sh, WState.sets_sh, PrimAsm.WriteNat.appendO_sh,
      Function.update_apply]
    by_cases h1 : i = tbl j
    · subst h1; simp [hne, hneT]
    · simp +decide [h1, hne.symm, hneT.symm]
  · rfl
  · rfl
  · rfl

/-- A gate's framed native word is at most `(8h+8)(n+2) + 8·natBitLength n + 8` cells. -/
theorem gateWord_le (h : ℕ) (hh : 1 ≤ h) {n : ℕ} (g : NormalizedThresholdGate n)
    (hw : ∀ i, (g.weight i).natAbs < 2 ^ h) (ht : (g.threshold - 1).natAbs + 1 < 2 ^ h) :
    (quad (tabGW g) ++ [true, false]).length ≤ (8 * h + 8) * (n + 2) + 8 * natBitLength n + 8 := by
  have hws : ∀ w ∈ List.ofFn g.weight, w.natAbs < 2 ^ h := by
    intro w hw'; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw'; exact hw i
  have h1 := flatMap_intWord_le h hh _ hws
  rw [List.length_ofFn] at h1
  have h2 := CompilerMachine.Pool.natBitLength_le (g.threshold - 1).natAbs h hh (by omega)
  rw [List.length_append, quad_length, tabGW_eq, List.length_append, List.length_append, natWord_length',
    intWord_length']
  have e : (8 * h + 8) * (n + 2) = 4 * (n * (2 * h + 2)) + 16 * h + 16 := by ring
  simp only [List.length_cons, List.length_nil]
  omega

/-- **One table**: each gate after its marker. -/
def tabW (T : Fin 12) : CW := .whs T (.seq (.fwd T) (gateB T))

/-- The standing facts the gate body needs. -/
structure Ready (σ : CS) (n : ℕ) : Prop where
  L : σ.val rL = 0
  L2 : σ.val rL2 = 0
  Z : σ.val rZ = 0
  F : σ.val rF = 0
  H : σ.val rH = 0
  X : σ.val rX = 0
  T : σ.val rT = 0
  K : σ.val rK = 0
  Ot : σ.val rOt = 0
  NQ : σ.st sNQ = Streaming.marks (natWord n)
  NQh : σ.sh sNQ = 0
  q : σ.val rOq = (Streaming.marks (natWord n)).length
  N : σ.val rN = n
  S : σ.sh sS = (σ.st sS).length
  TS : σ.sh sTS = (σ.st sTS).length

theorem ready_ust (j : Fin 6) {n : ℕ} (σ : CS) (hσ : Ready σ n) (p : ℕ) (wt ws : List Bool) (c : ℕ) :
    Ready (ust (tbl j) σ p wt ws c) n := by
  have hne : tbl j ≠ sS := tbl_ne j sS (by decide)
  have hneT : tbl j ≠ sTS := tbl_ne j sTS (by decide)
  have hneQ : tbl j ≠ sNQ := tbl_ne j sNQ (by decide)
  constructor <;> simp +decide [ust, appTS, Function.update_apply, hne.symm, hneT.symm, hneQ.symm, hσ.L, hσ.L2,
    hσ.Z, hσ.F, hσ.H, hσ.X, hσ.T, hσ.K, hσ.Ot, hσ.NQ, hσ.NQh, hσ.q, hσ.N, hσ.S, hσ.TS] <;> omega

theorem ready_seth (j : Fin 6) {n : ℕ} (σ : CS) (hσ : Ready σ n) (x : ℕ) : Ready (σ.seth (tbl j) x) n := by
  have hne : tbl j ≠ sS := tbl_ne j sS (by decide)
  have hneT : tbl j ≠ sTS := tbl_ne j sTS (by decide)
  have hneQ : tbl j ≠ sNQ := tbl_ne j sNQ (by decide)
  constructor <;> simp [Function.update_apply, hne.symm, hneT.symm, hneQ.symm, hσ.L, hσ.L2, hσ.Z, hσ.F, hσ.H,
    hσ.X, hσ.T, hσ.K, hσ.Ot, hσ.NQ, hσ.NQh, hσ.q, hσ.N, hσ.S, hσ.TS]

/-- **One table's gates**, each to its framed native word on `S`. -/
theorem tabLoop_spec (cap : ℕ) (hcap : 1 ≤ cap) (j : Fin 6) (h : ℕ) (hh : 1 ≤ h) {n : ℕ} :
    ∀ (G : List (NormalizedThresholdGate n)) (pre rest : List Bool) (σ : CS),
      (∀ g ∈ G, (∀ i, (g.weight i).natAbs < 2 ^ h) ∧ (g.threshold - 1).natAbs + 1 < 2 ^ h ∧
        g.threshold.natAbs < 2 ^ h) →
      σ.st (tbl j) = pre ++ (G.flatMap (gateW h) ++ false :: rest) → σ.sh (tbl j) = pre.length → Ready σ n →
      σ.val rOs + G.length * ((8 * h + 8) * (n + 2) + 8 * natBitLength n + 8) ≤ cap → 2 * h + 2 ≤ cap →
      n + 4 * natBitLength n + 4 ≤ cap → σ.val rCNT + G.length ≤ cap →
      WExec cap (tabW (tbl j)) σ
        (ust (tbl j) σ (pre.length + (G.flatMap (gateW h)).length) (WT G) (WS G) (σ.val rCNT + G.length))
        (G.length * (gateCost h n + 4) + 1)
  | [], pre, rest, σ, _, hst, hsh, _, _, _, _, _ => by
    have hr : wbit σ (tbl j) = false := by
      simp only [wbit, hst, hsh]
      rw [show pre.length = pre.length + 0 from rfl, rd_shift]
      simp [readTapeBit]
    have e := ust_self j σ
    rw [hsh] at e
    simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, WT, WS, Nat.zero_mul, Nat.zero_add]
    rw [e]
    exact WExec.whsF hr
  | g :: G, pre, rest, σ, hG, hst, hsh, hR, hcS, hc2, hcn, hcC => by
    obtain ⟨hw, ht, ht'⟩ := hG g (by simp)
    simp only [List.length_cons] at hcS hcC
    have hm : wbit σ (tbl j) = true := by
      simp only [wbit, hst, hsh]
      rw [show pre.length = pre.length + 0 from rfl, rd_shift]
      simp [List.flatMap_cons, gateW, readTapeBit]
    have s1 := WExec.fwd (cap := cap) (tbl j) σ
    set σ1 := σ.seth (tbl j) (σ.sh (tbl j) + 1) with hσ1
    have hwl := gateWord_le h hh g hw ht
    have s2 := gateB_spec cap hcap j h g (pre ++ [true]) (G.flatMap (gateW h) ++ false :: rest) σ1 hh hw ht ht'
      (by simp [σ1, hst, gateW, List.append_assoc]) (by simp [σ1, hsh])
      (ready_seth j σ hR _).L (ready_seth j σ hR _).L2 (ready_seth j σ hR _).Z (ready_seth j σ hR _).F
      (ready_seth j σ hR _).H (ready_seth j σ hR _).X (ready_seth j σ hR _).T (ready_seth j σ hR _).K
      (ready_seth j σ hR _).Ot (ready_seth j σ hR _).NQ (ready_seth j σ hR _).NQh (ready_seth j σ hR _).q
      (ready_seth j σ hR _).N (ready_seth j σ hR _).S (ready_seth j σ hR _).TS
      (by simp [σ1]; nlinarith) hc2 hcn (by simp [σ1]; omega)
    set σ2 := ((PrimAsm.WriteNat.appendO (appTS σ1 (quad (intWord (g.threshold - 1)))) sS rOs
        (quad (tabGW g) ++ [true, false])).setv rCNT (σ1.val rCNT + 1)).seth (tbl j)
        ((pre ++ [true]).length + (pairW h (-g.threshold)).length + ((List.ofFn g.weight).flatMap (pairW h)).length)
      with hσ2
    have hσ2u : σ2 = ust (tbl j) σ1 ((pre ++ [true]).length + (pairW h (-g.threshold)).length +
        ((List.ofFn g.weight).flatMap (pairW h)).length) (quad (intWord (g.threshold - 1)))
        (quad (tabGW g) ++ [true, false]) (σ1.val rCNT + 1) := rfl
    have hne : tbl j ≠ sS := tbl_ne j sS (by decide)
    have s3 := tabLoop_spec cap hcap j h hh G (pre ++ gateW h g) rest σ2 (fun x hx => hG x (by simp [hx]))
      (by rw [hσ2u]; simp [ust, appTS, σ1, Function.update_apply, hst, List.append_assoc,
        tbl_ne j sTS (by decide), hne])
      (by rw [hσ2u]; simp [ust, gateW, List.length_append]; omega)
      (by rw [hσ2u]; exact ready_ust j σ1 (ready_seth j σ hR _) _ _ _ _)
      (by
        have : σ2.val rOs = σ.val rOs + (quad (tabGW g) ++ [true, false]).length := by
          rw [hσ2u]; simp +decide [ust, appTS, σ1, Function.update_apply]
        rw [this]; nlinarith)
      hc2 hcn (by rw [hσ2u]; simp +decide [ust, σ1, Function.update_apply]; omega)
    refine WExec.cast cap (WExec.whsT hm (WExec.seq s1 s2) s3) ?_ ?_
    · rw [hσ2u, ust_ust, hσ1, ust_seth]
      congr 1
      all_goals first
        | rfl
        | (simp [gateW, List.length_append]; omega)
        | (simp +decide [ust, appTS, Function.update_apply]; omega)
        | simp [WT]
        | simp [WS]
    · rw [List.length_cons, Nat.add_mul, Nat.one_mul]; omega

end NearCubicWires.WireExponent3_5.PrimT.C4Gates
