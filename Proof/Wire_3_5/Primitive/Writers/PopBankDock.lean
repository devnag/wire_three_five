import Proof.Wire_3_5.Primitive.Writers.PopBank
import Proof.Wire_3_5.Primitive.Writers.SymDecEmit

/-! # Part iii: the POP bank at the SYM call (the unit decode's `hP`)

At a SYM call the POP bank (`pbW`, run `pb_run`) meets the unit decode's POP branch: from the `Decoded` state of a POP
unit `j` (`IsPopU`) it reaches `CellUnit.DecOK` with the SYM tape's unit `symCallUnit e r s`: the POP disjunct with
the row's body when the clamp of the target matches the enumerated state's digit, the empty disjunct otherwise.

* `take_sum_sel4`, `getD_sel4`, `sum_four`, `pop_digit` (the joint state's digit, `SymDecEnum.stateDigit`, as the
  bank's divisions), `slice_off_circ`, `slice_len_circ`, **`pop_unit`** (the unit's body at a circuit row);
* `pbdL`, `pbdOff`, `pbdG` (the POP row's slice length, offset and pool size), `pop_core`, **`pop_hP`** (`sym_hdec`'s
  hypothesis `hP` at `pb := pbW W Q`), **`sym_hdec_pop`** (`sym_hdec` with the POP bank).

Paper quantities of the main types: the SYM request unit of a circuit row, `[clamp(s) = t_i^±]` times the POP row of
the flat list at the call's seed (row:sym P3:2477-2496, list:flatten P3:1491-1498), and the SYM tape's unit `j`
(P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.Records
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm.Enum NearCubicWires.WireExponent3_5.PrimAsm.SymDecEnum
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces

/-! ## Value facts -/

theorem take_sum_sel4 (l : List ℕ) (i : ℕ) (hi : i ≤ 3) :
    (l.take i).sum = sel4 i 0 (l.getD 0 0) (l.getD 0 0 + l.getD 1 0) (l.getD 0 0 + l.getD 1 0 + l.getD 2 0) := by
  interval_cases i <;> rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, t⟩⟩⟩ <;> simp [sel4] <;> omega

theorem getD_sel4 (l : List ℕ) (i : ℕ) (hi : i ≤ 3) :
    l.getD i 0 = sel4 i (l.getD 0 0) (l.getD 1 0) (l.getD 2 0) (l.getD 3 0) := by
  interval_cases i <;> simp [sel4]

theorem sum_four (l : List ℕ) (h : l.length ≤ 4) : l.sum = l.getD 0 0 + l.getD 1 0 + l.getD 2 0 + l.getD 3 0 := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, t⟩⟩⟩⟩⟩
  · rfl
  · simp
  · simp
  · simp; omega
  · simp; omega
  · simp only [List.length_cons] at h; omega

/-- **The joint state's digit, as the bank's divisions** (`SymDecEnum.stateDigit`). -/
theorem pop_digit {a : ℕ} (m : Fin a → ℕ) (xx : Fin (∏ j, (m j + 1) * (m j + 1))) (i : ℕ) (hi : i < a) (hi3 : i ≤ 3)
    (m0 m1 m2 m3 : ℕ) (hm : ∀ k (hk : k < a), m ⟨k, hk⟩ = sel4 k m0 m1 m2 m3) (p : ℕ) :
    (if p = 0 then (((symStateEquiv m).symm xx ⟨i, hi⟩).1 : ℕ) else (((symStateEquiv m).symm xx ⟨i, hi⟩).2 : ℕ)) =
      pbT xx.val m0 m1 m2 m3 i p := by
  obtain ⟨d1, d2⟩ := stateDigit m xx ⟨i, hi⟩
  rw [d1, d2, hm i hi]
  unfold pbT pbX
  interval_cases i
  · simp [sel4, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
  · have h0 := hm 0 (by omega)
    simp [sel4] at h0
    simp [Fin.prod_univ_one, Fin.castLE, h0, sel4, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod,
      ← Nat.div_div_eq_div_mul]
  · have h0 := hm 0 (by omega)
    have h1 := hm 1 (by omega)
    simp [sel4] at h0 h1
    simp [Fin.prod_univ_two, Fin.castLE, h0, h1, sel4, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod,
      ← Nat.div_div_eq_div_mul]
  · have h0 := hm 0 (by omega)
    have h1 := hm 1 (by omega)
    have h2 := hm 2 (by omega)
    simp [sel4] at h0 h1 h2
    simp [Fin.prod_univ_three, Fin.castLE, h0, h1, h2, sel4, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod,
      ← Nat.div_div_eq_div_mul]

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
variable (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n)
  (carriers : List (Carrier n))

theorem slice_off_circ (i : ℕ) (hi : i ≤ 3) (hnc : carriers.length ≤ 2) :
    sliceOff (symSlices Cs carriers) (carriers.length + i) =
      2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) +
        sel4 i 0 ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0)
          ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0 + (cyOf Cs).getD 2 0) := by
  unfold sliceOff symSlices
  rw [List.take_append, List.take_of_length_le (by simp), List.map_append, List.sum_append]
  simp only [List.length_map, Nat.add_sub_cancel_left]
  have e1 : ∀ L : List (Carrier n),
      ((L.map FinalPass.Corner.maskGates).map List.length).sum = 2 * (L.map (·.length)).sum := by
    intro L
    rw [List.map_map]
    induction L with
    | nil => rfl
    | cons X t ih => simp only [List.map_cons, List.sum_cons, Function.comp, mask_len] at ih ⊢; rw [ih]; ring
  have e2 : ((List.take i (List.ofFn fun j => symGates (Cs j))).map List.length) = (cyOf Cs).take i := by
    unfold cyOf; rw [List.map_take, List.map_ofFn]; rfl
  rw [e1 carriers, e2, sum_two _ (by simpa using hnc), take_sum_sel4 _ i hi]

theorem slice_len_circ (i : ℕ) (hi : i < a) (ha : a ≤ 4) :
    ((symSlices Cs carriers).getD (carriers.length + i) []).length =
      sel4 i ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) := by
  have e := symSlices_circuit Cs carriers ⟨i, hi⟩
  simp only at e
  rw [e, length_symGates, ← getD_sel4 _ i (by omega), cy_getD, dif_pos hi]

theorem symM_sel4 (ha : a ≤ 4) (k : ℕ) (hk : k < a) :
    symM (I.starParams n hs) Cs ⟨k, hk⟩ =
      sel4 k ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) := by
  rw [← getD_sel4 _ k (by omega), cy_getD, dif_pos hk]
  rfl

/-- **A SYM request unit of a circuit row** (`r ≥ |carriers|`): the POP row's body at the enumerated flat seed,
circuit `i = (r − nc)/2`'s slice and sign, if the target's clamp is the enumerated state's digit; empty otherwise. -/
theorem pop_unit (ha : a ≤ 4) (hnc : carriers.length ≤ 2) (e r s : ℕ) (hnr : carriers.length ≤ r)
    (hr : r < carriers.length + 2 * a) (hs' : s < (symListParams I n a Cs carriers).M + 1) :
    SymFlat.symCallUnit I hs Cs carriers e r s =
      if pbC s (sel4 ((r - carriers.length) / 2) ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
          ((cyOf Cs).getD 3 0)) =
        pbT (symStateEquiv _ (symEnum I hs Cs carriers (e / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).2 : ℕ)
          ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0)
          ((r - carriers.length) / 2) ((r - carriers.length) % 2)
      then (popRefC (symListParams I n a Cs carriers)
          (symEnum I hs Cs carriers (e / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).1.2
          (sel4 ((r - carriers.length) / 2) ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
            ((cyOf Cs).getD 3 0))
          (decide ((r - carriers.length) % 2 = 0))
          (sliceLabs (2 * (2 * (e % (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)))
            (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
            (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) +
              sel4 ((r - carriers.length) / 2) 0 ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0)
                ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0 + (cyOf Cs).getD 2 0))
            (sel4 ((r - carriers.length) / 2) ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
              ((cyOf Cs).getD 3 0))) ⟨s, hs'⟩).flatMap (fun t => true :: ListMachine.Rec.termWord t)
      else [] := by
  have hia : (r - carriers.length) / 2 < a := by omega
  have hi3 : (r - carriers.length) / 2 ≤ 3 := by omega
  have hcl : (Rows.clampState (symM (I.starParams n hs) Cs ⟨(r - carriers.length) / 2, hia⟩) s : ℕ) =
      pbC s (sel4 ((r - carriers.length) / 2) ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
          ((cyOf Cs).getD 3 0)) := by
    rw [symM_sel4 I hs Cs ha _ hia]
    generalize sel4 ((r - carriers.length) / 2) ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
      ((cyOf Cs).getD 3 0) = mm
    unfold Rows.clampState pbC
    by_cases h : s ≤ mm
    · rw [dif_pos h, if_neg (by omega)]
    · rw [dif_neg h, if_pos (by omega)]
  have hdg := pop_digit (symM (I.starParams n hs) Cs)
    (symStateEquiv _ (symEnum I hs Cs carriers (e / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).2)
    ((r - carriers.length) / 2) hia hi3 ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
    ((cyOf Cs).getD 3 0) (fun k hk => symM_sel4 I hs Cs ha k hk) ((r - carriers.length) % 2)
  rw [Equiv.symm_apply_apply] at hdg
  have hbody : ∀ (Pl : FlatListParams) (e' : Pl.FlatSeed) (G row nw : ℕ) (sgn : Bool) (s' : Fin (Pl.M + 1)),
      SymFlat.unitBody (popRow (symSlices Cs carriers) Pl e' G row nw (carriers.length + (r - carriers.length) / 2) sgn s') =
        (popRefC Pl e' ((symSlices Cs carriers).getD (carriers.length + (r - carriers.length) / 2) []).length sgn
          (sliceLabs (4 * row) G (sliceOff (symSlices Cs carriers) (carriers.length + (r - carriers.length) / 2))
            ((symSlices Cs carriers).getD (carriers.length + (r - carriers.length) / 2) []).length) s').flatMap
          (fun t => true :: ListMachine.Rec.termWord t) := by
    intro Pl e' G row nw sgn s'
    rw [← labs_eq]
    rfl
  unfold SymFlat.symCallUnit SymFlat.symReqUnit
  rw [if_neg (by omega), dif_pos hia, dif_pos hs', hcl, hdg]
  split_ifs with h
  · rw [hbody, slice_len_circ Cs carriers _ hia ha, slice_off_circ Cs carriers _ hi3 hnc, pool_length,
      sum_two _ (by simpa using hnc), show ∀ q : ℕ, 4 * q = 2 * (2 * q) from fun q => by ring]
  · rfl

/-! ## The dock -/

theorem numsVec_pbZ (n capS err M nc L kh a m0 m1 m2 m3 : ℕ) (i : Fin 64) (hi : i.val ∈ pbZ) :
    numsVec n capS err M nc L kh a m0 m1 m2 m3 i = 0 := by
  obtain ⟨iv, hiv⟩ := i
  simp only [pbZ, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The POP row's slice length `m_i`. -/
def pbdL (i : ℕ) : ℕ := sel4 i ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0)

/-- The POP row's slice offset `2(|X_0| + |X_1|) + Σ_{k<i} m_k`. -/
def pbdOff (i : ℕ) : ℕ :=
  2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) +
    sel4 i 0 ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0)
      ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0 + (cyOf Cs).getD 2 0)

/-- The SYM pool's size `2(|X_0| + |X_1|) + Σ_i m_i`. -/
def pbdG : ℕ := 2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum

end Call

section Dock
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable (cap : ℕ) (W : WalkBankProducer)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

theorem stV_pos (m0 m1 m2 m3 : ℕ) : 0 < stV m0 m1 m2 m3 := by unfold stV; positivity

/-- The dock at one unit, in the unit's numbers: the bank's run and `DecOK` from the unit's body. -/
theorem pop_core (Q : PopSetupSpec W) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (w out u : List Bool)
    (Bb BP j e r s row x : ℕ) (y : Fin (Fintype.card (symListParams I n a Cs carriers).FlatSeed))
    (σ : WState (LNS W.x) LNR) (hsM : s < (symListParams I n a Cs carriers).M + 1)
    (hst : σ.st = (CellLoopD.blankCellD W.x w out j u).st)
    (hsh : ∀ s', s' ≠ sk W.x 113 → σ.sh s' = (CellLoopD.blankCellD W.x w out j u).sh s') (hcl : σ.cell = false)
    (hzl : ∀ q : Fin LNR, q.val < 250 → σ.val q = 0) (zfs : ∀ q : Fin LNR, 400 ≤ q.val → q.val < 408 → σ.val q = 0)
    (zTM : σ.val TM = 0) (hB : ∀ q, σ.val q ≤ cap)
    (h9 : σ.val (H 9) = r) (h12 : σ.val (H 12) = s) (h13 : σ.val (H 13) = row) (h15 : σ.val (H 15) = x)
    (h17 : σ.val (H 17) = y.val) (hz : ∀ k : Fin 40, 20 ≤ k.val → σ.val (H k) = 0)
    (gz : ∀ i : Fin 64, i.val ∈ pbZ → σ.val (G i) = 0)
    (g32 : σ.val (G 32) = (symListParams I n a Cs carriers).M) (g33 : σ.val (G 33) = (symListParams I n a Cs carriers).B)
    (g34 : σ.val (G 34) = (symListParams I n a Cs carriers).errExp)
    (vNC : σ.val dNC = carriers.length) (v0 : σ.val dM0 = (cyOf Cs).getD 0 0) (v1 : σ.val dM1 = (cyOf Cs).getD 1 0)
    (v2 : σ.val dM2 = (cyOf Cs).getD 2 0) (v3 : σ.val dM3 = (cyOf Cs).getD 3 0)
    (vA : σ.val XA = (carriers.map (·.length)).getD 0 0) (vB : σ.val XB = (carriers.map (·.length)).getD 1 0)
    (vMS : σ.val dMS = (cyOf Cs).sum)
    (hia : (r - carriers.length) / 2 < a) (hi3 : (r - carriers.length) / 2 ≤ 3)
    (hc : r + carriers.length + x + 4 * ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0 + (cyOf Cs).getD 2 0 +
      (cyOf Cs).getD 3 0) + (symListParams I n a Cs carriers).M + (symListParams I n a Cs carriers).B +
      (symListParams I n a Cs carriers).errExp + y.val + s + 4 * row +
      2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum + 20 ≤ cap)
    (hrow : row < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)))
    (hQc : pbCost cap + Q.bound cap ≤ Bb)
    (hPN : ∀ i : ℕ, i < a → ∀ (e' : (symListParams I n a Cs carriers).FlatSeed) (row : ℕ) (sgn : Bool)
      (s : Fin ((symListParams I n a Cs carriers).M + 1)), row < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) →
      Q.need (symListParams I n a Cs carriers) (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) ≤ cap ∧
      ∀ hl : 4 * pbdL Cs i ≤ (sliceLabs (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i)).length,
        popPipeBound cap (symListParams I n a Cs carriers) e' (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers)
          (pbdOff Cs carriers i) (popMlab (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popLw (symListParams I n a Cs carriers) (pbdL Cs i))
          (popR (symListParams I n a Cs carriers) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popCp (symListParams I n a Cs carriers) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popRW (symListParams I n a Cs carriers)) (popRW (symListParams I n a Cs carriers)) sgn s hl ≤ BP)
    (hU : SymFlat.symCallUnit I hs Cs carriers e r s =
      if pbC s (pbdL Cs ((r - carriers.length) / 2)) =
        pbT x ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0)
          ((r - carriers.length) / 2) ((r - carriers.length) % 2)
      then (popRefC (symListParams I n a Cs carriers) ((flatSeedEquiv (symListParams I n a Cs carriers)).symm y)
          (pbdL Cs ((r - carriers.length) / 2)) (decide ((r - carriers.length) % 2 = 0))
          (sliceLabs (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers ((r - carriers.length) / 2))
            (pbdL Cs ((r - carriers.length) / 2))) ⟨s, hsM⟩).flatMap (fun t => true :: ListMachine.Rec.termWord t)
      else []) :
    ∃ τ c, WExec cap (pbW W Q) σ τ c ∧ DecOK cap W τ out (SymFlat.symCallUnit I hs Cs carriers e r s) BP ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧ c ≤ Bb := by
  obtain ⟨hn1, hn2⟩ := hPN _ hia ((flatSeedEquiv _).symm y) row (decide ((r - carriers.length) % 2 = 0))
    ⟨s, hsM⟩ hrow
  have hn1' : Q.need ⟨(symListParams I n a Cs carriers).M, (symListParams I n a Cs carriers).B,
      (symListParams I n a Cs carriers).errExp⟩
      (sel4 ((r - carriers.length) / 2) ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
        ((cyOf Cs).getD 3 0)) (2 * (2 * row))
      (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
      (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) +
        sel4 ((r - carriers.length) / 2) 0 ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0)
          ((cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0 + (cyOf Cs).getD 2 0)) ≤ cap := hn1
  obtain ⟨τ, c, eQ, hcb, k0, k2, k2h, hM, hN⟩ := pb_run cap W Q σ w out u j r carriers.length s row x y.val
    _ _ _ _ _ _ _ _ _ _ hst hsh hcl hzl zfs zTM hB h9 h12 h13 h15 h17 hz gz g32 g33 g34 vNC v0 v1 v2 v3 vA vB vMS hi3
    hsM y.isLt hc hn1'
  refine ⟨τ, c, eQ, ?_, k0, k2, k2h, le_trans hcb hQc⟩
  rw [hU]
  by_cases hm : pbC s (pbdL Cs ((r - carriers.length) / 2)) =
      pbT x ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0)
        ((r - carriers.length) / 2) ((r - carriers.length) % 2)
  · rw [if_pos hm]
    obtain ⟨f150, h150, hlabs, hPR⟩ := hM hm
    right; left
    exact ⟨f150, h150, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlabs, hPR, rfl, hn2 hlabs⟩
  · rw [if_neg hm]
    obtain ⟨sτ, shτ⟩ := hN hm
    have n150 : sk W.x 150 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
    have n151 : sk W.x 151 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
    have n1B : sk W.x 1 ≠ sk W.x 113 := fun e => absurd (sk_inj W.x e) (by decide)
    have n01 : sk W.x 0 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
    have a0 : sk W.x 150 ≠ sk W.x 0 := fun e => absurd (sk_inj W.x e) (by decide)
    have a1 : sk W.x 150 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
    have a2 : sk W.x 150 ≠ sk W.x 2 := fun e => absurd (sk_inj W.x e) (by decide)
    have b0 : sk W.x 151 ≠ sk W.x 0 := fun e => absurd (sk_inj W.x e) (by decide)
    have b1 : sk W.x 151 ≠ sk W.x 1 := fun e => absurd (sk_inj W.x e) (by decide)
    have b2 : sk W.x 151 ≠ sk W.x 2 := fun e => absurd (sk_inj W.x e) (by decide)
    left
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sτ, hst]; simp [CellLoopD.blankCellD, blankCell, a0, a1, a2, n150]
    · rw [shτ, hsh _ n150]; simp [CellLoopD.blankCellD, blankCell, a1]
    · rw [sτ, hst]; simp [CellLoopD.blankCellD, blankCell, b0, b1, b2, n151]
    · rw [shτ, hsh _ n151]; simp [CellLoopD.blankCellD, blankCell, b1]
    · rw [sτ, hst]; simp [CellLoopD.blankCellD, blankCell, n1B, n01.symm]
    · rw [shτ, hsh _ n1B]; simp [CellLoopD.blankCellD, blankCell]

/-- **The POP bank as the unit decode's `hP`** (`sym_hdec`, `pb := pbW W Q`): at every POP unit below `b`, from the
`Decoded` state, `DecOK` with the SYM tape's unit, the request and the counter kept, within `Bb`; given the POP setup's
need and the POP pipeline's bound at every circuit, seed, cell row, sign and target. -/
theorem pop_hP (Q : PopSetupSpec W) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (w : List Bool) (b Bb BP : ℕ)
    (ha : a ≤ 4) (hnc : carriers.length ≤ 2) (hcd : I.carrierDeg = 26) (hD : I.D = 1)
    (hQc : pbCost cap + Q.bound cap ≤ Bb)
    (hcB : stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) +
      7 * (cyOf Cs).sum + bV carriers.length (B.capOf .sym n) + Ledger.Lq n +
      2 ^ FlatNums.fbv (cyOf Cs).sum (bV carriers.length (B.capOf .sym n)) (Ledger.Lq n + 5) +
      4 * 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) +
      2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + 40 ≤ cap)
    (hPN : ∀ i : ℕ, i < a → ∀ (e' : (symListParams I n a Cs carriers).FlatSeed) (row : ℕ) (sgn : Bool)
      (s : Fin ((symListParams I n a Cs carriers).M + 1)), row < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) →
      Q.need (symListParams I n a Cs carriers) (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) ≤ cap ∧
      ∀ hl : 4 * pbdL Cs i ≤ (sliceLabs (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i)).length,
        popPipeBound cap (symListParams I n a Cs carriers) e' (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers)
          (pbdOff Cs carriers i) (popMlab (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popLw (symListParams I n a Cs carriers) (pbdL Cs i))
          (popR (symListParams I n a Cs carriers) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popCp (symListParams I n a Cs carriers) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popRW (symListParams I n a Cs carriers)) (popRW (symListParams I n a Cs carriers)) sgn s hl ≤ BP) :
    ∀ j < b, ∀ (out : List Bool) (σ : WState (LNS W.x) LNR), Decoded W.x cap σ w out j
        (Data.unaryList (Data.symCounts a Cs carriers)) n a
        carriers.length (cyOf Cs).sum ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
        ((cyOf Cs).getD 3 0) ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)
        (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs)) →
      IsPopU (totV n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n)
        (SeedFix.callKh (I.starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
        ((cyOf Cs).getD 3 0)) (carriers.length + 2 * a) (cyOf Cs).sum carriers.length j →
      ∃ τ c, WExec cap (pbW W Q) σ τ c ∧
        DecOK cap W τ out (SymFlat.symCallUnit I hs Cs carriers (j / ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2))
          ((j % ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) - 1) / ((cyOf Cs).sum + 3))
          ((j % ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) - 1) % ((cyOf Cs).sum + 3) - 1)) BP ∧
        τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧ c ≤ Bb := by
  intro j hj out σ hDd hp
  have hpow : (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 = 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) := by
    rw [← pow_mul, mul_comm]
  have hpos : 0 < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) := by positivity
  have htot := tot_eq_symNT I hs Cs carriers (B.capOf .sym n) ha hcd hD rfl
  have hsum := cy_sum I Cs carriers
  have hEU : euV (cyOf Cs).sum carriers.length a = (carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2 := by
    unfold euV; ring
  have hSt := stV_eq_nSt I hs Cs ha
  have hFl := fbv_eq_nFlat I Cs carriers (B.capOf .sym n) hD rfl
  have hH := hDd.hv
  obtain ⟨hT, hw0, hwlt, hv0, hvlt, hnr⟩ := hp
  rw [htot] at hT
  generalize hEUd : (carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2 = EU at hT hw0 hwlt hv0 hvlt hnr hEU ⊢
  generalize hNd : 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) = N2 at hpow hpos hH ⊢
  have hEU2 : EU = (carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2 := by rw [← hEUd, hsum]
  rw [hEU] at hH
  have hr : (j % EU - 1) / ((cyOf Cs).sum + 3) < carriers.length + 2 * a := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hsM : (j % EU - 1) % ((cyOf Cs).sum + 3) - 1 < (symListParams I n a Cs carriers).M + 1 := by rw [← hsum]; omega
  have ht : j / EU / N2 < symNT I hs Cs carriers := by
    rw [Nat.div_lt_iff_lt_mul hpos, Nat.div_lt_iff_lt_mul (by omega), ← hpow]
    calc j < symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 *
          ((carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2) := hT
      _ = _ := by rw [← hEU2]
  have hrow : j / EU % N2 < N2 := Nat.mod_lt _ hpos
  obtain ⟨vg, vf, vx⟩ := symEnum_vals I hs Cs carriers _ ht
  generalize hMS : stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) = MS
    at hH hcB hSt
  generalize hFB : 2 ^ FlatNums.fbv (cyOf Cs).sum (bV carriers.length (B.capOf .sym n)) (Ledger.Lq n + 5) = FB
    at hH hcB hFl
  have hMS0 : 0 < MS := by rw [← hMS]; exact stV_pos _ _ _ _
  have hFB0 : 0 < FB := by rw [← hFB]; positivity
  have hxs : j / EU / N2 % MS < MS := Nat.mod_lt _ hMS0
  have hfl : j / EU / N2 / MS % FB < FB := Nat.mod_lt _ hFB0
  have hsumle : (cyOf Cs).getD 0 0 + (cyOf Cs).getD 1 0 + (cyOf Cs).getD 2 0 + (cyOf Cs).getD 3 0 ≤ (cyOf Cs).sum := by
    rw [sum_four _ (by rw [cyOf_length]; exact ha)]
  have eM : (symListParams I n a Cs carriers).M = (cyOf Cs).sum := hsum.symm
  have eB : (symListParams I n a Cs carriers).B = bV carriers.length (B.capOf .sym n) := by
    unfold bV symListParams; ring
  have eE : (symListParams I n a Cs carriers).errExp = Ledger.Lq n + 5 := by
    unfold symListParams Ledger.Lq; rw [hD, one_mul]
  have hU := pop_unit I hs Cs carriers ha hnc (j / EU) ((j % EU - 1) / ((cyOf Cs).sum + 3))
    ((j % EU - 1) % ((cyOf Cs).sum + 3) - 1) hnr hr hsM
  have hxe : (symStateEquiv _ (symEnum I hs Cs carriers (j / EU / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).2 : ℕ) =
      j / EU / N2 % MS := by rw [hpow, vx, hSt]
  obtain ⟨y, hy⟩ : ∃ y, y = flatSeedEquiv (symListParams I n a Cs carriers) (symEnum I hs Cs carriers (j / EU / N2)).1.2 :=
    ⟨_, rfl⟩
  have hyv : (y : ℕ) = j / EU / N2 / MS % FB := by rw [hy, vf, hSt, hFl]
  have hes : (symEnum I hs Cs carriers (j / EU / (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2)).1.2 =
      (flatSeedEquiv (symListParams I n a Cs carriers)).symm y := by
    rw [hpow, hy, Equiv.symm_apply_apply]
  rw [hxe, hes, hpow] at hU
  exact pop_core cap W Q I hs Cs carriers w out _ Bb BP j (j / EU) _ _ _ _ y σ hsM hDd.st hDd.sh hDd.cell hDd.zl
    hDd.zfs hDd.zTM hDd.bd hH.h9 hH.h12 hH.h13 hH.h15 (by rw [hH.h17, hyv]) hH.hz
    (fun i hi => by rw [hDd.gv]; exact numsVec_pbZ _ _ _ _ _ _ _ _ _ _ _ _ i hi)
    (by rw [hDd.gv]; exact hsum)
    (by rw [hDd.gv, eB]; rfl)
    (by rw [hDd.gv, eE]; rfl)
    hDd.vNC hDd.v0 hDd.v1 hDd.v2 hDd.v3 hDd.vXA hDd.vXB hDd.vM (by omega) (by omega) (by omega) (by rw [hNd]; exact hrow) hQc hPN hU

/-- **The SYM unit decode with the POP bank** (`sym_hdec` at `pb := pbW W Q`, `hP` by `pop_hP`): the writer loop's
decode contract at every unit `j < b` and output `out`, given the POP setup's need and pipeline bound at every circuit,
seed, cell row, sign and target. -/
theorem sym_hdec_pop (F : FiltSetupSpec5 W) (Q : PopSetupSpec W) (cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)
    (Cδ : ℕ) (C : Ledger.CapParams) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (tl w : List Bool)
    (b Kb Cmax Bb BP : ℕ) (ha : a ≤ 4) (hnc : carriers.length ≤ 2) (hrB : B.rOf n = Ledger.rowBr cr n)
    (hcapOf : B.capOf .sym n = Ledger.rowBCap C .sym (B.rOf n) (Ledger.rowBSparse h0 h1 2 Cδ n) n)
    (hcd : I.carrierDeg = 26) (hD : I.D = 1)
    (hw : w = Data.reqW n false (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) tl)
    (hKb : ∀ c ∈ Data.symCodes a Cs, natBitLength c ≤ Kb)
    (hC : ∀ c ∈ carriers.map (·.length) ++ cyOf Cs, c ≤ Cmax)
    (hN1 : P1Need cap w n (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) (carriers.map (·.length)) (cyOf Cs)
      Kb Cmax)
    (hcS : (I.filterErrDeg + 4) * (n + 3) + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq n) (Ledger.rowBt h0 h1 n - 1) ≤ cap)
    (hcC : CapNeed C .sym n (B.rOf n) (Ledger.rowBSparse h0 h1 2 Cδ n) cap)
    (hN2 : NumsNeed cap n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length
      (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0)
      ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0))
    (hI : b + totV n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n)
      (SeedFix.callKh (I.starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
      ((cyOf Cs).getD 3 0) + euV (cyOf Cs).sum carriers.length a + 2 * (cyOf Cs).sum +
      2 ^ (2 * SeedFix.callKh (I.starParams n hs)) +
      stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) +
      2 ^ FlatNums.fbv (cyOf Cs).sum (bV carriers.length (B.capOf .sym n)) (Ledger.Lq n + 5) + carriers.length + 20 ≤ cap)
    (hU : 1 ≤ B.capOf .sym n)
    (hcF : 4 * 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) +
      2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum ≤ cap)
    (hFc : fbCost cap + F.bound cap ≤ Bb)
    (hFN : ∀ (eg : GapSeed (I.filterParams .sym n)) (r row : ℕ), r < carriers.length →
      row < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) →
      F.need (I.filterParams .sym n).len (I.filterParams .sym n).cap (I.filterParams .sym n).errExp
          (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)) (2 * (2 * row))
          (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
          (fbOff r ((carriers.map (·.length)).getD 0 0)) (Fintype.card (GapSeed (I.filterParams .sym n))) ≤ cap ∧
      filtPipeBound (I.filterParams .sym n) eg
          (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)) (2 * (2 * row))
          (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
          (fbOff r ((carriers.map (·.length)).getD 0 0)) (rulerW (I.filterParams .sym n))
          (rulerW (I.filterParams .sym n)) ≤ BP)
    (hQc : pbCost cap + Q.bound cap ≤ Bb)
    (hcB : stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) +
      7 * (cyOf Cs).sum + bV carriers.length (B.capOf .sym n) + Ledger.Lq n +
      2 ^ FlatNums.fbv (cyOf Cs).sum (bV carriers.length (B.capOf .sym n)) (Ledger.Lq n + 5) +
      4 * 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) +
      2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + 40 ≤ cap)
    (hPN : ∀ i : ℕ, i < a → ∀ (e' : (symListParams I n a Cs carriers).FlatSeed) (row : ℕ) (sgn : Bool)
      (s : Fin ((symListParams I n a Cs carriers).M + 1)), row < 2 ^ (2 * SeedFix.callKh (I.starParams n hs)) →
      Q.need (symListParams I n a Cs carriers) (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) ≤ cap ∧
      ∀ hl : 4 * pbdL Cs i ≤ (sliceLabs (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i)).length,
        popPipeBound cap (symListParams I n a Cs carriers) e' (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers)
          (pbdOff Cs carriers i) (popMlab (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popLw (symListParams I n a Cs carriers) (pbdL Cs i))
          (popR (symListParams I n a Cs carriers) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popCp (symListParams I n a Cs carriers) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popRW (symListParams I n a Cs carriers)) (popRW (symListParams I n a Cs carriers)) sgn s hl ≤ BP) :
    ∀ j < b, ∀ out : List Bool, ∃ σD m Bp, WExec cap (decW W F (pbW W Q) cr I.filterErrDeg ζ Cδ C)
        (CellLoopD.blankCellD W.x w out j (Data.unaryList (Data.symCounts a Cs carriers))) σD m ∧
      DecOK cap W σD out ((unitE (symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 * ((carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2)) (carriers.length + 2 * a) (symListParams I n a Cs carriers).M (SymFlat.symCallUnit I hs Cs carriers)) j) Bp ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      CellLoopD.cpCost (Data.unaryList (Data.symCounts a Cs carriers)).length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤
        symNU (Data.unaryList (Data.symCounts a Cs carriers)).length
          (4 * UnaryPow.sq cap + 1 + (reqParseCost n a carriers.length Kb + 1 + (5 * UnaryPow.sq cap + 1 +
        (30 * UnaryPow.sq cap + 1 + countsCost carriers.length Cmax (cyOf Cs).sum))) + 1 +
        (starCapCost n cr I.filterErrDeg (Ledger.rowBt h0 h1 n) (Ledger.rowBSparse h0 h1 2 Cδ n) (Ledger.Lq n) cap +
        1 + (500 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap))) + 1 + (Bb + 12)) BP b := sym_hdec cap W F (pbW W Q) cr h0 h1 Cδ C I hs Cs carriers tl w b Kb Cmax Bb BP ha hnc hrB hcapOf hcd hD hw hKb
  hC hN1 hcS hcP hcC hN2 hI hU hcF hFc hFN (pop_hP cap W Q I hs Cs carriers w b Bb BP ha hnc hcd hD hQc hcB hPN)

end Dock

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
