import Proof.Wire_3_5.Selection.CosParse3

/-! # C1.5 parse, part 4: the gate and population tables (P3:1326-1330)

Paper: "polynomially many bottom gates, each gate given by a polynomial-bit integer threshold description [...] and
nonnegative rational weights `p_X` summing to one, with polynomial-bit descriptions" (P3:1326-1330). `gatesP` reads the
gate count (PA's `readNatM`), writes it as the width-`W` word `NG` (C6's `incB`), computes the record count `g·(n+1)`,
converts every gate number (`recL`) into the gate table and rewinds it; `popsP` reads the population count and converts
every population (`popsT`) into the population table, its length into `Q 58`, and rewinds it; `powP` sets the round
counter `C = 2^k` (PA's `pow2W`). Main declarations: `ngL_spec`, `gT6_spec`, **`gatesP_spec`**, `pT2_spec`,
**`popsP_spec`**, **`powP_spec`**. Paper quantity: the request's gates and populations on the machine's tables. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (selWord)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith (pow2W pow2W_spec)
open NearCubicWires.RepairRepresentation (natWord intWord natListWord)
open NearCubicWires.WireExponent3_5 (ratWord)

/-! ## Stream literals -/

@[simp] theorem Sm_v0 : Sm 0 = 2 := by decide
@[simp] theorem Sm_v2 : Sm 2 = 4 := by decide
@[simp] theorem Sm_v3 : Sm 3 = 5 := by decide
@[simp] theorem Sm_v30 : Sm 30 = 32 := by decide
@[simp] theorem Sm_v31 : Sm 31 = 33 := by decide
@[simp] theorem Sm_v32 : Sm 32 = 34 := by decide
@[simp] theorem Sm_v33 : Sm 33 = 35 := by decide
@[simp] theorem Sm_v34 : Sm 34 = 36 := by decide
@[simp] theorem Sm_v35 : Sm 35 = 37 := by decide
@[simp] theorem Sm_v36 : Sm 36 = 38 := by decide
@[simp] theorem Sm_v37 : Sm 37 = 39 := by decide
@[simp] theorem Sm_v38 : Sm 38 = 40 := by decide
@[simp] theorem Sm_v39 : Sm 39 = 41 := by decide
@[simp] theorem Sm_v40 : Sm 40 = 42 := by decide
@[simp] theorem Sm_v41 : Sm 41 = 43 := by decide
@[simp] theorem Sm_v42 : Sm 42 = 44 := by decide
@[simp] theorem Sm_v43 : Sm 43 = 45 := by decide
@[simp] theorem Sm_v44 : Sm 44 = 46 := by decide
@[simp] theorem Sm_v45 : Sm 45 = 47 := by decide
@[simp] theorem Sm_v46 : Sm 46 = 48 := by decide
@[simp] theorem Sm_v47 : Sm 47 = 49 := by decide

/-! ## `NG` -/

/-- The `NG` loop: `j` increments. -/
def ngL : WM 49 112 := .whr 92 (.seq (.dec 92) (incB (Sm 32) (Sm 3) 90 91))

theorem ngL_spec (cap W b : ℕ) (hcap : 2 * W + 1 ≤ cap) :
    ∀ (j : ℕ) (σ : WState 49 112) (a : ℕ), σ.val 92 = j → NumOn σ (Sm 32) W a → NumOn σ (Sm 3) W b →
      σ.val 90 = 0 → σ.val 91 = 0 → a + j < 2 ^ W → j ≤ cap →
      WExec cap ngL σ ((σ.sets (Sm 32) (frame (binary W (a + j)))).setv 92 0) (j * (41 * W + 11) + 1)
  | 0, σ, a, h92, hA, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h92) ?_ (by omega)
    rw [Nat.add_zero, ← hA.1, wsets_same, Gate.wsetv_zero _ _ h92]
  | j + 1, σ, a, h92, hA, hB, h90, h91, hfit, hj => by
    have d := WExec.dec (cap := cap) 92 σ (by omega)
    set σ1 := σ.setv 92 (σ.val 92 - 1) with hσ1
    have x := incB_spec cap W (A := Sm 32) (B := Sm 3) (F := 90) (R := 91) (by decide) (by decide) σ1 a b
      (numOn_setv _ _ _ _ _ _ hA) (numOn_setv _ _ _ _ _ _ hB) (by simp [hσ1, h90]) (by simp [hσ1, h91]) (by omega) hcap
    have ih := ngL_spec cap W b hcap j (σ1.sets (Sm 32) (frame (binary W (a + 1)))) (a + 1)
      (by simp [hσ1, h92]) (numOn_sets_self _ _ _ _ (by simpa [hσ1] using hA.2))
      (numOn_sets_other _ _ _ _ _ _ (by decide) (numOn_setv _ _ _ _ _ _ hB)) (by simp [hσ1, h90])
      (by simp [hσ1, h91]) (by omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d x) ih) ?_ (by ring_nf; omega)
    rw [hσ1, wsets_sets', show a + 1 + j = a + (j + 1) by ring]
    apply WState.eq
    · rfl
    · rfl
    · simp [Function.update_idem]
    · rfl

/-! ## The gate table -/

/-- The gate table's suffix: the records, the table's head home. -/
def gT6 : WM 49 112 := .seq (recL 0 (Sm 30) (Sm 45) 90 91 97) (rewS (Sm 30) 87 89)

theorem gT6_spec (cap : ℕ) (R : SelectionReq) (W B : ℕ) (σ : WState 49 112) (pre rest : List Bool)
    (hI : σ.st 0 = pre ++ (frameP ((gInts R).flatMap intWord) ++ rest)) (hIh : σ.sh 0 = pre.length)
    (h97 : σ.val 97 = (gInts R).length) (h90 : σ.val 90 = 0) (h91 : σ.val 91 = 0) (h87 : σ.val 87 = B)
    (h89 : σ.val 89 = 0) (h30 : σ.st (Sm 30) = []) (h30h : σ.sh (Sm 30) = 0)
    (hR : σ.st (Sm 45) = false :: List.replicate W true) (hRh : σ.sh (Sm 45) = 0)
    (hbits : ∀ z ∈ gInts R, natBitLength z.natAbs ≤ W) (hB : (gateTable W R).length ≤ B)
    (hcap : (gInts R).length + W + B + 1 ≤ cap) :
    WExec cap gT6 σ (((σ.seth 0 (pre.length + 2 * ((gInts R).flatMap intWord).length)).sets (Sm 30)
      (gateTable W R)).setv 97 0)
      (((gInts R).map fun z => convRecCost z W + 4).sum + 1 + 1 + (B * (1 + 8) + 1 + 1 + (7 * B + 1))) := by
  obtain ⟨τ, x1, t1, k1, c1, f1⟩ := recL_spec cap 0 (Sm 30) (Sm 45) 90 91 (by decide) (by decide) (by decide)
    (by decide) (by omega) 97 (by decide) (by decide) W rest (fun _ => rfl) (gInts R) σ pre hI hIh h97 (by omega)
    h90 h91 (fun z hz => ⟨hbits z hz, by have := hbits z hz; omega⟩) (by rw [h30h, h30]; rfl) hR hRh
  have hRg : ∀ r : Fin 112, r ≠ 90 → r ≠ 91 → r ≠ 97 → τ.val r = σ.val r := fun r a b c =>
    t1.fr.2.1 r (fun h' => by rcases h' with e | e | e <;> [exact a e; exact b e; exact c e])
  have x2 := rewS_spec cap (Sm 30) 87 89 (by decide) τ B (by rw [hRg 87 (by decide) (by decide) (by decide), h87])
    (by rw [hRg 89 (by decide) (by decide) (by decide), h89]) (by omega)
    (by rw [t1.hO, t1.sO, h30, ← gateTable_eq]; simpa using hB)
  refine WExec.cast cap (WExec.seq x1 x2) ?_ le_rfl
  have n030 : (0 : Fin 50) ≠ Sm 30 := by decide
  apply WState.eq
  · funext i
    by_cases hi0 : i = 0
    · subst hi0
      simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_self]
      rw [Function.update_of_ne n030]; exact t1.hI
    · by_cases hi30 : i = Sm 30
      · subst hi30
        simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_self]
        rw [Function.update_of_ne (Ne.symm n030)]; exact h30h.symm
      · simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_of_ne hi0,
          Function.update_of_ne hi30]
        exact (t1.fr.1 i (fun h' => by rcases h' with e | e <;> [exact hi0 e; exact hi30 e])).2
  · funext i
    by_cases hi0 : i = 0
    · subst hi0
      simp only [WState.seth_st, WState.sets_st, WState.setv_st, Function.update_of_ne n030]; exact t1.sI
    · by_cases hi30 : i = Sm 30
      · subst hi30
        simp only [WState.seth_st, WState.sets_st, WState.setv_st, Function.update_self]
        rw [t1.sO, h30, gateTable_eq, List.nil_append]
      · simp only [WState.seth_st, WState.sets_st, WState.setv_st, Function.update_of_ne hi30]
        exact (t1.fr.1 i (fun h' => by rcases h' with e | e <;> [exact hi0 e; exact hi30 e])).1
  · funext r
    by_cases h1 : r = 97
    · subst h1; simp [k1]
    · by_cases h2 : r = 90
      · subst h2; simp [c1, h90]
      · by_cases h3 : r = 91
        · subst h3; simp [f1, h91]
        · simp [Function.update_apply, h1, hRg r h2 h3 h1]
  · simp [t1.fr.2.2]

/-- The addition loop's registers: `(_, _, 92, _, 89, _, 60, 97)`. -/
def zGA : Fin 8 ↪ Fin 112 := ⟨fun i => ![90, 91, 92, 93, 89, 94, 60, 97] i, by decide⟩

theorem gatesP_eq : gatesP = .seq (readNatM true 0 91 90 88 94 89) (.seq (FinalPass.Hash4.wcopyR 88 92 89)
    (.seq ngL (.seq (FinalPass.Hash4.wcopyR 88 92 89) (.seq (.whr (zGA 2) (.seq (.dec (zGA 2))
      (addR (zGA 6) (zGA 4) (zGA 7)))) gT6)))) := rfl

/-- The gate stage's cost. -/
def gatesCost (R : SelectionReq) (W B : ℕ) : ℕ :=
  (natBitLength R.gates.length + 2) * (40 * 2 ^ natBitLength R.gates.length + 40) + 1 + (18 * R.gates.length + 3 + 1 +
    (R.gates.length * (41 * W + 11) + 1 + 1 + (18 * R.gates.length + 3 + 1 + (R.gates.length * ((R.n + 1) * 11 + 1 + 1 +
      (7 * (R.n + 1) + 1) + 4) + 1 + 1 + (((gInts R).map fun z => convRecCost z W + 4).sum + 1 + 1 +
        (B * (1 + 8) + 1 + 1 + (7 * B + 1)))))))

/-- **The gate stage**: `88 = g`, `NG = g`, the gate table (head home), the input past the gate section. -/
theorem gatesP_spec (cap : ℕ) (R : SelectionReq) (W B : ℕ) (σ : WState 49 112) (pre rest : List Bool)
    (hI : σ.st 0 = pre ++ (frameP (natWord R.gates.length ++ (gInts R).flatMap intWord) ++ rest))
    (hIh : σ.sh 0 = pre.length) (h60 : σ.val 60 = R.n + 1) (h87 : σ.val 87 = B)
    (hz : ∀ r : Fin 112, (r = 88 ∨ r = 89 ∨ r = 90 ∨ r = 91 ∨ r = 92 ∨ r = 94 ∨ r = 97) → σ.val r = 0)
    (hNG : NumOn σ (Sm 32) W 0) (h3 : NumOn σ (Sm 3) W 0) (h30 : σ.st (Sm 30) = []) (h30h : σ.sh (Sm 30) = 0)
    (hR : σ.st (Sm 45) = false :: List.replicate W true) (hRh : σ.sh (Sm 45) = 0)
    (hbits : ∀ z ∈ gInts R, natBitLength z.natAbs ≤ W) (hB : (gateTable W R).length ≤ B)
    (hG : R.gates.length < 2 ^ W)
    (hcap : 2 ^ (R.gates.length + 2) + R.gates.length * (R.n + 1) + 2 * W + B + R.n + 2 ≤ cap) :
    WExec cap gatesP σ ((((σ.seth 0 (pre.length + 2 * (natWord R.gates.length ++ (gInts R).flatMap intWord).length)).setv
      88 R.gates.length).sets (Sm 32) (frame (binary W R.gates.length))).sets (Sm 30) (gateTable W R))
      (gatesCost R W B) := by
  have z := hz
  set g := R.gates.length with hg
  have hnb : natBitLength g ≤ g + 1 := natBitLength_le g
  have hpw : 2 ^ (natBitLength g + 1) ≤ 2 ^ (g + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hgp : g + 2 ≤ 2 ^ (g + 2) := by have := Nat.lt_two_pow_self (n := g + 2); omega
  have x1 := readNatM_spec cap true 0 91 90 88 94 89 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) g pre (frameP ((gInts R).flatMap intWord) ++ rest) σ
    (by rw [hI, frameP_append']; simp [PrimAsm.ParseNat.enc, marks_eq, List.append_assoc]) hIh
    (z 91 (by decide)) (z 90 (by decide)) (z 94 (by decide)) (z 89 (by decide))
    (by rw [z 88 (by decide)]; omega)
  rw [z 88 (by decide), Nat.zero_add] at x1
  simp only [PrimAsm.ParseNat.stp, if_true] at x1
  set σ1 := (σ.seth 0 (pre.length + 2 * (natWord g).length)).setv 88 g with hσ1
  have x2 := cp_spec cap 88 92 89 (by decide) (by decide) (by decide) σ1 g (by simp [hσ1])
    (by simp [hσ1, z 92 (by decide)]) (by simp [hσ1, z 89 (by decide)]) (by omega)
  have x3 := ngL_spec cap W 0 (by omega) g (σ1.setv 92 g) 0 (by simp)
    (numOn_setv _ _ _ _ _ _ (numOn_setv _ _ _ _ _ _ ⟨hNG.1, by simpa using hNG.2⟩))
    (numOn_setv _ _ _ _ _ _ (numOn_setv _ _ _ _ _ _ ⟨h3.1, by simpa using h3.2⟩)) (by simp [hσ1, z 90 (by decide)])
    (by simp [hσ1, z 91 (by decide)]) (by omega) (by omega)
  rw [Nat.zero_add] at x3
  have e3 : ((σ1.setv 92 g).sets (Sm 32) (frame (binary W g))).setv 92 0 = σ1.sets (Sm 32) (frame (binary W g)) := by
    apply WState.eq
    · rfl
    · rfl
    · simp [hσ1, Function.update_idem, z 92 (by decide)]
    · rfl
  rw [e3] at x3
  set σ3 := σ1.sets (Sm 32) (frame (binary W g)) with hσ3
  have x4 := cp_spec cap 88 92 89 (by decide) (by decide) (by decide) σ3 g (by simp [hσ3, hσ1])
    (by simp [hσ3, hσ1, z 92 (by decide)]) (by simp [hσ3, hσ1, z 89 (by decide)]) (by omega)
  have x5 := ptlAdd_loop cap zGA (R.n + 1) g (σ3.setv 92 g) 0 (by simp [zGA]) (by simp [zGA, hσ3, hσ1, h60])
    (by simp [zGA, hσ3, hσ1, z 89 (by decide)]) (by simp [zGA, hσ3, hσ1, z 97 (by decide)]) (by omega) (by omega)
    (by nlinarith)
  have e5 : (((σ3.setv 92 g).setv (zGA 7) (0 + g * (R.n + 1))).setv (zGA 2) 0) =
      σ3.setv 97 (g * (R.n + 1)) := by
    simp only [zGA, Nat.zero_add]
    apply WState.eq
    · rfl
    · rfl
    · funext r
      by_cases h1 : r = 92
      · subst h1; simp [hσ3, hσ1, z 92 (by decide)]
      · simp [Function.update_apply, h1]
    · rfl
  rw [e5] at x5
  set σ5 := σ3.setv 97 (g * (R.n + 1)) with hσ5
  have x6 := gT6_spec cap R W B σ5 (pre ++ frameP (natWord g)) rest
    (by simp [hσ5, hσ3, hσ1, hI, frameP_append', List.append_assoc])
    (by simp [hσ5, hσ3, hσ1, frameP_length']) (by simp [hσ5, gInts_length, hg]) (by simp [hσ5, hσ3, hσ1, z 90 (by decide)])
    (by simp [hσ5, hσ3, hσ1, z 91 (by decide)]) (by simp [hσ5, hσ3, hσ1, h87]) (by simp [hσ5, hσ3, hσ1, z 89 (by decide)])
    (by simpa [hσ5, hσ3, hσ1] using h30) (by simpa [hσ5, hσ3, hσ1] using h30h) (by simpa [hσ5, hσ3, hσ1] using hR)
    (by simpa [hσ5, hσ3, hσ1] using hRh)
    hbits hB (by rw [gInts_length, ← hg]; omega)
  rw [gatesP_eq]
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 x6))))) ?_
    (by unfold gatesCost; rw [← hg])
  apply WState.eq
  · funext i; by_cases hi : i = 0
    · subst hi; simp [hσ5, hσ3, hσ1, frameP_length']; ring
    · simp [hσ5, hσ3, hσ1, Function.update_apply, hi]
  · funext i; by_cases hi : i = Sm 30
    · subst hi; simp
    · by_cases hi' : i = Sm 32
      · subst hi'; simp [hσ5, hσ3, hσ1]
      · simp [hσ5, hσ3, hσ1, Function.update_apply, hi, hi']
  · funext r; by_cases h1 : r = 97
    · subst h1; simp [hσ5, hσ3, hσ1, z 97 (by decide)]
    · simp [hσ5, hσ3, hσ1, Function.update_apply, h1]
  · rfl

/-! ## The population table -/

/-- The population table's suffix. -/
def pT2 : WM 49 112 := .seq (popsT 0 (Sm 31) (Sm 45) zPT 96) (rewS (Sm 31) 87 89)

/-- The population facts the table needs. -/
def PopsOK (R : SelectionReq) (W cap : ℕ) : Prop :=
  ∀ X ∈ R.pops, 0 ≤ X.2 ∧ (∀ i ∈ X.1, natBitLength i ≤ W) ∧ natBitLength X.2.num.natAbs ≤ W ∧
    natBitLength X.2.den ≤ W ∧ 2 ^ (X.1.length + 2) + (popTable W R).length + (X.1.length + 2) * (2 * W + 2) + W + 1 ≤
      cap

theorem zPT_lo (i : Fin 8) (hi : i.val ≤ 5) :
    zPT i = 90 ∨ zPT i = 91 ∨ zPT i = 92 ∨ zPT i = 93 ∨ zPT i = 89 ∨ zPT i = 94 := by
  revert hi; revert i; decide

theorem pT2_spec (cap : ℕ) (R : SelectionReq) (W B : ℕ) (σ : WState 49 112) (pre rest : List Bool)
    (hI : σ.st 0 = pre ++ (frameP (R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2) ++ rest))
    (hIh : σ.sh 0 = pre.length) (h96 : σ.val 96 = R.pops.length)
    (hz : ∀ r : Fin 112, (r = 58 ∨ r = 89 ∨ r = 90 ∨ r = 91 ∨ r = 92 ∨ r = 93 ∨ r = 94) → σ.val r = 0)
    (h95 : σ.val 95 = 2 * W + 1) (h87 : σ.val 87 = B) (h31 : σ.st (Sm 31) = []) (h31h : σ.sh (Sm 31) = 0)
    (hR : σ.st (Sm 45) = false :: List.replicate W true) (hRh : σ.sh (Sm 45) = 0) (hX : PopsOK R W cap)
    (hB : (popTable W R).length ≤ B) (hcap : R.pops.length + B + 1 ≤ cap) :
    WExec cap pT2 σ ((((σ.seth 0 (pre.length + 2 * (R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2).length)).sets
      (Sm 31) (popTable W R)).setv 58 (popTable W R).length).setv 96 0)
      (popsTCost W R.pops + 1 + (B * (1 + 8) + 1 + 1 + (7 * B + 1))) := by
  have z := hz
  have hpt : popTable W R = (R.pops.map (popRec W)).flatten := by simp [popTable]
  obtain ⟨τ, x1, t1, v1, c1⟩ := popsT_spec cap 0 (Sm 31) (Sm 45) (by decide) (by decide) (by decide) zPT 96
    (by decide) W (popTable W R).length rest R.pops σ pre 0 hI hIh h96 (by omega)
    (fun i hi => by
      rcases zPT_lo i hi with e | e | e | e | e | e <;> rw [e] <;> exact z _ (by decide))
    (by rw [show zPT 6 = 95 from rfl, h95]) (by rw [show zPT 7 = 58 from rfl, z 58 (by decide)])
    (by rw [h31h, h31]; rfl) hR hRh (by rw [hpt]; simp) hX
  rw [show zPT 7 = 58 from rfl, Nat.zero_add, ← hpt] at v1
  have hRg : ∀ r : Fin 112, r ≠ 58 → r ≠ 96 → τ.val r = σ.val r := fun r a b =>
    t1.fr.2.1 r (fun h' => by rcases h' with e | e <;> [exact a (e.trans rfl); exact b e])
  have x2 := rewS_spec cap (Sm 31) 87 89 (by decide) τ B (by rw [hRg 87 (by decide) (by decide), h87])
    (by rw [hRg 89 (by decide) (by decide), z 89 (by decide)]) (by omega)
    (by rw [t1.hO, t1.sO, h31, ← hpt]; simpa using hB)
  refine WExec.cast cap (WExec.seq x1 x2) ?_ le_rfl
  have n031 : (0 : Fin 50) ≠ Sm 31 := by decide
  apply WState.eq
  · funext i
    by_cases hi0 : i = 0
    · subst hi0
      simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_self]
      rw [Function.update_of_ne n031]; exact t1.hI
    · by_cases hi31 : i = Sm 31
      · subst hi31
        simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_self]
        rw [Function.update_of_ne (Ne.symm n031)]; exact h31h.symm
      · simp only [WState.seth_sh, WState.sets_sh, WState.setv_sh, Function.update_of_ne hi0,
          Function.update_of_ne hi31]
        exact (t1.fr.1 i (fun h' => by rcases h' with e | e <;> [exact hi0 e; exact hi31 e])).2
  · funext i
    by_cases hi0 : i = 0
    · subst hi0
      simp only [WState.seth_st, WState.sets_st, WState.setv_st, Function.update_of_ne n031]; exact t1.sI
    · by_cases hi31 : i = Sm 31
      · subst hi31
        simp only [WState.seth_st, WState.sets_st, WState.setv_st, Function.update_self]
        rw [t1.sO, h31, ← hpt, List.nil_append]
      · simp only [WState.seth_st, WState.sets_st, WState.setv_st, Function.update_of_ne hi31]
        exact (t1.fr.1 i (fun h' => by rcases h' with e | e <;> [exact hi0 e; exact hi31 e])).1
  · funext r
    by_cases h1 : r = 96
    · subst h1; simp [c1]
    · by_cases h2 : r = 58
      · subst h2; simp [v1]
      · simp [Function.update_apply, h1, h2, hRg r h2 h1]
  · simp [t1.fr.2.2]

theorem popsP_eq : popsP = .seq (readNatM true 0 91 90 59 94 89) (.seq (FinalPass.Hash4.wcopyR 59 96 89) pT2) := rfl

/-- **The population stage**: `Q 59 = #pops`, the population table (head home), `Q 58` its length, the input past
the population section. -/
theorem popsP_spec (cap : ℕ) (R : SelectionReq) (W B : ℕ) (σ : WState 49 112) (pre rest : List Bool)
    (hI : σ.st 0 = pre ++ (frameP (natWord R.pops.length ++ R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2) ++
      rest)) (hIh : σ.sh 0 = pre.length)
    (hz : ∀ r : Fin 112, (r = 58 ∨ r = 59 ∨ r = 89 ∨ r = 90 ∨ r = 91 ∨ r = 92 ∨ r = 93 ∨ r = 94 ∨ r = 96) →
      σ.val r = 0)
    (h95 : σ.val 95 = 2 * W + 1) (h87 : σ.val 87 = B) (h31 : σ.st (Sm 31) = []) (h31h : σ.sh (Sm 31) = 0)
    (hR : σ.st (Sm 45) = false :: List.replicate W true) (hRh : σ.sh (Sm 45) = 0) (hX : PopsOK R W cap)
    (hB : (popTable W R).length ≤ B) (hcap : 2 ^ (R.pops.length + 2) + R.pops.length + B + 1 ≤ cap) :
    WExec cap popsP σ ((((σ.seth 0 (pre.length + 2 * (natWord R.pops.length ++
      R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2).length)).setv 59 R.pops.length).sets (Sm 31)
        (popTable W R)).setv 58 (popTable W R).length)
      ((natBitLength R.pops.length + 2) * (40 * 2 ^ natBitLength R.pops.length + 40) + 1 + (18 * R.pops.length + 3 + 1 +
        (popsTCost W R.pops + 1 + (B * (1 + 8) + 1 + 1 + (7 * B + 1))))) := by
  have z := hz
  set p := R.pops.length with hp
  have hnb : natBitLength p ≤ p + 1 := natBitLength_le p
  have hpw : 2 ^ (natBitLength p + 1) ≤ 2 ^ (p + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpp : p + 2 ≤ 2 ^ (p + 2) := by have := Nat.lt_two_pow_self (n := p + 2); omega
  have x1 := readNatM_spec cap true 0 91 90 59 94 89 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) p pre
    (frameP (R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2) ++ rest) σ
    (by rw [hI, frameP_append']; simp [PrimAsm.ParseNat.enc, marks_eq, List.append_assoc]) hIh
    (z 91 (by decide)) (z 90 (by decide)) (z 94 (by decide)) (z 89 (by decide))
    (by rw [z 59 (by decide)]; omega)
  rw [z 59 (by decide), Nat.zero_add] at x1
  simp only [PrimAsm.ParseNat.stp, if_true] at x1
  set σ1 := (σ.seth 0 (pre.length + 2 * (natWord p).length)).setv 59 p with hσ1
  have x2 := cp_spec cap 59 96 89 (by decide) (by decide) (by decide) σ1 p (by simp [hσ1])
    (by simp [hσ1, z 96 (by decide)]) (by simp [hσ1, z 89 (by decide)]) (by omega)
  have x3 := pT2_spec cap R W B (σ1.setv 96 p) (pre ++ frameP (natWord p)) rest
    (by simp [hσ1, hI, frameP_append', List.append_assoc, hp]) (by simp [hσ1, frameP_length'])
    (by simp [hp]) (fun r hr => by
      have h59 : r ≠ 59 := by rcases hr with e | e | e | e | e | e | e <;> (subst e; decide)
      have h96 : r ≠ 96 := by rcases hr with e | e | e | e | e | e | e <;> (subst e; decide)
      simp only [hσ1, WState.setv_val, WState.seth_val, Function.update_of_ne h59, Function.update_of_ne h96]
      exact z r (by rcases hr with e | e | e | e | e | e | e <;> simp [e]))
    (by simp [hσ1, h95]) (by simp [hσ1, h87]) (by simpa [hσ1] using h31) (by simpa [hσ1] using h31h)
    (by simpa [hσ1] using hR) (by simpa [hσ1] using hRh) hX hB (by omega)
  rw [popsP_eq]
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 x3)) ?_ le_rfl
  apply WState.eq
  · funext i; by_cases hi : i = 0
    · subst hi; simp [hσ1, frameP_length']; ring
    · simp [hσ1, Function.update_apply, hi]
  · funext i; by_cases hi : i = Sm 31
    · subst hi; simp
    · simp [hσ1, Function.update_apply, hi]
  · funext r; by_cases h1 : r = 96
    · subst h1; simp [hσ1, z 96 (by decide)]
    · simp [hσ1, Function.update_apply, h1]
  · rfl

/-! ## The round counter -/

/-- **`C = 2^k`** (PA's `pow2W` on `(73, 84, 92, 89)`). -/
theorem powP_spec (cap : ℕ) (σ : WState 49 112) (k : ℕ) (h73 : σ.val 73 = k) (h84 : σ.val 84 = 0)
    (h92 : σ.val 92 = 0) (h89 : σ.val 89 = 0) (hcap : 2 ^ (k + 1) ≤ cap) :
    WExec cap (pow2W zPow) σ (σ.setv 84 (2 ^ k)) (k * (18 * 2 ^ k + 7) + 18 * k + 20) := by
  have x := pow2W_spec cap zPow σ (by simp [zPow, h84]) (by simp [zPow, h92]) (by simp [zPow, h89])
    (by simp [zPow, h73, hcap])
  have e0 : σ.val (zPow 0) = k := by simp [zPow, h73]
  rw [e0, show zPow 1 = 84 from rfl] at x
  exact x

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
