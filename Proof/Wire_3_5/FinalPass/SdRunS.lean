import Proof.Wire_3_5.FinalPass.SdRunA

/-! # S4 (the seeds phase), part 39: the body after the tables writer, at a SYM star call (P3:3044-3048, 3170-3178)

**`bodyW E = setRS ; ldMode ; loopTd E`**. **`bodyW_sym`**: from the body state after the prep and the tables writer
at a SYM star call (`PreSet`, the SYM evaluator's words and numbers in place, word `13` blank), under the seed
loop's numeric hypotheses (`QNum`), the numerator stream holds `frame (binary W symNum)` (the printed SYM numerator,
`num_sym`), every register is `0`, the heads as at entry; within the setup's, the teardown's and the seed loop's steps.

Paper quantity of the main type: the printed numerator `symNum = Σ_c Σ_e Σ_ℓ M(e,x)·Σ R̂(x)` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 SymCall rsumSym)
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decWord digitsOf)

theorem nj (v : ℕ) (h : 26 < v) : v ≠ 1 ∧ v ≠ 2 ∧ v ≠ 3 ∧ (v < 8 ∨ 17 < v) ∧ v ≠ 25 ∧ v ≠ 26 := by omega

section Body
variable {nw nn nsc nrs : ℕ}
variable {P : StarParams} {σT : P.Translation} {smp : CallSample P} {carriers : List (Stars.Carrier P.n)}
  {FP : GapParams} {W : ℕ} {σ0 : BS nw nn nsc nrs}

theorem omS_le (cap : ℕ) (H : PreSet P σT smp carriers FP W σ0) (e0 : GapSeed FP)
    (hv : ∀ k : Fin 30, σ0.val (sRp k) ≤ cap) (hc1 : 1 ≤ cap) (q : Fin (bnr nn nrs)) :
    (omS P carriers FP σ0 e0).val q ≤ cap := by
  by_cases hq : q ∈ (seedFix : List (Fin (bnr nn nrs)))
  · simp only [seedFix, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (setRS_cp σ0 _ _ _ _ (sRp 1, ctrR 0) (by simp [cps])).trans_le (hv 1)
    · exact (setRS_cp σ0 _ _ _ _ (sRp 2, ctrR 1) (by simp [cps])).trans_le (hv 2)
    · exact (setRS_cp σ0 _ _ _ _ (sRp 3, ctrR 2) (by simp [cps])).trans_le (hv 3)
    · exact (setRS_cp σ0 _ _ _ _ (sRp 4, ctrR 3) (by simp [cps])).trans_le (hv 4)
    · exact (setRS_cp σ0 _ _ _ _ (sRp 5, ctrR 4) (by simp [cps])).trans_le (hv 5)
    · exact (setRS_cp σ0 _ _ _ _ (sRp 2, frD 0) (by simp [cps])).trans_le (hv 2)
    · exact (setRS_cp σ0 _ _ _ _ (sRp 1, frD 1) (by simp [cps])).trans_le (hv 1)
    · exact (setRS_cp σ0 _ _ _ _ (sRp 3, frD 2) (by simp [cps])).trans_le (hv 3)
    · exact (setRS_cp σ0 _ _ _ _ (sRp 6, frD 3) (by simp [cps])).trans_le (hv 6)
    · unfold omS; rw [setRS_rP]
      have h01 : ∀ x : ℕ, (if 1 ≤ x then 1 else 0) ≤ 1 := fun x => by split_ifs <;> omega
      exact le_trans (h01 _) hc1
    · unfold omS; rw [setRS_rP]
      have h01 : ∀ x : ℕ, (if 2 ≤ x then 1 else 0) ≤ 1 := fun x => by split_ifs <;> omega
      exact le_trans (h01 _) hc1
  · unfold omS; rw [setRS_val_zero σ0 _ _ _ _ H.R q hq]; exact Nat.zero_le _

end Body

variable (E : SymPtEval2)

/-- **The body after the tables writer**: the setup, the evaluator's numbers, the loops, the teardown. -/
noncomputable def bodyW : BP E.nw E.nn E.nsc E.nrs := .seq setRS (.seq ldMode (loopTd E))

/-- The body's steps besides the seed loop's. -/
def bodyA (cap nn : ℕ) : ℕ := 2300 * (cap + 1) + 16 * cap + 20 + tdCost cap nn

theorem bodyW_sym (cap : ℕ) (k : SymCall) (σT : k.P.Translation) (smp : CallSample k.P)
    (carriers : List (Stars.Carrier k.P.n)) (hk2 : carriers.length ≤ 2) (FP : GapParams) (W T Vm Bd : ℕ)
    (σ0 : BS E.nw E.nn E.nsc E.nrs) (H : PreSet k.P σT smp carriers FP W σ0)
    (hSw : ∀ i : Fin E.nw, σ0.st (SSe (.inr (.inl i))) = E.words k i)
    (h13 : σ0.st (bst 43 (by omega)) = [])
    (hNs : σ0.st tNumsS = Data.unaryList (List.ofFn (E.nums k)))
    (hdl : ∀ a : Fin smp.N, decWord k.P.b (k.P.r / 2) (k.P.n - k.P.r * k.P.b) false
      (digitsOf k.P.s (k.P.r / 2) (binary (k.P.s * (k.P.r / 2)) a)) = List.ofFn (euOf k.P smp.eqv a))
    (hdr : ∀ b : Fin smp.N, decWord k.P.b (k.P.r / 2) (k.P.n - k.P.r * k.P.b) true
      (digitsOf k.P.s (k.P.r / 2) (binary (k.P.s * (k.P.r / 2)) b)) = List.ofFn (evOf k.P smp.eqv b))
    (hVle : ∀ c a b, VfOf k.P smp.eqv (rsumSym k.P k.Cs k.Pl) c a b ≤ Vm)
    (Qn : QNum cap FP k.P carriers (List.ofFn smp.S) T Vm
      (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length)
    (hv8 : ∀ j : Fin 30, 8 * σ0.val (sRp j) + 1 ≤ cap)
    (hHT : 8 * Hof carriers 0 + 8 * Hof carriers 1 +
      8 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) + 1) +
      8 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) + 1) + 10 ≤ cap)
    (hnums : (Data.unaryList (List.ofFn (E.nums k))).length ≤ cap)
    (hneed : E.need (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) ≤ cap)
    (hBW : Bd < 2 ^ W) (hBT : Bd < 2 ^ T)
    (hb : NumDen.symNum k.P σT smp.eqv smp.S k.Cs carriers FP k.Pl ≤ Bd) :
    ∃ ω : BS E.nw E.nn E.nsc E.nrs, ∃ m, WExec cap (bodyW E) σ0 ω m ∧
      m ≤ bodyA cap E.nn + slCost FP k.P carriers smp.Q k.P.s k.P.b (k.P.r / 2) (k.P.n - k.P.r * k.P.b)
        (E.bound (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) + 1) Vm T
        (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length (esOf FP) ∧
      ω.st tN = frame (binary W (NumDen.symNum k.P σT smp.eqv smp.S k.Cs carriers FP k.Pl)) ∧
      ω.sh = σ0.sh ∧ (∀ q, ω.val q = 0) := by
  have hv : ∀ j : Fin 30, σ0.val (sRp j) ≤ cap := fun j => by have := hv8 j; omega
  have hc2 := Qn.c2
  obtain ⟨e0, rest, h2⟩ := twW_two FP (Seams.carLen carriers 0) (Seams.carLen carriers 1)
  have hTW0 : σ0.st tTW = frameP (tb FP e0 (Seams.carLen carriers 0)) ++ false ::
      (frameP (tb FP e0 (Seams.carLen carriers 1)) ++ false :: rest) := by rw [H.TW, h2]
  have hGk : ∀ kk : Fin 2, σ0.st (tG kk) = Seams.carTab carriers kk.val := fun kk => by
    have e2 := H.W8 ⟨2 + kk.val, by omega⟩
    have e3 : Seams.s4Core2 k.P σT smp carriers FP ⟨2 + kk.val, by omega⟩ = Seams.carTab carriers kk.val := by
      fin_cases kk <;> rfl
    rw [show (tG kk : Fin (bns E.nw E.nsc + 1)) = bst (30 + (⟨2 + kk.val, by omega⟩ : Fin 8).val) (by omega) from
      Fin.ext (by simp [tG, bst]; omega), e2, e3]
  have hG : ∀ kk : Fin 2, (∃ w rest, σ0.st (tG kk) = true :: (frameP w ++ false :: rest) ∧
      w.length = Hof carriers kk) ∨ (readTapeBit (σ0.st (tG kk)) 0 = false ∧ Hof carriers kk = 0) := fun kk => by
    rw [hGk kk]; exact carTab_H carriers kk
  have hT0 := tab_len FP e0 (Seams.carLen carriers 0)
  have hT1 := tab_len FP e0 (Seams.carLen carriers 1)
  have hl0 : (tb FP e0 (Seams.carLen carriers 0)).length =
      FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) + 1 := hT0
  have hl1 : (tb FP e0 (Seams.carLen carriers 1)).length =
      FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) + 1 := hT1
  -- the setup
  obtain ⟨m1, e1, hm1⟩ := setRS_spec cap σ0 (Hof carriers 0) (Hof carriers 1) (tb FP e0 (Seams.carLen carriers 0))
    (tb FP e0 (Seams.carLen carriers 1)) rest H.R hv8 (hG 0) (hG 1) (fun kk => H.sh _) hTW0 (H.sh _)
    (fun j hj => ⟨H.E j hj, H.sh _⟩) H.Sp (H.sh _) (by rw [hl0, hl1]; omega)
  have hm1' := setRS_cost_le cap σ0 (Hof carriers 0) (Hof carriers 1) (tb FP e0 (Seams.carLen carriers 0)).length
    (tb FP e0 (Seams.carLen carriers 1)).length hv (by omega) (by omega) (by rw [hl0]; omega) (by rw [hl1]; omega)
  -- the evaluator's numbers
  have sS : ∀ i : Fin (bns E.nw E.nsc + 1),
      (i.val ≠ 1 ∧ i.val ≠ 2 ∧ i.val ≠ 3 ∧ (i.val < 8 ∨ 17 < i.val) ∧ i.val ≠ 25 ∧ i.val ≠ 26) → i.val ≠ 4 →
      (omS k.P carriers FP σ0 e0).st i = σ0.st i := fun i h h4 => omS_st_other i h h4
  obtain ⟨ωQ, m2, e2, hm2, sQ, hQ, vQ, oQ, lQ⟩ := ldMode_sym cap (omS k.P carriers FP σ0 e0) (List.ofFn (E.nums k))
    (by simp) (by
      rw [show (tMode : Fin (bns E.nw E.nsc + 1)) = bst 43 (by omega) from rfl,
        sS (bst 43 (by omega)) (nj 43 (by omega)) (by show (43 : ℕ) ≠ 4; omega), h13]
      rfl)
    (by rw [sS tNumsS (nj (46 + E.nw) (by omega)) (by show 46 + E.nw ≠ 4; omega)]; exact hNs)
    (by unfold omS; rw [setRS_sh]; exact H.sh _)
    (fun r hr => omS_zero H.R r (Or.inr (Or.inr (Or.inr (by have := symRegs_mem r hr; omega)))))
    (omS_zero H.R Sd.sC (Or.inl (show (43 : ℕ) < 120 by omega))) hnums
  have hstQ : ωQ.st = (omS k.P carriers FP σ0 e0).st := sQ
  have hshQ : ωQ.sh = (omS k.P carriers FP σ0 e0).sh := hQ
  have hvQ : ∀ q, q ∉ (thrRegs : List (Fin (bnr E.nn E.nrs))) → q ∉ (symRegs : List (Fin (bnr E.nn E.nrs))) →
      ωQ.val q = (omS k.P carriers FP σ0 e0).val q := fun q _ h => oQ q h
  have hCS := cstat_of cap hc2 H ωQ hstQ hshQ hvQ
  obtain ⟨hP0, hF0, hRT, hRB, hTWQ, hZQ⟩ := entry_misc H ωQ hstQ hshQ hvQ
  have hcellQ : ωQ.cell = false := by rw [lQ]; unfold omS; rw [setRS_cell]; exact H.cell
  -- the evaluator at every center and pair
  have hnotS : ∀ j : Fin E.nrs, (RSe (.inr (.inr j)) : Fin (bnr E.nn E.nrs)) ∉ (symRegs : List (Fin (bnr E.nn E.nrs))) := by
    intro j hm
    rw [symRegs, List.mem_ofFn] at hm
    obtain ⟨i, hi⟩ := hm
    have := congrArg Fin.val hi
    simp [RSe, rSv] at this
    omega
  have hkept : ∀ i : Fin (bns E.nw E.nsc + 1), KeptC i → i ≠ tT 0 → i ≠ tT 1 → i.val ≠ 4 →
      (i.val ≠ 1 ∧ i.val ≠ 2 ∧ i.val ≠ 3 ∧ (i.val < 8 ∨ 17 < i.val) ∧ i.val ≠ 25 ∧ i.val ≠ 26) → ωQ.st i = σ0.st i :=
    fun i _ _ _ h4 h => by rw [hstQ]; exact omS_st_other i h h4
  have QH : QHyp E cap FP k.P σT carriers (List.ofFn smp.S) (euOf k.P smp.eqv) (evOf k.P smp.eqv)
      (VfOf k.P smp.eqv (rsumSym k.P k.Cs k.Pl)) k.P.s k.P.b (k.P.r / 2) (k.P.n - k.P.r * k.P.b) T
      (E.bound (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) + 1) Vm ωQ :=
    { R := hCS, bs := k.P.b_succ, n := n_split k.P, kh := kh_pos k.P, dl := hdl, dr := hdr,
      evq := fun ωR0 hst0 hsh0 hval0 hcell0 c a b ω₀ hPt => by
        refine evC_sym E cap k smp.eqv ωR0 (fun i => ?_) ?_ (fun i => ?_) (fun j => ?_) ?_ (fun i => ?_) ?_ hneed
          c a b ω₀ hPt
        · have hKi : KeptC (SSe (.inr (.inl i)) : Fin (bns E.nw E.nsc + 1)) :=
            keptC_of _ (by show 46 + i.val ≠ 0; omega) (by show 46 + i.val ≠ 1; omega)
              (by show 46 + i.val ≠ 2; omega) (by show 46 + i.val ≠ 3; omega)
              (Or.inr (show 25 ≤ 46 + i.val by omega)) (by show 46 + i.val ≠ 25; omega)
              (by show 46 + i.val ≠ 26; omega) (show 46 + i.val < 47 + E.nw by omega)
          rw [hst0 _ hKi (ne_of_val (show 46 + i.val ≠ 8 by omega)) (ne_of_val (show 46 + i.val ≠ 9 by omega)),
            hstQ, omS_st_other _ (nj (46 + i.val) (by omega)) (by show 46 + i.val ≠ 4; omega)]
          exact hSw i
        · have hKi : KeptC (bst (30 + 13) (by omega) : Fin (bns E.nw E.nsc + 1)) :=
            keptC_of _ (by show (43 : ℕ) ≠ 0; omega) (by show (43 : ℕ) ≠ 1; omega) (by show (43 : ℕ) ≠ 2; omega)
              (by show (43 : ℕ) ≠ 3; omega) (Or.inr (show 25 ≤ 43 by omega)) (by show (43 : ℕ) ≠ 25; omega)
              (by show (43 : ℕ) ≠ 26; omega) (show 43 < 47 + E.nw by omega)
          rw [hst0 _ hKi (ne_of_val (show (43 : ℕ) ≠ 8 by omega)) (ne_of_val (show (43 : ℕ) ≠ 9 by omega)),
            hstQ, omS_st_other _ (nj 43 (by omega)) (by show (43 : ℕ) ≠ 4; omega)]
          exact h13
        · rw [hval0 _ (ne_of_val (show 220 + i.val ≠ 203 by omega)) (ne_of_val (show 220 + i.val ≠ 202 by omega))]
          rw [vQ i]
          simp
        · rw [hval0 _ (ne_of_val (show 220 + E.nn + j.val ≠ 203 by omega))
            (ne_of_val (show 220 + E.nn + j.val ≠ 202 by omega))]
          rw [oQ _ (hnotS j)]
          exact omS_zero H.R _ (Or.inr (Or.inr (Or.inr (show 172 < 220 + E.nn + j.val by omega))))
        · rw [hval0 _ (ne_of_val (show (0 : ℕ) ≠ 203 by omega)) (ne_of_val (show (0 : ℕ) ≠ 202 by omega))]
          exact hCS.acc
        · rw [hsh0, hshQ]; unfold omS; rw [setRS_sh]; exact H.sh i
        · rw [hcell0, hcellQ],
      Vle := hVle, Vc := Qn.Vc, capT := Qn.capT, cs := Qn.cs, p := Qn.p, c8 := Qn.c8, dT := Qn.dT, c2 := Qn.cc2,
      mkc := Qn.mkc, regT := hRT, regB := hRB, twc := by rw [hTWQ]; exact Qn.twc }
  have hcQ : ∀ q, ωQ.val q ≤ cap := fun q => by
    by_cases hq : q ∈ (symRegs : List (Fin (bnr E.nn E.nrs)))
    · rw [symRegs, List.mem_ofFn] at hq
      obtain ⟨i, rfl⟩ := hq
      rw [symReg_eq, vQ i]
      exact le_trans (ppUl_getD _ _) hnums
    · rw [oQ q hq]; exact omS_le cap H e0 hv (by omega) q
  have hsum : ((esOf FP).map fun e => Gs FP e k.P σT carriers (List.ofFn smp.S) (euOf k.P smp.eqv)
      (evOf k.P smp.eqv) (VfOf k.P smp.eqv (rsumSym k.P k.Cs k.Pl))).sum =
      NumDen.symNum k.P σT smp.eqv smp.S k.Cs carriers FP k.Pl :=
    num_sym k.P σT smp.eqv smp.S carriers FP k.Cs k.Pl hk2 (Enum.gapSeedEquiv FP).symm
  obtain ⟨ω, m3, e3, hm3, hN3, hsh3, hv3, _, _⟩ := loopTd_spec E cap FP k.P σT carriers (List.ofFn smp.S)
    (euOf k.P smp.eqv) (evOf k.P smp.eqv) (VfOf k.P smp.eqv (rsumSym k.P k.Cs k.Pl)) k.P.s k.P.b (k.P.r / 2)
    (k.P.n - k.P.r * k.P.b) W T _ Vm Bd ωQ QH hBW hBT (esOf FP) (sdinv_of H ωQ hstQ hshQ hvQ) hP0 hF0 hTWQ
    (by rw [hsum]; exact hb) hZQ hcQ
  refine ⟨ω, _, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, hv3⟩
  · rw [hTWQ, List.length_ofFn] at hm3
    unfold bodyA
    omega
  · rw [hN3, hsum]
  · rw [hsh3, hshQ]; unfold omS; rw [setRS_sh]

end NearCubicWires.WireExponent3_5.FinalPass.Sd
