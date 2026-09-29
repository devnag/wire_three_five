import Proof.Wire_3_5.FinalPass.SdG2

/-! # S4 (the seeds phase), part 43: S4's run at a SYM star call (P3:3044-3048, 3170-3178)

`preset_of`: after the prep and the tables writer, the body's state is `PreSet` (part 36). **`run_symG`**: S4's
machine from an entry state at a SYM star call (S4's words `s4Core2` on the body's word streams, the SYM evaluator's
words and numbers on theirs, word `13` blank, the numerator's zero, every other stream blank, every head and register
`0`, a blank cell), given the tables writer's run on the call's request and the numeric side conditions, steps to a
state whose numerator stream holds `frame (binary W symNum)`, the denominator's stream untouched, every head and
register `0`.

Paper quantity of the main type: the printed SYM numerator (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 SymCall rsumSym)
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decWord digitsOf)

variable (E : SymPtEval2)

/-- The body state after the prep and the writer is `PreSet` (streams below the words blank but the numerator). -/
theorem preset_of (tw : ℕ) (P : StarParams) (σT : P.Translation) (smp : CallSample P)
    (carriers : List (Stars.Carrier P.n)) (FP : GapParams) (W : ℕ) (σ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs))
    (hW8 : ∀ i : Fin 8, σ.st (fsB (bst (30 + i.val) (by omega))) = Seams.s4Core2 P σT smp carriers FP i)
    (hN : σ.st (fsB tN) = frame (binary W 0))
    (hblank : ∀ i : Fin (bns E.nw E.nsc + 1), i.val < 30 → i.val ≠ 0 → σ.st (fsB i) = [])
    (hSc2 : ∀ i : Fin (bns E.nw E.nsc + 1), 47 + E.nw ≤ i.val → σ.st (fsB i) = []) (hcell : σ.cell = false)
    (σ0 : BS E.nw E.nn E.nsc E.nrs)
    (h1 : ∀ j : Fin (bns E.nw E.nsc + 1), j.val ≠ 27 → j.val ≠ 28 → σ0.st j = σ.st (fsB j))
    (h2 : σ0.st tTW = TabW.tabWord FP (Seams.carLen carriers 0) (Seams.carLen carriers 1) ++ [false])
    (h3 : ∀ j, σ0.sh j = 0)
    (h4 : ∀ k : Fin 16, σ0.val (sRp ⟨k.val, by omega⟩) = (Seams.s4Small2 P carriers FP).getD k.val 0)
    (h5 : σ0.val (sRp 17) = ppN (Seams.s4Small2 P carriers FP)) (h7 : ∀ q, ¬ IsPrepReg q → σ0.val q = 0)
    (h8 : σ0.cell = σ.cell) : PreSet P σT smp carriers FP W σ0 := by
  have hjob : ∀ j ∈ (sJobs : List (FlJob (bns E.nw E.nsc) (bnr E.nn E.nrs))), j.o.val < 30 ∧ j.o.val ≠ 0 ∧
      j.o.val ≠ 27 ∧ j.o.val ≠ 28 := by
    intro j hj
    simp only [sJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [tU, tV, tC, tRow, tCol, tX, tZ, tPos, tNeg, tT, bst]
  refine
    { R := h7, Rp := h4, Rn := by rw [h5, ppN_s4], W8 := fun i => ?_, N := ?_, TW := ?_, E := fun j hj => ?_,
      Sp := ?_, Sc := fun i hi => ?_, sh := h3, cell := by rw [h8, hcell] }
  · rw [h1 _ (by show 30 + i.val ≠ 27; omega) (by show 30 + i.val ≠ 28; omega)]
    exact hW8 i
  · rw [h1 tN (by show (0 : ℕ) ≠ 27; omega) (by show (0 : ℕ) ≠ 28; omega)]
    exact hN
  · rw [h2, tabWord_twW]
  · obtain ⟨a1, a2, a3, a4⟩ := hjob j hj
    rw [h1 _ a3 a4]
    exact hblank _ a1 a2
  · rw [h1 tSp (by show (4 : ℕ) ≠ 27; omega) (by show (4 : ℕ) ≠ 28; omega)]
    exact hblank _ (show (4 : ℕ) < 30 by omega) (show (4 : ℕ) ≠ 0 by omega)
  · unfold IsSc at hi
    rw [h1 i (by omega) (by omega)]
    rcases hi with hi | hi
    · exact hblank i (by omega) (by omega)
    · exact hSc2 i hi

/-- The prep's registers after the prep and the writer, within the capacity. -/
theorem hv8_of (cap : ℕ) (vs : List ℕ) (nv ev : ℕ) (σ0 : BS E.nw E.nn E.nsc E.nrs)
    (h4 : ∀ k : Fin 16, σ0.val (sRp ⟨k.val, by omega⟩) = vs.getD k.val 0) (h5 : σ0.val (sRp 17) = nv)
    (h6 : σ0.val (sRp 18) = ev) (h7 : ∀ q, ¬ IsPrepReg q → σ0.val q = 0)
    (hv16 : ∀ j : ℕ, 8 * vs.getD j 0 + 1 ≤ cap) (hvn : 8 * nv + 1 ≤ cap) (hvE : 8 * ev + 1 ≤ cap) :
    ∀ j : Fin 30, 8 * σ0.val (sRp j) + 1 ≤ cap := by
  intro j
  by_cases hj : j.val < 16
  · have e : σ0.val (sRp j) = vs.getD j.val 0 := h4 ⟨j.val, hj⟩
    rw [e]; exact hv16 _
  · by_cases h17 : j.val = 17
    · rw [show j = 17 from Fin.ext h17, h5]; exact hvn
    · by_cases h18 : j.val = 18
      · rw [show j = 18 from Fin.ext h18, h6]; exact hvE
      · have hz : σ0.val (sRp j) = 0 := h7 _ (fun ⟨k', hk16, hk19, hk⟩ => by
          have := congrArg Fin.val hk
          simp [sRp_b, brg] at this
          omega)
        rw [hz]
        have := hvE
        omega

theorem run_symG (tw sw : ℕ) (win wout : Fin tw) (hio : win ≠ wout) (Mw : Machine tw sw) (cap Bud W T : ℕ)
    (k : SymCall) (σT : k.P.Translation) (smp : CallSample k.P) (carriers : List (Stars.Carrier k.P.n))
    (hk2 : carriers.length ≤ 2) (FP : GapParams) (σ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs))
    (hW8 : ∀ i : Fin 8, σ.st (fsB (bst (30 + i.val) (by omega))) = Seams.s4Core2 k.P σT smp carriers FP i)
    (h13 : σ.st (fsB (bst 43 (by omega))) = [])
    (hSw : ∀ i : Fin E.nw, σ.st (fsB (SSe (.inr (.inl i)))) = E.words k i)
    (hNs : σ.st (fsB tNumsS) = Data.unaryList (List.ofFn (E.nums k)))
    (hN : σ.st (fsB tN) = frame (binary W 0))
    (hblank : ∀ i : Fin (bns E.nw E.nsc + 1), i.val < 30 → i.val ≠ 0 → σ.st (fsB i) = [])
    (hSc2 : ∀ i : Fin (bns E.nw E.nsc + 1), 47 + E.nw ≤ i.val → σ.st (fsB i) = [])
    (hWx : ∀ x, x ≠ win → x ≠ wout → σ.st (tmW win wout x) = [])
    (hsh : ∀ i, σ.sh i = 0) (hreg : ∀ q, σ.val q = 0) (hcell : σ.cell = false)
    (hwr : WriterIfaceJ.WriterRun Mw Bud win wout
      (TabW.reqT k.P.n FP.len FP.cap FP.errExp (Seams.carLen carriers 0) (Seams.carLen carriers 1)
        (Fintype.card (GapSeed FP))) (TabW.tabWord FP (Seams.carLen carriers 0) (Seams.carLen carriers 1) ++ [false]))
    (hdl : ∀ a : Fin smp.N, decWord k.P.b (k.P.r / 2) (k.P.n - k.P.r * k.P.b) false
      (digitsOf k.P.s (k.P.r / 2) (binary (k.P.s * (k.P.r / 2)) a)) = List.ofFn (euOf k.P smp.eqv a))
    (hdr : ∀ b : Fin smp.N, decWord k.P.b (k.P.r / 2) (k.P.n - k.P.r * k.P.b) true
      (digitsOf k.P.s (k.P.r / 2) (binary (k.P.s * (k.P.r / 2)) b)) = List.ofFn (evOf k.P smp.eqv b))
    (hcap : (Data.unaryList (Seams.s4Small2 k.P carriers FP)).length + ppN (Seams.s4Small2 k.P carriers FP) +
      2 ^ ((Seams.s4Small2 k.P carriers FP).getD 11 0 + 1) + 4 * (ppReq (Seams.s4Small2 k.P carriers FP)).length +
      10 ≤ cap)
    (Qn : QNum cap FP k.P carriers (List.ofFn smp.S) T (Fintype.card k.Pl.FlatSeed)
      (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length)
    (hv16 : ∀ j : ℕ, 8 * (Seams.s4Small2 k.P carriers FP).getD j 0 + 1 ≤ cap)
    (hvn : 8 * k.P.n + 1 ≤ cap) (hvE : 8 * 2 ^ (Seams.s4Small2 k.P carriers FP).getD 11 0 + 1 ≤ cap)
    (hHT : 8 * Hof carriers 0 + 8 * Hof carriers 1 +
      8 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) + 1) +
      8 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) + 1) + 10 ≤ cap)
    (hnums : (Data.unaryList (List.ofFn (E.nums k))).length ≤ cap)
    (hneed : E.need (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) ≤ cap)
    (hBW : NumDen.symNum k.P σT smp.eqv smp.S k.Cs carriers FP k.Pl < 2 ^ W)
    (hBT : NumDen.symNum k.P σT smp.eqv smp.S k.Cs carriers FP k.Pl < 2 ^ T) :
    ∃ τ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs),
      Step (s4M E tw sw win wout Mw) (prepCost (Seams.s4Small2 k.P carriers FP) + 1 + Bud + 1 +
        (bodyA cap E.nn + slCost FP k.P carriers smp.Q k.P.s k.P.b (k.P.r / 2) (k.P.n - k.P.r * k.P.b)
          (E.bound (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) + 1) (Fintype.card k.Pl.FlatSeed) T
          (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length (esOf FP)))
        (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      τ.st (fsB tN) = frame (binary W (NumDen.symNum k.P σT smp.eqv smp.S k.Cs carriers FP k.Pl)) ∧
      τ.st gD = σ.st gD ∧ (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  refine s4_run E tw sw win wout hio Mw cap Bud W _ _ σ (Seams.s4Small2 k.P carriers FP) rfl
    (TabW.tabWord FP (Seams.carLen carriers 0) (Seams.carLen carriers 1) ++ [false])
    (by have := hW8 7; exact this) (hblank _ (by show (28 : ℕ) < 30; omega) (by show (28 : ℕ) ≠ 0; omega))
    (hblank _ (by show (27 : ℕ) < 30; omega) (by show (27 : ℕ) ≠ 0; omega)) hWx hsh hreg hcap
    (by rw [ppReq_s4]; exact hwr) ?_
  intro σ0 h1 h2 h3 h4 h5 h6 h7 h8
  have H := preset_of E tw k.P σT smp carriers FP W σ hW8 hN hblank hSc2 hcell σ0 h1 h2 h3 h4 h5 h7 h8
  have hv8 := hv8_of E cap _ _ _ σ0 h4 h5 h6 h7 hv16 (by rw [ppN_s4]; exact hvn) hvE
  have hVle : ∀ c a b, VfOf k.P smp.eqv (rsumSym k.P k.Cs k.Pl) c a b ≤ Fintype.card k.Pl.FlatSeed :=
    fun c a b => by
      unfold VfOf Seams.rsumSym
      exact le_trans (Finset.sum_le_sum (fun el _ => Bool.toNat_le _)) (by simp)
  exact bodyW_sym E cap k σT smp carriers hk2 FP W T (Fintype.card k.Pl.FlatSeed)
    (NumDen.symNum k.P σT smp.eqv smp.S k.Cs carriers FP k.Pl) σ0 H
    (fun i => by
      rw [h1 _ (by show 46 + i.val ≠ 27; omega) (by show 46 + i.val ≠ 28; omega)]
      exact hSw i)
    (by rw [h1 _ (by show (43 : ℕ) ≠ 27; omega) (by show (43 : ℕ) ≠ 28; omega)]; exact h13)
    (by rw [h1 _ (by show 46 + E.nw ≠ 27; omega) (by show 46 + E.nw ≠ 28; omega)]; exact hNs)
    hdl hdr hVle Qn hv8 hHT hnums hneed hBW hBT le_rfl

end NearCubicWires.WireExponent3_5.FinalPass.Sd
