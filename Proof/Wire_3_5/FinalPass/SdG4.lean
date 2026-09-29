import Proof.Wire_3_5.FinalPass.SdG3

/-! # S4 (the seeds phase), part 44: S4's run at a THR star call (P3:3044-3048, 3170-3178)

**`run_thrG`**: `run_symG`'s twin at a THR star call (THR's words `8 … 14` and numbers on their streams): S4's machine
steps to a state whose numerator stream holds `frame (binary W thrNum)`, the denominator's stream untouched, every
head and register `0`.

Paper quantity of the main type: the printed THR numerator (P3:3044-3048). -/

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
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 ThrCall rsumThr thrWords thrNums)
open NearCubicWires.WireExponent3_5.FinalPass.Sample (decWord digitsOf)
open NearCubicWires.SupplierPrime NearCubicWires.SupplierPipeline

variable (E : SymPtEval2)

theorem run_thrG (tw sw : ℕ) (win wout : Fin tw) (hio : win ≠ wout) (Mw : Machine tw sw) (cap Bud W T : ℕ)
    (k : ThrCall) (σT : k.P.Translation) (smp : CallSample k.P) (carriers : List (Stars.Carrier k.P.n))
    (hk2 : carriers.length ≤ 2) (FP : GapParams) (σ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs))
    (hW8 : ∀ i : Fin 8, σ.st (fsB (bst (30 + i.val) (by omega))) = Seams.s4Core2 k.P σT smp carriers FP i)
    (hTw : ∀ i : Fin 7, σ.st (fsB (bst (38 + i.val) (by omega))) = thrWords k i)
    (hNt : σ.st (fsB tNumsT) = Data.unaryList (List.ofFn (thrNums k)))
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
    (Qn : QNum cap FP k.P carriers (List.ofFn smp.S) T
      (Fintype.card (ThrEq k.P k.Cs k.alg × PrimeIndex (thrCutoff k.P k.Cs k.alg k.den)))
      (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length)
    (hv16 : ∀ j : ℕ, 8 * (Seams.s4Small2 k.P carriers FP).getD j 0 + 1 ≤ cap)
    (hvn : 8 * k.P.n + 1 ≤ cap) (hvE : 8 * 2 ^ (Seams.s4Small2 k.P carriers FP).getD 11 0 + 1 ≤ cap)
    (hHT : 8 * Hof carriers 0 + 8 * Hof carriers 1 +
      8 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) + 1) +
      8 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) + 1) + 10 ≤ cap)
    (hnums : (Data.unaryList (List.ofFn (thrNums k))).length ≤ cap)
    (hneed : ThrPt.thrPtProg.need (k.P.n + (∑ i, (thrWords k i).length) + ∑ i, thrNums k i) ≤ cap)
    (hBW : NumDen.thrNum k.P σT smp.eqv smp.S k.Cs carriers FP k.alg k.den (ListFast.listReportFast k.D) < 2 ^ W)
    (hBT : NumDen.thrNum k.P σT smp.eqv smp.S k.Cs carriers FP k.alg k.den (ListFast.listReportFast k.D) < 2 ^ T) :
    ∃ τ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs),
      Step (s4M E tw sw win wout Mw) (prepCost (Seams.s4Small2 k.P carriers FP) + 1 + Bud + 1 +
        (bodyA cap E.nn + slCost FP k.P carriers smp.Q k.P.s k.P.b (k.P.r / 2) (k.P.n - k.P.r * k.P.b)
          (ThrPt.thrPtProg.bound (k.P.n + (∑ i, (thrWords k i).length) + ∑ i, thrNums k i) + 1)
          (Fintype.card (ThrEq k.P k.Cs k.alg × PrimeIndex (thrCutoff k.P k.Cs k.alg k.den))) T
          (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length (esOf FP)))
        (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      τ.st (fsB tN) = frame (binary W (NumDen.thrNum k.P σT smp.eqv smp.S k.Cs carriers FP k.alg k.den
        (ListFast.listReportFast k.D))) ∧
      τ.st gD = σ.st gD ∧ (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  refine s4_run E tw sw win wout hio Mw cap Bud W _ _ σ (Seams.s4Small2 k.P carriers FP) rfl
    (TabW.tabWord FP (Seams.carLen carriers 0) (Seams.carLen carriers 1) ++ [false])
    (by have := hW8 7; exact this) (hblank _ (by show (28 : ℕ) < 30; omega) (by show (28 : ℕ) ≠ 0; omega))
    (hblank _ (by show (27 : ℕ) < 30; omega) (by show (27 : ℕ) ≠ 0; omega)) hWx hsh hreg hcap
    (by rw [ppReq_s4]; exact hwr) ?_
  intro σ0 h1 h2 h3 h4 h5 h6 h7 h8
  have H := preset_of E tw k.P σT smp carriers FP W σ hW8 hN hblank hSc2 hcell σ0 h1 h2 h3 h4 h5 h7 h8
  have hv8 := hv8_of E cap _ _ _ σ0 h4 h5 h6 h7 hv16 (by rw [ppN_s4]; exact hvn) hvE
  have hVle : ∀ c a b, VfOf k.P smp.eqv (rsumThr k.P k.Cs k.alg k.den (ListFast.listReportFast k.D)) c a b ≤
      Fintype.card (ThrEq k.P k.Cs k.alg × PrimeIndex (thrCutoff k.P k.Cs k.alg k.den)) :=
    fun c a b => by
      unfold VfOf Seams.rsumThr
      exact le_trans (Finset.sum_le_sum (fun gp _ => Bool.toNat_le _)) (by simp)
  exact bodyW_thr E cap k σT smp carriers hk2 FP W T
    (Fintype.card (ThrEq k.P k.Cs k.alg × PrimeIndex (thrCutoff k.P k.Cs k.alg k.den)))
    (NumDen.thrNum k.P σT smp.eqv smp.S k.Cs carriers FP k.alg k.den (ListFast.listReportFast k.D)) σ0 H
    (fun i => by
      rw [h1 _ (by show 38 + i.val ≠ 27; omega) (by show 38 + i.val ≠ 28; omega)]
      exact hTw i)
    (by rw [h1 _ (by show (45 : ℕ) ≠ 27; omega) (by show (45 : ℕ) ≠ 28; omega)]; exact hNt)
    hdl hdr hVle Qn hv8 hHT hnums hneed hBW hBT le_rfl

end NearCubicWires.WireExponent3_5.FinalPass.Sd
