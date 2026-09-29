import Proof.Wire_3_5.Primitive.Writers.SymDecUnit

/-! # PA (d)-SYM, (iv): the SYM writer loop's emission and per-unit budget

The writer loop (`CellLoopD.loop_stepD`, `ShellDRun.shell_runD`) runs `b` units and prints
`(List.range b).flatMap emit ++ [false]`; its decode contract `hdec` asks, at every unit `j < b` and output `out`, for
`DecOK` with `emit j` within the per-unit budget `nU`.

* `flatMap_unitE`: past the tape's `TOT ≤ b` units the loop prints nothing, so its output is the tape's units;
* **`sym_loop_tape`**: at a SYM call, the loop's output closed by `false` is C4's `BAT` word `symTape` (with
  `SymFlat.symTape_flat`);
* `symNU` (the per-unit budget: copy-in, the decode's bound, the pipeline bound `BP`, the counter at `b`);
* **`sym_hdec`**: `shell_runD`'s `hdec` for the SYM unit decode `decW`, the emission `unitE`, at `symNU`.

Paper quantities of the main type: C4's `BAT` word of the call (`symTape`, P3:3011-3016) and the writer's per-unit
time (lem:primitive P3:3068-3084). -/

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
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.PrimAsm.Enum
open NearCubicWires.WireExponent3_5.PrimAsm.SymDecEnum
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces

/-- **Past the tape's units the loop prints nothing.** -/
theorem flatMap_unitE (TOT R M : ℕ) (rq : ℕ → ℕ → ℕ → List Bool) (b : ℕ) (h : TOT ≤ b) :
    (List.range b).flatMap (unitE TOT R M rq) = (List.range TOT).flatMap (SymFlat.symEmit R M rq) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  have h1 : (List.range TOT).flatMap (unitE TOT R M rq) = (List.range TOT).flatMap (SymFlat.symEmit R M rq) :=
    List.flatMap_congr fun j hj => by unfold unitE; rw [if_pos (List.mem_range.mp hj)]
  have h2 : (List.range k).flatMap (fun i => unitE TOT R M rq (TOT + i)) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro i _
    unfold unitE
    rw [if_neg (by omega)]
  rw [h1, h2, List.append_nil]

section Loop
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
variable (cap : ℕ) (W : WalkBankProducer)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}

/-- **The SYM writer loop's output is the call's `BAT` word**: `b ≥ TOT` units, closed by `false`. -/
theorem sym_loop_tape (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (b : ℕ)
    (hb : (symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 * ((carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2)) ≤ b) :
    (List.range b).flatMap (unitE (symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 * ((carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2)) (carriers.length + 2 * a) (symListParams I n a Cs carriers).M (SymFlat.symCallUnit I hs Cs carriers)) ++ [false] = WriterIface.symTape I hs Cs carriers := by
  rw [flatMap_unitE _ _ _ _ _ hb]
  exact SymFlat.symTape_flat I hs Cs carriers

/-- **The SYM writer loop's per-unit budget**: the copy-in of the counts, the decode's bound `Dc`, the pipeline bound
`BP`, the counter's increment at `b`. -/
def symNU (ul Dc BP b : ℕ) : ℕ := CellLoopD.cpCost ul + 1 + (Dc + 1 + (BP + 4) + 1 + (3 * b + 3))

/-- **The SYM unit decode meets the writer loop's contract** (`ShellDRun.shell_runD`'s `hdec`) at every unit `j < b`
and output `out`, with the emission `unitE` and the budget `symNU`. -/
theorem sym_hdec (F : FiltSetupSpec5 W) (pb : WM (LNS W.x) LNR) (cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)
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
    (hP : ∀ j < b, ∀ (out : List Bool) (σ : WState (LNS W.x) LNR), Decoded W.x cap σ w out j (Data.unaryList (Data.symCounts a Cs carriers)) n a
        carriers.length (cyOf Cs).sum ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
        ((cyOf Cs).getD 3 0) ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)
        (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs)) →
      IsPopU (totV n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n)
        (SeedFix.callKh (I.starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
        ((cyOf Cs).getD 3 0)) (carriers.length + 2 * a) (cyOf Cs).sum carriers.length j →
      ∃ τ c, WExec cap pb σ τ c ∧
        DecOK cap W τ out (SymFlat.symCallUnit I hs Cs carriers (j / ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2))
          ((j % ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) - 1) / ((cyOf Cs).sum + 3))
          ((j % ((carriers.length + 2 * a) * ((cyOf Cs).sum + 3) + 2) - 1) % ((cyOf Cs).sum + 3) - 1)) BP ∧
        τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧ c ≤ Bb) :
    ∀ j < b, ∀ out : List Bool, ∃ σD m Bp, WExec cap (decW W F pb cr I.filterErrDeg ζ Cδ C)
        (CellLoopD.blankCellD W.x w out j (Data.unaryList (Data.symCounts a Cs carriers))) σD m ∧
      DecOK cap W σD out ((unitE (symNT I hs Cs carriers * (2 ^ SeedFix.callKh (I.starParams n hs)) ^ 2 * ((carriers.length + 2 * a) * ((symListParams I n a Cs carriers).M + 3) + 2)) (carriers.length + 2 * a) (symListParams I n a Cs carriers).M (SymFlat.symCallUnit I hs Cs carriers)) j) Bp ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      CellLoopD.cpCost (Data.unaryList (Data.symCounts a Cs carriers)).length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤
        symNU (Data.unaryList (Data.symCounts a Cs carriers)).length
          (4 * UnaryPow.sq cap + 1 + (reqParseCost n a carriers.length Kb + 1 + (5 * UnaryPow.sq cap + 1 +
        (30 * UnaryPow.sq cap + 1 + countsCost carriers.length Cmax (cyOf Cs).sum))) + 1 +
        (starCapCost n cr I.filterErrDeg (Ledger.rowBt h0 h1 n) (Ledger.rowBSparse h0 h1 2 Cδ n) (Ledger.Lq n) cap +
        1 + (500 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap))) + 1 + (Bb + 12)) BP b := by
  intro j hj out
  obtain ⟨σD, m, e, d, k0, k2, k2h, hm⟩ := sym_dec cap W F pb cr h0 h1 Cδ C I hs Cs carriers tl w out j Kb Cmax Bb BP
    ha hnc hrB hcapOf hcd hD hw hKb hC hN1 hcS hcP hcC hN2 (by omega) hU hcF hFc hFN (hP j hj out)
  refine ⟨σD, m, BP, e, d, k0, k2, k2h, ?_⟩
  unfold symNU
  omega

end Loop

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec
