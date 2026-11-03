import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4BudEBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB7Base
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.SeedFix.C4PadC
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfABase


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K SymLeafC4, part 1: the SYM stage at a call with rows

P3:3011-3016 (the SYM tape's entries, the seed of `samp:seed`), 3098-3100 (the budget), 1188-1189 (the star:
`N = 2^{k_h}` live halves, `k_h = s·(r/2) ≥ 1`): at a SYM call with `R = |carriers| + 2a ≥ 1` rows the tape word's second
bit is set (`symTape_plain`), so the branched stage `padStage (symStageU3 …)` runs the SYM stage unchanged
(`padStage_plain`); PA's data stage runs at the unary numbers `C_L(n+1)^D ≥ needW` (`sym_data`); the stage's run from
the numbers machine (`sym_stage_of_big4`), the contract's side conditions at the call (`SymEAt3`) and the C3 writer
(`sym_hc3`) within any budget above its steps (`sym_plain_run`).

* `callKh_pos`, `blockWord_chunk_bit`, **`symTape_plain`**, **`sym_data`**, **`sym_plain_run`**.

Paper quantity of the main type: the SYM stage's output at the call (its seed word) within the budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymLf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

/-- **PA's data stage at a SYM call**, at the unary numbers `C_L(n+1)^D ≥ needW` (both of the stage's). -/
theorem sym_data (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation)) (D CL : ℕ)
    (hWL : PrimT.C4GateSym.needW n ≤ UnaryCalc.value D CL n) :
    ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ),
      Step Data.dataM (2 * Data.coreCost a Cs carriers (UnaryCalc.value D CL n) (UnaryCalc.value D CL n) + 2) (fun _ => 0)
        (Fin.addCases (Data.rawIn (symReq n a ha Cs carriers translation).word n (UnaryCalc.value D CL n)
          (UnaryCalc.value D CL n)) (fun _ : Fin 1 => List.replicate 0 false))
        (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape Data.sOUT) = Data.dataWord (Data.symCounts a Cs carriers) ∧
      tout (sTape Data.sIN) = frame (symReq n a ha Cs carriers translation).word := by
  obtain ⟨hk, hd, he⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  obtain ⟨hL, hLX, h2, hcN, hcA, hcK, hcx, hcy, hcu, -, -⟩ := PrimT.C4GateSym.sym_data_hyps Cs carriers ha hk hd he _ hWL
  obtain ⟨tout, m, hst, h1, h2', -⟩ := Data.data_step_blank a Cs carriers (RepairRepresentation.natListWord translation)
    _ _ ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu
  rw [ReqBridge.reqW_symReq ha Cs carriers translation] at hst h2'
  exact ⟨tout, m, hst, h1, h2'⟩

end NearCubicWires.WireExponent3_5.PrimT.C4SymLf

end
