import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrSide10
import Proof.Wire_3_5.Primitive.Writers.ThrEAt3
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SymCost4
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrSide1
import Proof.Wire_3_5.Primitive.Writers.ThrSide3
import Proof.Wire_3_5.Primitive.Writers.ThrSide5
import Proof.Wire_3_5.Primitive.Writers.ThrSide7
import Proof.Wire_3_5.Primitive.Writers.ThrSide8
import Proof.Wire_3_5.Primitive.Writers.ThrSide9
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.ThrSide10Base


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 THR block, piece 6 part 11: `ThrEAt3` at every THR call (piece 6's deliverable)

The THR twin of the SYM side's assembly (the SymBuild `side`): at a THR call of the gate, under the THR
constants' constraints (`ThrHpreC`, `d_Q ≥ cST + 1`, `d_T ≥ 2e_N`, `d_C ≥ 12d_T`, `symDAc ≤ d_A`, all fixed before `F`)
and the THR floors (`occCDT`, `16·thrC1`, `symHC(d_C, cDa + c_m, …)` below `C_D`), the free program
`freeProg2 (thrK2 c)` with the degree bound `thrDF c`, `K = symKn c` (the capacity `2^{⌊n/16⌋ + d_C L²}`) and
`K_ch = symKch` meets every clause of `ThrEAt3` (**`thrEAt`**): `hok` (`thrHok`), `hpre` (`hpre_thr`), `Q' ≤ pr`
(`hQp_thr`), `hcost` (`thrHcost`), the exact recovery range (`hrange_thr`), the pad (`thrHR`), `CoefFit` (`thrHcf`),
`1 ≤ h` (`thrH1`).

Paper quantity of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a THR call and its degree bound
(P3:2929-2941, 2994-3000, 3011-3016, 3034-3036, 3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC cDa coOf symHC symDAc symKch symKn)

section Gate
variable (l : Literals) (F : GateFree l)

/-- **`ThrEAt3` at every THR call** of the gate at the THR free numbers `freeProg2 (thrK2 c)`, `thrDF c`,
`K = symKn c`, `K_ch = symKch`, any `E3`. -/
theorem thrEAt (c : SymC) (wa : WilliamsAlgorithm) (E3 : Envelope) (hc : ThrHpreC l F.filterErrDeg (gate0 l F).alg c)
    (hdQ : cST l F.filterErrDeg + 1 ≤ c.dQ) (hdT : 2 * eNT l F.filterErrDeg ≤ c.dT) (hdC : 12 * c.dT ≤ c.dC)
    (hdA : symDAc c.eH c.eP c.dH c.dP (CompetitorCountTable.coefficient wa) (CompetitorCrossScheduler.exponent wa) ≤ c.dA)
    (hCDo : occCDT (gate0 l F).alg c (A1T l F.filterErrDeg) (10 * CallIndex.algX l + 32) ≤ F.CD)
    (hCDq : 16 * thrC1 (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) (10 * CallIndex.algX l + 32)
      (dDT l F.filterErrDeg) ≤ F.CD)
    (hCDh : symHC c.dC (cDa (gate0 l F).alg + cmT l) c.dQ c.dD (coOf (A1T l F.filterErrDeg + 1392 * (10 * CallIndex.algX l + 32) + cmT l) c.dQ (cDa (gate0 l F).alg) c.dD) (eNT l F.filterErrDeg) (eQT l F.filterErrDeg) ≤ F.CD)
    (hcpsi : 1 ≤ F.E.cpsi)
    (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    ThrFam.ThrEAt3 (callInputs l F kclk coef A a ha) (gate0 l F).alg wa Cs carriers translation hs
      ((freeProg2 (thrK2 c)).val (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) (thrDF c (ThrFam.thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) (symKn c n) (symKch l F c n) E3 := by
  refine ⟨thrHok l F c hdT hCDq hcpsi hdC kclk coef A a ha ha' Cs carriers translation hcall hs,
    fun p b _ => hpre_thr l F c hc hCDo hcpsi kclk coef A a ha ha' Cs carriers translation hcall hs (p ++ [b]),
    hQp_thr l F c (by have := hc.dP2; omega) hc.eP2 kclk coef A a ha ha' Cs carriers translation hcall hs,
    thrHcost l F c wa hc hCDo hCDq hCDh hcpsi hdA hdC kclk coef A a ha ha' Cs carriers translation hcall hs,
    hrange_thr l F c hdQ kclk coef A a ha ha' Cs carriers translation hcall hs,
    ?_,
    thrHcf l F c hc kclk coef A a ha ha' Cs carriers translation hcall hs,
    thrH1 l F c hc kclk coef A a ha Cs carriers hs⟩
  exact thrHR l F c wa hCDh hcpsi hdA kclk coef A a ha ha' Cs carriers translation hcall hs

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide

end
