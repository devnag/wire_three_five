import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfABase

/-! # C4.K SymLeafC4, part 2: the SYM stage's runs at a call with rows and at a degenerate call

P3:3011-3016, 3034-3038 (the child decisions and the fixed seed), #146 (c′), #159 (contract v7): at a call with rows the
branched stage runs the SYM stage on the call's own tape (`sym_plain_run`, from `SymEAt3`); at a degenerate call
(`R = 0`) it writes the padded batch (constant row per entry, `R′ = 1`) and runs the SYM stage on it with the padded
child family (`sym_deg_run`, from `SymPadEAt`); the padded batch prints the same objective (`PadEval`, C1b's
`chV_pad_eval`), so the loop fixes the same seed (`sym_prefix_pad`).

* `PadEval`, `chVal_pad`, **`sym_prefix_pad`**, **`sym_plain_run`**, **`sym_deg_run`**.

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
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters

/-- **The padded batch prints the same objective** (the `chV_pad_eval`): at every valuation, the child
expression of `R′ = 1` constant rows evaluates as the one of `R = 0` rows. -/
def PadEval : Prop :=
  ∀ (P : Sampler.SeedParams) (nT : ℕ) (b : List SeedFix.SExpr) (p' : List Bool) (v : ℕ → Bool),
    IntExpression.eval (C4Child.chV P nT 1 (C4Pad.padBatch (2 ^ P.kh) nT) p') v =
      IntExpression.eval (C4Child.chV P nT 0 b p') v

theorem chVal_pad (he : PadEval) (R0 : CompilerMachine.Req.C3Req) (P : Sampler.SeedParams) (nT : ℕ)
    (b : List SeedFix.SExpr) (p' : List Bool) :
    C4Child.chVal R0 P nT 1 (C4Pad.padBatch (2 ^ P.kh) nT) p' = C4Child.chVal R0 P nT 0 b p' := by
  unfold C4Child.chVal
  simp only [he P nT b p']

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hs : I.StarAt n)

/-- **The fixed seed at a degenerate SYM call**: after the `8ℓ` decisions of the padded child family, the prefix tape
holds `frame (ofFn greedyBitsQ)`, the same seed as `sym_prefix`'s (`PadEval`). -/
theorem sym_prefix_pad (he : PadEval) (hR0 : carriers.length + 2 * a = 0) (E3 : Envelope)
    (h Q psi m d pr k TWd Cap K Kch : ℕ) hok hpre (hQp : Q ≤ pr) hcost (R : ℕ)
    (hrange : ∀ p' : List Bool, p'.length ≤ 8 * (C4Val.symSP I hs Cs carriers).ell → ∀ z,
      (2 : ℤ) ^ (m - 1) * SeedFix.sampElim (C4Val.symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ Q) :
    (C4SymW.padFam I alg wa Cs carriers translation hs E3 h Q psi m d pr k TWd Cap K Kch hok hpre hQp hcost).src R
        (C4SymW.padFam I alg wa Cs carriers translation hs E3 h Q psi m d pr k TWd Cap K Kch hok hpre hQp hcost).bound
        ((C4SymW.padFam I alg wa Cs carriers translation hs E3 h Q psi m d pr k TWd Cap K Kch hok hpre hQp hcost).sl0
          (C4SymW.padFam I alg wa Cs carriers translation hs E3 h Q psi m d pr k TWd Cap K Kch hok hpre hQp hcost).PFX) =
      frame (List.ofFn (SeedFix.greedyBitsQ (C4Val.symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation))) := by
  rw [C4Loop.ChildFam.src_pfx]
  congr 1
  have hK : 0 < C4Geo.mult (I.starParams n hs) * 2 ^ (m - 1) := Nat.mul_pos (C4Sym.mult_pos _) (Nat.two_pow_pos _)
  rw [← C4Val.greedy_scaled (C4Val.symSP I hs Cs carriers) (SeedFix.symStateBits I hs Cs carriers translation) _ hK]
  apply C4Loop.greedyLoop_congr
  intro p' hp'
  show ((C4Child.chVal (C4Sym.symR0 I hs Cs carriers translation h Q psi m d pr k) (C4Val.symSP I hs Cs carriers)
    (PrimAsm.Enum.symNT I hs Cs carriers) 1 (C4SymW.padB I Cs carriers hs) p' : ℕ) : ℤ) = _
  have e1 := chVal_pad he (C4Sym.symR0 I hs Cs carriers translation h Q psi m d pr k) (C4Val.symSP I hs Cs carriers)
    (PrimAsm.Enum.symNT I hs Cs carriers) (PrimAsm.WriterIface.symExprs I hs Cs carriers) p'
  have e2 := C4Sym.sym_chVal I hs Cs carriers translation h Q psi m d pr k p' hp' (hrange p' hp')
  rw [hR0] at e2
  rw [show C4SymW.padB I Cs carriers hs = C4Pad.padBatch (2 ^ (C4Val.symSP I hs Cs carriers).kh)
    (PrimAsm.Enum.symNT I hs Cs carriers) from rfl, e1, e2]
  push_cast
  ring

end Call


end NearCubicWires.WireExponent3_5.PrimT.C4SymLf
