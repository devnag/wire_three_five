import Proof.Wire_3_5.Primitive.SeedFix.C4SymWB

/-! # C4 SYM stage, part 3: the shape of the child family the loop runs

"For each candidate child prefix, print its signed equation expression" (P3:3034-3035): the child family of C6's
assembler (`C4Child.chFam` at `UnionMachine.TailAsm.asmStage`) keeps `32` tapes whose words the setup writes. This part
states what the loop's entry reads of a child family (**`ChShape`**: the tape count, the kept tapes, the prefix tape, the
kept words, the decision count) and proves it for every `chFam` (**`chFam_shape`**, for SYM and THR alike; one lemma
per field, heartbeats being per declaration).

Paper quantity of the main type: the child family's kept words (compiler fields, rulers, constants, `1^{Q'}`, mask). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary

/-- **The shape of a child family** as the loop's entry reads it. -/
structure ChShape (F : C4Loop.ChildFam) (pd : ℕ) (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr))
    (TWd Cap nT : ℕ) (pre post : List Bool) (q uu : ℕ) : Prop where
  ht : F.t = 202 + pd
  keep : ∀ v (h : v < F.t), F.keep ⟨v, h⟩ = decide (kept pd v)
  pfx : F.PFX.val = 17
  k0 : ∀ h, F.K ⟨0, h⟩ = frame pre
  k2 : ∀ h, F.K ⟨2, h⟩ = frame post
  keu : ∀ v (h1 : 6 ≤ v) (h2 : v < 101) (h : v < F.t),
    F.K ⟨v, h⟩ = C4Dock.euIn P ents TWd Cap nT [] ⟨v - 6, by have : C4Dock.EU = 95 := rfl; omega⟩
  kqq : ∀ h, F.K ⟨199 + pd, h⟩ = List.replicate q true
  kuu : ∀ h, F.K ⟨200 + pd, h⟩ = List.replicate uu true
  bound : F.bound = 8 * P.ell

section Fam
variable (wa : RepairRepresentation.WilliamsAlgorithm) (a : RepairRepresentation.DecompositionAlgorithm)
    (R0 : CompilerMachine.Req.C3Req) (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT Rn K : ℕ)
    (batch : List SeedFix.SExpr) (E : Cost.Envelope) (Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * P.ell → C4Dock.EnumOk P ents TWd Cap nT Rn K batch (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * P.ell → (C4Child.chR R0 P nT Rn batch (p ++ [b])).Pre a)
    (hQp : R0.P.Q ≤ R0.p)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request), p.length < 8 * P.ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
        (CompilerMachine.Req.c3v2Ref a (C4Child.chR R0 P nT Rn batch (p ++ [b]))) →
      C4Child.coreCost wa a R0 P TWd Cap nT Rn K batch (p ++ [b]) r ≤ Kch)

local notation "FF" => C4Child.chFam UnionMachine.TailAsm.asmStage wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp
  hcost

theorem sh_ht : (FF).t = 202 + C4Pipe.PD wa := by
  show C4Child.CT UnionMachine.TailAsm.asmStage wa + 1 = _
  rw [CT_eq]
  omega

theorem sh_keep : ∀ v (h : v < (FF).t), (FF).keep ⟨v, h⟩ = decide (kept (C4Pipe.PD wa) v) :=
  fun v h => keepF_val wa v h

theorem sh_pfx : (FF).PFX.val = 17 := pfxT_val wa

theorem sh_k0 : ∀ h, (FF).K ⟨0, h⟩ = frame (C4Child.pre a R0) := fun h => KF_asm0 wa a R0 P ents TWd Cap nT h

theorem sh_k2 : ∀ h, (FF).K ⟨2, h⟩ = frame (C4Child.post a R0) := fun h => KF_asm2 wa a R0 P ents TWd Cap nT h

theorem sh_keu : ∀ v (h1 : 6 ≤ v) (h2 : v < 101) (h : v < (FF).t),
    (FF).K ⟨v, h⟩ = C4Dock.euIn P ents TWd Cap nT [] ⟨v - 6, by have : C4Dock.EU = 95 := rfl; omega⟩ :=
  fun v h1 h2 h => KF_eu wa a R0 P ents TWd Cap nT v h1 h2 h

set_option maxHeartbeats 1000000 in
theorem sh_kqq (h : 199 + C4Pipe.PD wa < (FF).t) :
    (FF).K ⟨199 + C4Pipe.PD wa, h⟩ = List.replicate R0.P.Q true :=
  KF_qq wa a R0 P ents TWd Cap nT h

set_option maxHeartbeats 1000000 in
theorem sh_kuu (h : 200 + C4Pipe.PD wa < (FF).t) :
    (FF).K ⟨200 + C4Pipe.PD wa, h⟩ = List.replicate (2 ^ R0.dRow * 2 ^ R0.dRow) true :=
  KF_uu wa a R0 P ents TWd Cap nT h

theorem sh_bound : (FF).bound = 8 * P.ell := rfl

/-- **Every child family of C6's assembler has the shape.** -/
theorem chFam_shape :
    ChShape (FF) (C4Pipe.PD wa) P ents TWd Cap nT (C4Child.pre a R0) (C4Child.post a R0) R0.P.Q
      (2 ^ R0.dRow * 2 ^ R0.dRow) :=
  ⟨sh_ht wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost,
    sh_keep wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost,
    sh_pfx wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost,
    sh_k0 wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost,
    sh_k2 wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost,
    sh_keu wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost,
    sh_kqq wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost,
    sh_kuu wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost,
    sh_bound wa a R0 P ents TWd Cap nT Rn K batch E Kch hok hpre hQp hcost⟩

end Fam

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
