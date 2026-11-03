import Proof.SourceAssembly.SourceRestStages
import Proof.SourceAssembly.SourceRestLayout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.Rest
noncomputable section

namespace Dims
open NearCubicWires.SourceConstruction.Dims
variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- F6's dock, by value, over plain numbers (`s11` the clear driver `scr 11`, `s11+1` its log `scr 12`). -/
def gVn (B F rt s11 eX pX gW i : Nat) : Nat :=
  if i < 61 then B + 19 + i
  else if i = 61 then B + 19 + (71 + eX + pX + gW) + 3
  else if i = 62 then B + 19 + (71 + eX + pX + gW) + 4
  else if i = 63 then F + rt + 4
  else if i = 64 then s11
  else if i = 65 then s11 + 1
  else if i < 69 then B + 19 + 61 + (i - 66)
  else F + rt + (i - 69)

def g : Fin 72 → Fin V := fun i =>
  ⟨gVn d.B d.F d.rt (d.scrV 11) eX pX gW i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres
    simp only [gVn, scrV, restPc, SourceConstruction.Dims.B, SourceConstruction.Dims.U,
      SourceConstruction.Dims.G, SourceConstruction.Dims.prepT] at *
    split_ifs <;> omega) hV⟩

def slE : Fin (2 + eX) → Fin V := fun j =>
  ⟨if j.val = 0 then d.B + 19 + 66 else if j.val = 1 then d.B + 19 + 59 else d.B + 19 + 71 + (j.val - 2),
    Nat.lt_of_lt_of_le (by
      have := j.isLt; have := e.hres
      simp only [restPc, SourceConstruction.Dims.B, SourceConstruction.Dims.U, SourceConstruction.Dims.G,
        SourceConstruction.Dims.prepT] at *
      split_ifs <;> omega) hV⟩

def slP : Fin (2 + pX) → Fin V := fun j =>
  ⟨if j.val = 0 then d.B + 19 + 66 else if j.val = 1 then d.B + 19 + 60 else d.B + 19 + 71 + eX + (j.val - 2),
    Nat.lt_of_lt_of_le (by
      have := j.isLt; have := e.hres
      simp only [restPc, SourceConstruction.Dims.B, SourceConstruction.Dims.U, SourceConstruction.Dims.G,
        SourceConstruction.Dims.prepT] at *
      split_ifs <;> omega) hV⟩

/-! ### The docks, tape by tape -/




end Dims

/-- The back half's first three stages: frame the input, then the two metadata stages. -/
def stagesMachine {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt se.extra sp.extra gW) {V : Nat}
    (hV : d.U ≤ V) :=
  Composition.machine
    (SLoad.MaskFrame.machine (d.scr hV 5) (d.scr hV 6) (d.pcT e hV ⟨66, by unfold restPc; omega⟩)
      (d.pcT e hV ⟨67, by unfold restPc; omega⟩))
    (Composition.machine (RecoveryFocus.machine (Dims.slE e hV) se.machine)
      (RecoveryFocus.machine (Dims.slP e hV) sp.machine))

/-- The back half's machine. -/
def backMachine {a : DecompositionAlgorithm} {vE vP : Request → Nat}
    (se : PacketsGlue.RequestMeta.UnaryStage a vE) (sp : PacketsGlue.RequestMeta.UnaryStage a vP)
    {d : SourceConstruction.Dims} {gW : Nat} (e : d.RestExt se.extra sp.extra gW) {V : Nat}
    (hV : d.U ≤ V) :=
  Composition.machine (stagesMachine se sp e hV)
    (Composition.machine (Prologue.f6Full (Dims.g e hV))
      (Prologue.slopeMachine (Dims.lenTape e.ext hV) (d.rsT e hV 0) (d.rsT e hV 1)
        (Dims.csSlots e.ext hV 1) (d.pcT e hV ⟨68, by unfold restPc; omega⟩)
        (d.pcT e hV ⟨69, by unfold restPc; omega⟩)))

end
end NearCubicWires.SourceConstruction.Rest
end
