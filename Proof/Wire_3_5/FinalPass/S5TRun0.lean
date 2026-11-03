import Lean
import Proof.Wire_3_5.FinalPass.S5TNum4
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.S5TChC
import Proof.Wire_3_5.FinalPass.S5TJoin
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 120000


/-! # S5-THR, part 39: the THR call's named pieces at `l`'s algorithm (P3:2220-2231, 3170-3181)

Names for the THR call's pieces at a request, used by the stage's run (`Run1`): the call's majorant **`mpC`**, its
fixed hash bits **`hbC`**, the input's prefix before the bits' frame **`preC`**, W6's numbers **`vC`** at
`litAlg l` and `D = 1`; **`mp_eqL`** (`Join.mp_eq` there). Also `x6L`, `xtL` (W6's and the top front's tape counts
at `l`).

Paper quantity of the main type: the fixed hash's parameters of a THR call (P3:2220-2231). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimThrW.TopFront2 (tf2OutPorts)

/-- W6's tape count at `l`. -/
noncomputable abbrev x6L (l : Literals) : ℕ := (PrimT.W6.numsW6 (PrimT.W6.litAlg l) 1).x

/-- The top front's tape count at `l`. -/
noncomputable abbrev xtL (l : Literals) : ℕ := (PrimThrW.TF3Cost.topFront3 (PrimT.W6.litAlg l)).x

section Run
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The THR call's majorant. -/
noncomputable abbrev mpC {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) : Filters.MajorantParams :=
  Primitive.thrMajorant ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
    ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
    (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)

/-- The THR call's fixed hash bits. -/
noncomputable abbrev hbC {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ) :
    Fin (2 * (mpC l F kclk coef A a ha hs Cs carriers).t * (mpC l F kclk coef A a ha hs Cs carriers).ell0) → Bool :=
  FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
    (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
    ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
    (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
    (Primitive.thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (Primitive.thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
    (Primitive.thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)

/-- The input's prefix before the hash bits' frame. -/
noncomputable abbrev preC {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ) :
    List Bool :=
  (⟨n, .thr, a', ha', Cs, carriers, translation⟩ : PrimRequest).word ++
    FinalPass.Sample.sampleWord (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
      (List.ofFn fun j => (((SeedFix.thrCallSample (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers
        translation).S j).1.val, ((SeedFix.thrCallSample (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs
        carriers translation).S j).2.val))

/-- W6's numbers at the call. -/
noncomputable abbrev vC {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) :
    PrimThrW.Joins.ThrNumVals :=
  vOf l F.cr ((callInputs l F kclk coef A a ha).starParams n hs) Cs (PrimT.W6.litAlg l) 1 carriers

theorem mp_eqL {n : ℕ} (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) :
    mpC l F kclk coef A a ha hs Cs carriers = mpOf (vC l F kclk coef A a ha hs Cs carriers) :=
  mp_eq l F kclk coef A a ha hs Cs carriers

end Run

end NearCubicWires.WireExponent3_5.FinalPass.S5T

end
