import Proof.Packets.BudgetYFam
import Proof.Packets.BudgetWidthA
import Proof.Packets.BudgetInitAll
import Proof.SourceAssembly.SourceSkelInitK

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget.Params
open NearCubicWires.SourceBudget NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-! ## 1. AD's constants at `(selector, a, printer, degree, target)` -/

/-- AD's input coefficient (`input_poly`: `|input| ≤ (inC0 + 4L)(q+1)^inE0`). -/
def inC0 (a : DecompositionAlgorithm) (degree target : ℕ) : ℕ := Classical.choose (input_poly a degree target)
/-- AD's input exponent. -/
def inE0 (a : DecompositionAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (input_poly a degree target))

theorem inC0_spec (a : DecompositionAlgorithm) (degree target : ℕ) :
    ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      (r.input a).length ≤ (inC0 a degree target + 4*r.liveScale)*(r.q+1)^inE0 a degree target :=
  Classical.choose_spec (Classical.choose_spec (input_poly a degree target))

def cc0 (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (streamCap_le_uniformC selector a degree target)

def ce0 (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (streamCap_le_uniformC selector a degree target))

/-- AD's header coefficient at live scale `L` (`header_class`). -/
def hd0C (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (degree target L : ℕ) : ℕ :=
  Classical.choose (header_class selector a printer degree target L)
/-- AD's header (small) exponent at live scale `L`. -/
def hd0E (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (degree target L : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (header_class selector a printer degree target L))

def cpTC0 (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (copy_classC selector a printer degree target (cc0 selector a degree target) (ce0 selector a degree target))
/-- … table exponent. -/
def cpTE0 (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec
    (copy_classC selector a printer degree target (cc0 selector a degree target) (ce0 selector a degree target)))
/-- … small coefficient. -/
def cpSC0 (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (copy_classC selector a printer degree target (cc0 selector a degree target) (ce0 selector a degree target))))
/-- … small exponent. -/
def cpSE0 (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (copy_classC selector a printer degree target (cc0 selector a degree target) (ce0 selector a degree target)))))

def v0C (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (vcap_classC selector a printer degree target (cc0 selector a degree target) (ce0 selector a degree target))
/-- `V`'s (table) exponent, `L`-free. -/
def v0E (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec
    (vcap_classC selector a printer degree target (cc0 selector a degree target) (ce0 selector a degree target)))

/-! ## 2. Per parameter tuple -/

def cVcN (selector : CyclicChoice.Laws) : ParNat := fun s _ _ _ p =>
  v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)

def hVN (selector : CyclicChoice.Laws) : ParNat := fun s _ _ _ p =>
  v0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)

/-- The admission degree of every site request. -/
abbrev degOf : ParNat := fun _ _ _ _ p => p.clauseDegree
/-- The accuracy target of every site request. -/
abbrev tgOf : ParNat := fun s _ _ _ p => tgt s p

def rB : ParNat := fun s _ _ _ p => max (rSel s p) (betaE (decompositionOf s) p.clauseDegree + 3)

/-- The THR code width's polynomial bound (coefficient, exponent). -/
def wTC : ℕ := Classical.choose thrWidth_poly
def wTE : ℕ := Classical.choose (Classical.choose_spec thrWidth_poly)
/-- The SYM code width's polynomial bound. -/
def wSC : ℕ := Classical.choose symWidth_poly
def wSE : ℕ := Classical.choose (Classical.choose_spec symWidth_poly)

/-- **The gauge exponent base**: the sum of every exponent the unbuilt machines are built from. -/
def gE0 (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) :
    ParNat := fun s g hg hh p =>
  inE0 (decompositionOf s) p.clauseDegree (tgt s p) + rowsE (decompositionOf s) p.clauseDegree (tgt s p) +
    betaE (decompositionOf s) p.clauseDegree + rB s g hg hh p + ce0 selector (decompositionOf s) p.clauseDegree (tgt s p) +
    cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) +
    cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + hVN selector s g hg hh p +
    (packets (decompositionOf s)).degree + (rows (decompositionOf s) (printerOf s)).degree + mask.degree + p.clauseDegree +
    SourceSkeleton.Params.pE s g hg hh p + SourceSkeleton.Params.ldE s g hg hh p + SourceSkeleton.Params.dE s g hg hh p +
    SourceSkeleton.Params.cwE s g hg hh p + wTE + wSE + coldD

/-- **The gauge exponent** (`L`-free): the cube of the exponent base (covers products of up to three exponents). -/
def gE (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) :
    ParNat := fun s g hg hh p => (gE0 selector mask packets rows s g hg hh p + 64)^3

/-- The gauge coefficient base: the sum of every coefficient the unbuilt machines are built from. -/
def gC0 (selector : CyclicChoice.Laws) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) : ParNat := fun s g hg hh p =>
  inC0 (decompositionOf s) p.clauseDegree (tgt s p) + rowsC (decompositionOf s) p.clauseDegree (tgt s p) +
    betaC (decompositionOf s) p.clauseDegree + cc0 selector (decompositionOf s) p.clauseDegree (tgt s p) +
    cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) +
    cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) + cVcN selector s g hg hh p +
    (packets (decompositionOf s)).coefficient + SourceSkeleton.Params.pC s g hg hh p + SourceSkeleton.Params.ldC s g hg hh p +
    SourceSkeleton.Params.dC s g hg hh p + SourceSkeleton.Params.cwC s g hg hh p + SourceSkeleton.Params.sC s g hg hh p +
    SourceSkeleton.Params.rC s g hg hh p + C10PartsSchedule.thresholdFloor s + wTC + wSC + coldC + tgt s p +
    (SourceSkeleton.InitS.cwCs true).sum + (SourceSkeleton.InitS.cwCs false).sum +
    PCPSerializerCapacity.coefficient (SourceSkeleton.Params.dE s g hg hh p) (SourceSkeleton.Params.dC s g hg hh p) +
    PCPSerializerCapacity.coefficient (SourceSkeleton.Params.cwE s g hg hh p) (SourceSkeleton.Params.cwC s g hg hh p)

/-- **The gauge coefficient** (`L`-free). -/
def gC (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) :
    ParNat := fun s g hg hh p => (gC0 selector packets s g hg hh p + 2)^(gE selector mask packets rows s g hg hh p)

/-! ## 3. `KF` -/

def KFc (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) :
    CallKFam := fun s g hg hh p L =>
  { inC := inC0 (decompositionOf s) p.clauseDegree (tgt s p) + 4*L
    inE := inE0 (decompositionOf s) p.clauseDegree (tgt s p)
    rowsC := rowsC (decompositionOf s) p.clauseDegree (tgt s p)
    rowsE := rowsE (decompositionOf s) p.clauseDegree (tgt s p)
    capC := cc0 selector (decompositionOf s) p.clauseDegree (tgt s p)
    capE := ce0 selector (decompositionOf s) p.clauseDegree (tgt s p)
    hdC := hd0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L
    hdE := hd0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p) L
    cpTC := cpTC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
    cpTE := cpTE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
    cpSC := cpSC0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
    cpSE := cpSE0 selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)
    dsTC := cVcN selector s g hg hh p
    dsTE := hVN selector s g hg hh p
    dsSC := 0
    dsSE := 0
    rwC := (packets (decompositionOf s)).coefficient*rowsC (decompositionOf s) p.clauseDegree (tgt s p) + 1
    betC := betaC (decompositionOf s) p.clauseDegree
    betE := betaE (decompositionOf s) p.clauseDegree
    mC := 16
    mE := 2
    bC := C10PartsSchedule.thresholdFloor s + 1
    bE := rB s g hg hh p
    jC := gC selector mask packets rows s g hg hh p
    jE := gE selector mask packets rows s g hg hh p
    cG := gC selector mask packets rows s g hg hh p
    dG := gE selector mask packets rows s g hg hh p
    cwC := gC selector mask packets rows s g hg hh p
    cwE := gE selector mask packets rows s g hg hh p
    cVc := cVcN selector s g hg hh p
    hV := hVN selector s g hg hh p }

/-! ## 4. The uniform caps and stream capacity, and their fit at every admitted call -/

def COf (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (q : ℕ) : ℕ :=
  cc0 selector (decompositionOf s) p.clauseDegree (tgt s p)*smallClass 4 (ce0 selector (decompositionOf s) p.clauseDegree (tgt s p)) q

def VvOf (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (L q : ℕ) : ℕ :=
  v0C selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)*
    tableClass L (v0E selector (decompositionOf s) (printerOf s) p.clauseDegree (tgt s p)) q

theorem scalarsFit (L q : ℕ) :
    InitPost.Ms L q ≤ 16*(q+1)^2 ∧ InitRun.Mb L q ≤ 16*(q+1)^2 ∧ InitRun.U0 L q ≤ 16*(q+1)^2 := by
  have hK := normalizedLiveCount_le q L
  have hsq : (q+1)^2 = (q+1)*(q+1) := by ring
  have hMs : InitPost.Ms L q ≤ 2*(q+1) := by unfold InitPost.Ms; omega
  have hdiv : q / InitSlopes.dv L q ≤ q := Nat.div_le_self _ _
  have hMb : InitRun.Mb L q ≤ q*(2*(q+1)) := by
    unfold InitRun.Mb; exact Nat.mul_le_mul hdiv hMs
  have hU0 : InitRun.U0 L q ≤ 4*(q+1) + 12 := by
    unfold InitRun.U0 InitRun.Kc
    omega
  have hq1 : q+1 ≤ (q+1)*(q+1) := Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsq]; omega
  · rw [hsq]; nlinarith
  · rw [hsq]; nlinarith

/-- **The cache radix fits** `betC·(q+1)^betE` at every admitted request. -/
theorem gsFit (a : DecompositionAlgorithm) {den degree target : ℕ} (hden : 1 ≤ den) (r : Request)
    (hr : RequestAdmitted den degree target r) :
    (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length + 1 ≤
      betaC a degree*(r.q+1)^betaE a degree :=
  (RequestAdmitted.radix_le hden a r hr).trans (betaPoly_le a degree r.q)

/-- **The input fits** `inC·(q+1)^inE` of `KF … L` at a request of live scale `L`. -/
theorem inFit (a : DecompositionAlgorithm) {den degree target : ℕ} (hden : 1 ≤ den) (r : Request)
    (hr : RequestAdmitted den degree target r) (L : ℕ) (hL : r.liveScale = L) :
    (r.input a).length ≤ (inC0 a degree target + 4*L)*(r.q+1)^inE0 a degree target := by
  rw [← hL]; exact inC0_spec a degree target den hden r hr

/-- **An init-constant triple**: `icost ≤ iT·tableClass L (hR+1) q + iP·(q+1)^iE`. -/
structure InitK where
  iT : ℕ
  iP : ℕ
  iE : ℕ

/-- A per-parameter init-constant family (last argument: the live scale). -/
abbrev InitKFam : Type :=
  (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → InitK

/-- **The init class family**: table exponent `hR + 1`, polynomial exponent `iE` (read at `L = 0`), coefficients at `Lf`. -/
def IFam (R : RcChoice) (IK : InitKFam) (Lf : ParNat) : ClsFam where
  dP := fun s g hg hh p => (IK s g hg hh p 0).iE
  hT := fun s g hg hh p => R.hR s g hg hh p + 1
  hS := fun _ _ _ _ _ _ => 0
  cP := fun s g hg hh p k => (IK s g hg hh p (Lf s g hg hh p)).iP * C10PartsSchedule.widthConst s k ^ (IK s g hg hh p 0).iE
  cT := fun s g hg hh p _ => (IK s g hg hh p (Lf s g hg hh p)).iT
  cS := fun _ _ _ _ _ _ => 0

/-- The refill class's table exponent, written from the exponents alone (no live scale anywhere). -/
def yTx (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) :
    ParNat := fun s g hg hh p => (KFc selector mask packets rows s g hg hh p 0).H (rows (decompositionOf s) (printerOf s)).degree

def hRx (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) :
    ParNat := fun s g hg hh p =>
  max (max ((famSite printerOf (cVcN selector) (hVN selector)).hT s g hg hh p) (yTx selector mask packets rows s g hg hh p))
    (max (yTx selector mask packets rows s g hg hh p) (hVN selector s g hg hh p)) + 2

def IKc (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) :
    InitKFam := fun s g hg hh p L =>
  { iT := initT (hRx selector mask packets rows s g hg hh p) (hVN selector s g hg hh p) L 1 (cVcN selector s g hg hh p)
        (SourceSkeleton.Params.sC s g hg hh p) (SourceSkeleton.Params.rC s g hg hh p) + 98 + 1024*(cVcN selector s g hg hh p + 1)
    iP := (gC selector mask packets rows s g hg hh p + L +
        initP L (tgt s p) (SourceSkeleton.Params.sC s g hg hh p) (SourceSkeleton.Params.rC s g hg hh p)
          (SourceSkeleton.Params.pE s g hg hh p) (SourceSkeleton.Params.pC s g hg hh p) 3 1
          (SourceSkeleton.Params.ldE s g hg hh p) (SourceSkeleton.Params.ldC s g hg hh p) + 2)^(2*gE selector mask packets rows s g hg hh p)
    iE := 2*gE selector mask packets rows s g hg hh p }

end
end NearCubicWires.SourceBudget.Params
end

