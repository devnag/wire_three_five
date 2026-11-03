import Proof.SourceAssembly.SourceStepsParamsV3
import Proof.Packets.SrcMetaIface2

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.Admission NearCubicWires.RuntimeShape
open NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton NearCubicWires.SourceSkeleton.ClassR
namespace NearCubicWires.SourceSkeleton.ClassV4
noncomputable section

section gauge
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

def KFc4 : CallKFam := fun s g hg hh p L =>
  { SourceStart.Meta.KFc3 selector mask packets rows s g hg hh p L with
    jC := ClassV3.gCv3 selector mask packets rows s g hg hh p
    jE := ClassV3.gEv3 selector mask packets rows s g hg hh p
    cG := ClassV3.gCv3 selector mask packets rows s g hg hh p
    dG := ClassV3.gEv3 selector mask packets rows s g hg hh p
    cwC := ClassV3.gCv3 selector mask packets rows s g hg hh p
    cwE := ClassV3.gEv3 selector mask packets rows s g hg hh p }

def yTx4 : ParNat := fun s g hg hh p => (KFc4 selector mask packets rows s g hg hh p 0).H (rows (decompositionOf s) (printerOf s)).degree

end gauge

section site
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

/-- **The site reserve's exponent at `rB`**, from the exponents alone. -/
def hRx4 : ParNat := fun s g hg hh p =>
  max (max ((famSiteR printerOf (cVcN selector) (hVN selector)).hT s g hg hh p) (yTx4 selector mask packets rows s g hg hh p))
    (max (yTx4 selector mask packets rows s g hg hh p) (hVN selector s g hg hh p)) + 2

theorem hRx4_ge (s : EightSources) (g : Real) (hg : 0 < g) (hh : g < 1/2) (p : Parameters s g) :
    2 ≤ hRx4 selector mask packets rows s g hg hh p ∧ hVN selector s g hg hh p + 2 ≤ hRx4 selector mask packets rows s g hg hh p := by
  unfold hRx4
  constructor <;> omega

def IKc4 : InitKFam := fun s g hg hh p L =>
  { iT := initT (hRx4 selector mask packets rows s g hg hh p) (hVN selector s g hg hh p) L 1 (cVcN selector s g hg hh p)
        (SourceSkeleton.Params.sC s g hg hh p) (SourceSkeleton.Params.rC s g hg hh p) + 98 + 1024*(cVcN selector s g hg hh p + 1)
    iP := (ClassV3.gCv3 selector mask packets rows s g hg hh p + L +
        initP L (tgt s p) (SourceSkeleton.Params.sC s g hg hh p) (SourceSkeleton.Params.rC s g hg hh p)
          (SourceSkeleton.Params.pE s g hg hh p) (SourceSkeleton.Params.pC s g hg hh p) 3 1
          (SourceSkeleton.Params.ldE s g hg hh p) (SourceSkeleton.Params.ldC s g hg hh p) + 2)^(2*ClassV3.gEv3 selector mask packets rows s g hg hh p)
    iE := 2*ClassV3.gEv3 selector mask packets rows s g hg hh p }

/-- **`B`'s table exponent at `rB`, from the exponents alone.** -/
def siteHT4 : ParNat := fun s g hg hh p =>
  max (max ((famSiteR printerOf (cVcN selector) (hVN selector)).hT s g hg hh p)
      (max (hRx4 selector mask packets rows s g hg hh p) (yTx4 selector mask packets rows s g hg hh p)))
    (max (hRx4 selector mask packets rows s g hg hh p)
      (max (yTx4 selector mask packets rows s g hg hh p) (hRx4 selector mask packets rows s g hg hh p + 1)))

def siteL4 : ParNat := liveOfR (siteHT4 selector mask packets rows)

/-- **`y` at `rB`'s live scale.** -/
def siteY4 : ClsFam := yFam mask packets rows degOf tgOf (KFc4 selector mask packets rows) (siteL4 selector mask packets rows)
/-- **`yF0` at `rB`'s live scale.** -/
def siteYF04 : ClsFam := yF0Fam mask packets rows degOf tgOf (KFc4 selector mask packets rows) (siteL4 selector mask packets rows)
/-- **The site's reserve at `rB`.** -/
def siteR4 : RcChoice :=
  siteRcR printerOf (cVcN selector) (hVN selector) (siteY4 selector mask packets rows) (siteYF04 selector mask packets rows)
/-- **The init's class at `rB`.** -/
def siteI4 : ClsFam := IFam (siteR4 selector mask packets rows) (IKc4 selector mask packets rows) (siteL4 selector mask packets rows)

def siteBP4 : ClsFam :=
  siteBIR printerOf (cVcN selector) (hVN selector) (siteY4 selector mask packets rows) (siteYF04 selector mask packets rows)
    (siteI4 selector mask packets rows)

/-- **The reserve's exponent is `hRx4`** (field equation). -/
theorem siteR4_hR : (siteR4 selector mask packets rows).hR = hRx4 selector mask packets rows := by
  funext s g hg hh p
  rfl

end site

section fits4
variable (selector : CyclicChoice.Laws) (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (s : EightSources) (g : Real) (hg : 0 < g) (hh : g < 1/2) (p : Parameters s g) (k : Nat)

/-- **The seam's scalar reserve premises at `siteR4`**, the exact `V = VvOf` (decision 80b) (`hSl hRl hBl hdescR hUl hMb hMs`), past one onset. -/
theorem seam_scalars_Rc4 :
    ∃ n0, ∀ n, n0 ≤ n →
      P1TopDownPaidReusableReserves.workspace (printerOf s)
          (VvOf selector s p (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n)) + 2 ≤
        (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
          ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) ∧
      P1TopDownPaidReusableReserves.rewind (printerOf s)
          (VvOf selector s p (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n)) + 2 ≤
        (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
          ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) ∧
      P1TopDownPaidReusableReserves.buffer
          (VvOf selector s p (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n)) + 2 ≤
        (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
          ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) ∧
      VvOf selector s p (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n) ≤
        (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
          ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) ∧
      InitRun.U0 (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n) ≤
        (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
          ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) ∧
      InitRun.Mb (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n) ≤
        (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
          ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) ∧
      InitPost.Ms (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n) ≤
        (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
          ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) := by
  obtain ⟨n1, h1⟩ := reserves_le_Rc (printerOf s) s k (siteL4 selector mask packets rows s g hg hh p)
    (cVcN selector s g hg hh p) (hVN selector s g hg hh p)
  obtain ⟨q2, h2⟩ := poly_le_Rc 16 2 (siteL4 selector mask packets rows s g hg hh p)
  obtain ⟨n2, hn2⟩ := widthAt_ge_eventually s k q2
  have hC : 1 ≤ (siteR4 selector mask packets rows).C s g hg hh p := le_rfl
  have hR : hVN selector s g hg hh p + 2 ≤ (siteR4 selector mask packets rows).hR s g hg hh p := by
    rw [siteR4_hR]
    exact (hRx4_ge selector mask packets rows s g hg hh p).2
  refine ⟨max n1 n2, fun n hn => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h1 n (le_trans (le_max_left _ _) hn) _ _ hC hR
  have hV' : VvOf selector s p (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n) ≤
      cVcN selector s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p) (hVN selector s g hg hh p)
        (C10PartsSchedule.widthAt s k n) := le_rfl
  have hq := h2 (C10PartsSchedule.widthAt s k n) (hn2 n (le_trans (le_max_right _ _) hn)) _
    ((siteR4 selector mask packets rows).hR s g hg hh p) hC
  obtain ⟨b1, b2, b3⟩ := scalarsFit (siteL4 selector mask packets rows s g hg hh p) (C10PartsSchedule.widthAt s k n)
  refine ⟨(Nat.add_le_add_right (ClassV3.workspace_mono (printerOf s) hV') 2).trans a1,
    (Nat.add_le_add_right (ClassV3.rewind_mono (printerOf s) hV') 2).trans a2,
    le_trans (by show _ + 1 + 2 ≤ _ + 1 + 2; omega) a3, hV'.trans a4, b3.trans hq, b2.trans hq, b1.trans hq⟩

/-- **The seam's per-call reserve premises at `siteR4`** (`hlog`, `hL`), past one onset. -/
theorem seam_call_Rc4 (den : Nat) (hden : 1 ≤ den) :
    ∃ n0, ∀ n, n0 ≤ n → ∀ r : Request,
      RequestAdmitted den p.clauseDegree (tgt s p) r → r.liveScale = siteL4 selector mask packets rows s g hg hh p →
      r.q = C10PartsSchedule.widthAt s k n →
      2 * (r.input (decompositionOf s)).length + 1 ≤
          (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
            ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) ∧
      (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf s) (r.family (decompositionOf s))).gs).length + 3 ≤
          (siteR4 selector mask packets rows).C s g hg hh p * tableClass (siteL4 selector mask packets rows s g hg hh p)
            ((siteR4 selector mask packets rows).hR s g hg hh p) (C10PartsSchedule.widthAt s k n) := by
  obtain ⟨q1, h1⟩ := poly_le_Rc (2 * (inC0 (decompositionOf s) p.clauseDegree (tgt s p) + 4 * siteL4 selector mask packets rows s g hg hh p) + 1)
    (inE0 (decompositionOf s) p.clauseDegree (tgt s p)) (siteL4 selector mask packets rows s g hg hh p)
  obtain ⟨q2, h2⟩ := poly_le_Rc (betaC (decompositionOf s) p.clauseDegree + 2) (betaE (decompositionOf s) p.clauseDegree)
    (siteL4 selector mask packets rows s g hg hh p)
  obtain ⟨n1, hn1⟩ := widthAt_ge_eventually s k (max q1 q2)
  have hC : 1 ≤ (siteR4 selector mask packets rows).C s g hg hh p := le_rfl
  refine ⟨n1, fun n hn r hr hL hq => ?_⟩
  have hw := hn1 n hn
  have hin0 := inFit (decompositionOf s) hden r hr (siteL4 selector mask packets rows s g hg hh p) hL
  have hgs0 := gsFit (decompositionOf s) hden r hr
  have hin : (r.input (decompositionOf s)).length ≤
      (inC0 (decompositionOf s) p.clauseDegree (tgt s p) + 4 * siteL4 selector mask packets rows s g hg hh p) *
        (C10PartsSchedule.widthAt s k n + 1) ^ inE0 (decompositionOf s) p.clauseDegree (tgt s p) :=
    hin0.trans (le_of_eq (by rw [hq]))
  have hgs : (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf s) (r.family (decompositionOf s))).gs).length + 1 ≤
      betaC (decompositionOf s) p.clauseDegree * (C10PartsSchedule.widthAt s k n + 1) ^ betaE (decompositionOf s) p.clauseDegree :=
    hgs0.trans (le_of_eq (by rw [hq]))
  have hp1 : 1 ≤ (C10PartsSchedule.widthAt s k n + 1) ^ inE0 (decompositionOf s) p.clauseDegree (tgt s p) := Nat.one_le_pow _ _ (by omega)
  have hp2 : 1 ≤ (C10PartsSchedule.widthAt s k n + 1) ^ betaE (decompositionOf s) p.clauseDegree := Nat.one_le_pow _ _ (by omega)
  have e1 := h1 (C10PartsSchedule.widthAt s k n) (le_trans (le_max_left _ _) hw) _ ((siteR4 selector mask packets rows).hR s g hg hh p) hC
  have e2 := h2 (C10PartsSchedule.widthAt s k n) (le_trans (le_max_right _ _) hw) _ ((siteR4 selector mask packets rows).hR s g hg hh p) hC
  constructor
  · refine le_trans ?_ e1
    have hm : 2 * (r.input (decompositionOf s)).length ≤
        2 * ((inC0 (decompositionOf s) p.clauseDegree (tgt s p) + 4 * siteL4 selector mask packets rows s g hg hh p) *
          (C10PartsSchedule.widthAt s k n + 1) ^ inE0 (decompositionOf s) p.clauseDegree (tgt s p)) := Nat.mul_le_mul_left 2 hin
    rw [Nat.add_mul, one_mul, Nat.mul_assoc]
    omega
  · refine le_trans ?_ e2
    rw [Nat.add_mul]
    omega

end fits4

end
end NearCubicWires.SourceSkeleton.ClassV4
end

