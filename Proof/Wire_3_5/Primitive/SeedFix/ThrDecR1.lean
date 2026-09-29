import Proof.Wire_3_5.Primitive.Writers.HashCellD
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecE

/-! # THR decode front, RADIX part 1: the front end and the numbers machine docked on scratch tapes

P3:3071-3091 (the preprocessing: each circuit's retained top children), P3:2543-2558 (the THR call's numbers): at a
RADIX unit the setup's entry `RadSetupB3.RsIn4` wants W6's primes, level records and modulus word on `130`, `131`,
`132` and the payloads on `133 … 136`, and EVERY other stream but `0, 1, 2, 113` blank (`RsIn4.blank`; scratch tapes
`sT` may be dirty). `HashCell.docks_run` fixes W6's fourteen unary numbers on `139 … 152`, its inputs on `153`,
`154` and the count on `2` (the unit's counter `1^j` here), so the THR unit docks the same two machines (`T`, the
front end `TopFrontPort3`; `N`, the numbers machine `NumsPort4`) on its own maps: every port but the request, the
three words and the payloads on scratch tapes, the count `1^V` on scratch tape `bT`, `1^{|carriers|}`, `1^{cap_T}` on
`bT + 1`, `bT + 2`, the fourteen numbers on `bT + 3 … bT + 16` (`dX = bT + 17` scratch tapes needed).

* `bT`, `dX`, `tfV`, `w6V`, `tfM`, `w6M` (injective), `dockTFT`, `dockW6T`, `docksMT`;
* **`DockInT`**, **`DockOutT`**, `tf_inT`, `w6_inT`, **`docksT_run`**.

Paper quantities of the main type: the payloads `payOf (Cs i)`, the primes `≤ cut`, the level records and the
modulus word, on the RADIX setup's entry streams. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.SupplierPipeline

section Dock
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- The first of the unit's own scratch tapes (after `T`'s scratch, its four native words, `N`'s scratch). -/
def bT : ℕ := T.x + 4 + N.x

/-- The scratch tapes the decode front needs. -/
def dX : ℕ := bT T N + 17

/-- `T`'s tape `j` as a stream index. -/
def tfV (j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 1 then 161 + bT T N else if j < 6 then 131 + j
  else if j < 10 then 161 + T.x + (j - 6) else 161 + (j - 10)

/-- `N`'s tape `j` as a stream index. -/
def w6V (j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 20 then 161 + bT T N else if j < 17 then 161 + bT T N + j
  else if j < 20 then 113 + j else 161 + T.x + 4 + (j - 21)

theorem tfV_lt (x : ℕ) (hx : dX T N ≤ x) (j : ℕ) (hj : j < 10 + T.x) : tfV T N j < LNS x + 1 := by
  unfold tfV bT; unfold dX bT at hx; unfold LNS; split_ifs <;> omega

theorem w6V_lt (x : ℕ) (hx : dX T N ≤ x) (j : ℕ) (hj : j < 21 + N.x) : w6V T N j < LNS x + 1 := by
  unfold w6V bT; unfold dX bT at hx; unfold LNS; split_ifs <;> omega

/-- `T`'s tapes on the cell's streams. -/
def tfM (x : ℕ) (hx : dX T N ≤ x) (j : Fin (10 + T.x)) : Fin (LNS x + 1) :=
  ⟨tfV T N j.val, tfV_lt T N x hx j.val j.isLt⟩

/-- `N`'s tapes on the cell's streams. -/
def w6M (x : ℕ) (hx : dX T N ≤ x) (j : Fin (21 + N.x)) : Fin (LNS x + 1) :=
  ⟨w6V T N j.val, w6V_lt T N x hx j.val j.isLt⟩

theorem tfM_val (x : ℕ) (hx : dX T N ≤ x) (j : Fin (10 + T.x)) : (tfM T N x hx j).val = tfV T N j.val := rfl
theorem w6M_val (x : ℕ) (hx : dX T N ≤ x) (j : Fin (21 + N.x)) : (w6M T N x hx j).val = w6V T N j.val := rfl

theorem tfM_inj (x : ℕ) (hx : dX T N ≤ x) : Function.Injective (tfM T N x hx) := by
  intro a b h
  have e : tfV T N a.val = tfV T N b.val := congrArg Fin.val h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  unfold tfV at e
  unfold bT at e
  split_ifs at e <;> omega

theorem w6M_inj (x : ℕ) (hx : dX T N ≤ x) : Function.Injective (w6M T N x hx) := by
  intro a b h
  have e : w6V T N a.val = w6V T N b.val := congrArg Fin.val h
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  unfold w6V at e
  unfold bT at e
  split_ifs at e <;> omega

/-- `N`'s tapes other than the request and the count are none of `T`'s. -/
theorem w6_ne_tfT (x : ℕ) (hx : dX T N ≤ x) (j : Fin (21 + N.x)) (h0 : j.val ≠ 0) (h20 : j.val ≠ 20)
    (i : Fin (10 + T.x)) : tfM T N x hx i ≠ w6M T N x hx j := by
  intro h
  have e : tfV T N i.val = w6V T N j.val := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  unfold tfV w6V at e
  unfold bT at e
  split_ifs at e <;> omega

/-- The front end, docked. -/
noncomputable def dockTFT (x : ℕ) (hx : dX T N ≤ x) :=
  RecoveryFocus.machine (fun j => sTape (nr := LNR) (tfM T N x hx j)) T.M

/-- The numbers machine, docked. -/
noncomputable def dockW6T (x : ℕ) (hx : dX T N ≤ x) :=
  RecoveryFocus.machine (fun j => sTape (nr := LNR) (w6M T N x hx j)) N.M

/-- **Both docks** on the unit's maps. -/
noncomputable def docksMT (x : ℕ) (hx : dX T N ≤ x) := Composition.machine (dockTFT T N x hx) (dockW6T T N x hx)

/-- **The docks' entry**: the request on `0`; `1^V`, `1^{|carriers|}`, `1^{cap_T}` on scratch tapes `bT`, `bT + 1`,
`bT + 2`; the docks' other streams (`130 … 136`, scratch `0 … bT − 1`, `bT + 3 … bT + 16`) blank; heads `0`. -/
structure DockInT (x : ℕ) (σ : WState (LNS x) LNR) (w : List Bool) (V ncar capT : ℕ) : Prop where
  s0 : σ.st (sk x 0) = frame w
  h0 : σ.sh (sk x 0) = 0
  sc : ∀ i : Fin (LNS x + 1), i.val = 161 + bT T N → σ.st i = List.replicate V true
  s1 : ∀ i : Fin (LNS x + 1), i.val = 161 + bT T N + 1 → σ.st i = List.replicate ncar true
  s2 : ∀ i : Fin (LNS x + 1), i.val = 161 + bT T N + 2 → σ.st i = List.replicate capT true
  bl : ∀ i : Fin (LNS x + 1), ((130 ≤ i.val ∧ i.val ≤ 136) ∨ (161 ≤ i.val ∧ i.val < 161 + bT T N) ∨
    (161 + bT T N + 3 ≤ i.val ∧ i.val < 161 + bT T N + 17)) → σ.st i = []
  hd : ∀ i : Fin (LNS x + 1), (i.val = 0 ∨ (130 ≤ i.val ∧ i.val ≤ 136) ∨
    (161 ≤ i.val ∧ i.val < 161 + bT T N + 17)) → σ.sh i = 0

/-- **The docks' exit**: registers and cell kept; the request kept; W6's three words on `130`, `131`, `132`; the
payloads on `133 … 136`; those heads and the request's at `0`; every other named stream unchanged. -/
structure DockOutT (x : ℕ) (σ τ : WState (LNS x) LNR) (w : List Bool) (v : ThrNumVals) (pays : Fin 4 → List Bool) :
    Prop where
  val : τ.val = σ.val
  cell : τ.cell = σ.cell
  s0 : τ.st (sk x 0) = frame w
  sPr : τ.st (sk x 130) = Data.unaryList (primesList v.cut)
  sWin : τ.st (sk x 131) = winRecs (thrMP v.M v.A v.Bs v.den)
  sMod : τ.st (sk x 132) = frame (SignedSortKey.binary v.ell0 v.pMod)
  sPay : ∀ i : Fin 4, τ.st (sk x ⟨133 + i.val, by omega⟩) = pays i
  hd : ∀ k : Fin 161, (k.val = 0 ∨ (130 ≤ k.val ∧ k.val ≤ 136)) → τ.sh (sk x k) = 0
  other : ∀ k : Fin 161, k.val ≠ 0 → (k.val < 130 ∨ 136 < k.val) →
    τ.st (sk x k) = σ.st (sk x k) ∧ τ.sh (sk x k) = σ.sh (sk x k)

theorem tf_inT (x : ℕ) (hx : dX T N ≤ x) (σ : WState (LNS x) LNR) (w : List Bool) (V ncar capT : ℕ)
    (hin : DockInT T N x σ w V ncar capT) :
    (fun j => σ.sh (tfM T N x hx j)) = (fun _ => 0) ∧
    (fun j => σ.st (tfM T N x hx j)) = Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
      (PrimThrW.TopFront2.tf2InPorts w V) (fun _ => []) := by
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · apply hin.hd
    have := tfV_lt T N x hx j.val j.isLt
    rw [tfM_val]; unfold tfV; unfold bT; unfold dX bT at hx
    split_ifs <;> omega
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · rw [Fin.addCases_left]
      have hi := i.isLt
      by_cases a0 : i.val = 0
      · have e : tfM T N x hx (Fin.castAdd T.x i) = sk x 0 := Fin.ext (by
          rw [tfM_val, sk_val]; simp [tfV, a0])
        rw [e, hin.s0]; simp [PrimThrW.TopFront2.tf2InPorts, a0]
      · by_cases a1 : i.val = 1
        · rw [hin.sc _ (by rw [tfM_val]; simp [tfV, a1])]
          simp [PrimThrW.TopFront2.tf2InPorts, a1]
        · rw [hin.bl _ (by rw [tfM_val]; simp only [Fin.val_castAdd, tfV, a0, a1, if_false]; unfold bT; split_ifs <;> omega)]
          simp [PrimThrW.TopFront2.tf2InPorts, a0, a1]
    · rw [Fin.addCases_right]
      have hk := k.isLt
      exact hin.bl _ (by
        rw [tfM_val]; simp only [Fin.val_natAdd, tfV]; unfold bT
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega)

theorem w6_inT (x : ℕ) (hx : dX T N ≤ x) (σ : WState (LNS x) LNR) (w : List Bool) (V ncar capT : ℕ)
    (hin : DockInT T N x σ w V ncar capT) {q a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit q)
    (J1 : Fin T.x → List Bool) :
    (fun j => (updS (tfM T N x hx) σ (fun _ => 0) (Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
      (PrimThrW.TopFront2.tf2OutPorts alg w V Cs) J1)).sh (w6M T N x hx j)) = (fun _ => 0) ∧
    (fun j => (updS (tfM T N x hx) σ (fun _ => 0) (Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
      (PrimThrW.TopFront2.tf2OutPorts alg w V Cs) J1)).st (w6M T N x hx j)) =
      Fin.addCases (m := 21) (n := N.x) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3InPorts w ncar capT V)
        (fun _ => []) := by
  have e0 : w6M T N x hx (Fin.castAdd N.x 0) = tfM T N x hx (Fin.castAdd T.x 0) := Fin.ext rfl
  have e20 : w6M T N x hx (Fin.castAdd N.x 20) = tfM T N x hx (Fin.castAdd T.x 1) := Fin.ext rfl
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · show dockH (tfM T N x hx) σ.sh (fun _ => 0) (w6M T N x hx j) = 0
    by_cases h0 : j.val = 0
    · rw [show j = Fin.castAdd N.x 0 from Fin.ext h0, e0, dockH_slot _ (tfM_inj T N x hx)]
    · by_cases h20 : j.val = 20
      · rw [show j = Fin.castAdd N.x 20 from Fin.ext h20, e20, dockH_slot _ (tfM_inj T N x hx)]
      · rw [dockH_other _ _ _ _ (fun i => w6_ne_tfT T N x hx j h0 h20 i)]
        apply hin.hd
        have hj := j.isLt
        rw [w6M_val]; unfold w6V; unfold bT; unfold dX bT at hx
        split_ifs <;> omega
  · show install (tfM T N x hx) σ.st _ (w6M T N x hx j) = _
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · rw [Fin.addCases_left]
      have hi := i.isLt
      by_cases h0 : i.val = 0
      · rw [show i = 0 from Fin.ext h0, e0, install_slot _ (tfM_inj T N x hx), Fin.addCases_left]
        rfl
      · by_cases h20 : i.val = 20
        · rw [show i = 20 from Fin.ext h20, e20, install_slot _ (tfM_inj T N x hx), Fin.addCases_left]
          rfl
        · rw [install_other _ _ _ _ (fun i' => w6_ne_tfT T N x hx (Fin.castAdd N.x i) h0 h20 i')]
          by_cases h1 : i.val = 1
          · rw [hin.s1 _ (by rw [w6M_val]; simp [w6V, h1])]
            simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, h1]
          · by_cases h2 : i.val = 2
            · rw [hin.s2 _ (by rw [w6M_val]; simp [w6V, h2])]
              simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, h2]
            · rw [hin.bl _ (by
                rw [w6M_val]; simp only [Fin.val_castAdd, w6V, h0, h20, if_false]; unfold bT
                split_ifs <;> omega)]
              have h20' : i.val < 20 := by omega
              simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, h0, h1, h2, h20']
    · rw [Fin.addCases_right]
      have hk := k.isLt
      have hn0 : (Fin.natAdd 21 k : Fin (21 + N.x)).val ≠ 0 := by simp
      have hn20 : (Fin.natAdd 21 k : Fin (21 + N.x)).val ≠ 20 := by simp only [Fin.val_natAdd]; omega
      rw [install_other _ _ _ _ (fun i' => w6_ne_tfT T N x hx _ hn0 hn20 i')]
      exact hin.bl _ (by
        rw [w6M_val]; simp only [Fin.val_natAdd, w6V]; unfold bT
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; omega)

variable (cap : ℕ)

/-- **Both docks on the unit's maps, run**. -/
theorem docksT_run (x : ℕ) (hx : dX T N ≤ x) (σ : WState (LNS x) LNR) (P : Shared.StarParams) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (codes : List ℕ) (tl : List Bool) (V ncar capT : ℕ)
    (hin : DockInT T N x σ (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) V ncar capT)
    (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hnc : ncar ≤ 2)
    (hcap : 1 ≤ capT) (hok : PrimThrW.TopFront2.TF2Ok Cs codes V) (hneed : N.need (P.n + capT) ≤ V) :
    ∃ τ : WState (LNS x) LNR,
      Step (docksMT T N x hx) (T.cost V + 1 + N.cost (P.n + V + capT)) (wenc cap σ).H (wenc cap σ).A
        (wenc cap τ).H (wenc cap τ).A ∧
      DockOutT x σ τ (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) (thrNumVals P Cs alg Dexp ncar capT)
        (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else []) := by
  obtain ⟨J1, -, r1⟩ := T.run Cs codes tl V hn ha hd hok
  obtain ⟨eH1, eA1⟩ := tf_inT T N x hx σ _ V ncar capT hin
  have s1 := DockW.dockS cap (tfM T N x hx) (tfM_inj T N x hx) σ (HashCell.step_in r1 eH1.symm eA1.symm)
  obtain ⟨eH2, eA2⟩ := w6_inT T N x hx σ _ V ncar capT hin Cs J1
  obtain ⟨J2, -, r2⟩ := N.run P Cs codes tl ncar capT V hn ha hd hnc hcap hok hneed
  have s2 := DockW.dockS cap (w6M T N x hx) (w6M_inj T N x hx) _ (HashCell.step_in r2 eH2.symm eA2.symm)
  refine ⟨_, Step.seq s1 s2, ?_⟩
  set σ1 := updS (tfM T N x hx) σ (fun _ => 0) (Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
    (PrimThrW.TopFront2.tf2OutPorts alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) V Cs) J1) with hσ1
  have rdW : ∀ (k : Fin 161) (i : Fin 21), w6V T N i.val = k.val →
      (updS (w6M T N x hx) σ1 (fun _ => 0) (Fin.addCases (m := 21) (n := N.x) (motive := fun _ => List Bool)
        (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
          (thrNumVals P Cs alg Dexp ncar capT)) J2)).st (sk x k) =
      PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
        (thrNumVals P Cs alg Dexp ncar capT) i ∧
      (updS (w6M T N x hx) σ1 (fun _ => 0) (Fin.addCases (m := 21) (n := N.x) (motive := fun _ => List Bool)
        (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
          (thrNumVals P Cs alg Dexp ncar capT)) J2)).sh (sk x k) = 0 := by
    intro k i hk
    have e : sk x k = w6M T N x hx (Fin.castAdd N.x i) := Fin.ext (by rw [sk_val, w6M_val]; simp [hk])
    refine ⟨?_, ?_⟩
    · show install (w6M T N x hx) _ _ (sk x k) = _
      rw [e, install_slot _ (w6M_inj T N x hx), Fin.addCases_left]
    · show dockH (w6M T N x hx) _ _ (sk x k) = _
      rw [e, dockH_slot _ (w6M_inj T N x hx)]
  have w6ne : ∀ (k : Fin 161), k.val ≠ 0 → (k.val < 130 ∨ 132 < k.val) → ∀ j, w6M T N x hx j ≠ sk x k := by
    intro k h0 hk j h
    have e : w6V T N j.val = k.val := by have := congrArg Fin.val h; rwa [w6M_val, sk_val] at this
    have hj := j.isLt
    have hk' := k.isLt
    unfold w6V at e; unfold bT at e
    split_ifs at e <;> omega
  have tfne : ∀ (k : Fin 161), k.val ≠ 0 → (k.val < 133 ∨ 136 < k.val) → ∀ j, tfM T N x hx j ≠ sk x k := by
    intro k h0 hk j h
    have e : tfV T N j.val = k.val := by have := congrArg Fin.val h; rwa [tfM_val, sk_val] at this
    have hj := j.isLt
    have hk' := k.isLt
    unfold tfV at e; unfold bT at e
    split_ifs at e <;> omega
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(rdW 0 0 (by simp [w6V])).1]; rfl
  · rw [(rdW 130 17 (by simp [w6V])).1]; rfl
  · rw [(rdW 131 18 (by simp [w6V])).1]; rfl
  · rw [(rdW 132 19 (by simp [w6V])).1]; rfl
  · intro i
    have hi := i.isLt
    show install (w6M T N x hx) (install (tfM T N x hx) σ.st _) _ (sk x ⟨133 + i.val, _⟩) = _
    rw [install_other _ _ _ _ (w6ne ⟨133 + i.val, by omega⟩ (by simp) (by simp; omega))]
    have e : sk x ⟨133 + i.val, by omega⟩ = tfM T N x hx (Fin.castAdd T.x ⟨i.val + 2, by omega⟩) :=
      Fin.ext (by rw [sk_val, tfM_val]; simp [tfV]; split_ifs <;> omega)
    rw [e, install_slot _ (tfM_inj T N x hx), Fin.addCases_left]
    have a6 : i.val + 2 < 6 := by omega
    by_cases hh : i.val < a'
    · simp [PrimThrW.TopFront2.tf2OutPorts, hh, a6]
    · simp [PrimThrW.TopFront2.tf2OutPorts, hh, a6]
  · intro k hk
    rcases hk with h0 | h
    · exact (rdW k 0 (by simp [w6V, h0])).2
    · by_cases hm : k.val ≤ 132
      · have hv : w6V T N (k.val - 113) = k.val := by
          unfold w6V
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          omega
        exact (rdW k ⟨k.val - 113, by omega⟩ hv).2
      · show dockH (w6M T N x hx) (dockH (tfM T N x hx) σ.sh (fun _ => 0)) (fun _ => 0) (sk x k) = 0
        rw [dockH_other _ _ _ _ (w6ne k (by omega) (by omega))]
        have e : sk x k = tfM T N x hx (Fin.castAdd T.x ⟨k.val - 131, by omega⟩) :=
          Fin.ext (by rw [sk_val, tfM_val]; simp only [Fin.val_castAdd, tfV]; split_ifs <;> omega)
        rw [e, dockH_slot _ (tfM_inj T N x hx)]
  · intro k h0 hk
    refine ⟨?_, ?_⟩
    · show install (w6M T N x hx) (install (tfM T N x hx) σ.st _) _ (sk x k) = _
      rw [install_other _ _ _ _ (w6ne k h0 (by omega)), install_other _ _ _ _ (tfne k h0 (by omega))]
    · show dockH (w6M T N x hx) (dockH (tfM T N x hx) σ.sh _) _ (sk x k) = _
      rw [dockH_other _ _ _ _ (w6ne k h0 (by omega)), dockH_other _ _ _ _ (tfne k h0 (by omega))]

end Dock

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
