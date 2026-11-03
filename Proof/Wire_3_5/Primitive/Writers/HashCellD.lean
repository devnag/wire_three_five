import Proof.Wire_3_5.Primitive.Writers.HashCellA
import Proof.Wire_3_5.Primitive.Writers.DockW
import Proof.Wire_3_5.Primitive.ThresholdWriter.PortsE
import Proof.Wire_3_5.Primitive.ThresholdWriter.NumsPort4

/-! # HASH setup (C), P2b part 2: the front end and the numbers machine, docked on the cell's streams

P3:3071-3091 (the preprocessing: each circuit's retained top children, in time polynomial in `n`) and P3:2543-2558,
2596-2604, 2150-2157, 2220-2231 (the THR call's numbers: `|𝒢|`, `K`, the cutoff, the primes, `Σp`, `τ₀`, the fixed hash's
`M, A, B_*, J, t, e, ℓ₀` and the modulus): the HASH cell docks a front end `T : TopFrontPort3 alg` and a numbers machine
`N : NumsPort4 alg D` (built once: `TF3Cost.topFront3`, `W6.numsW6`) on its streams (`DockW.dockS`), on the layout
`LNS (cX T N)` whose extra streams hold the front end's scratch, its four native-word ports and the numbers machine's
scratch:

* the front end: port `0` on the request stream `0`, the count `1^V` on `2`, the payloads on `133 … 136`;
* the numbers machine: port `0` on `0`, `1^{|carriers|}`, `1^{cap_T}` on `153`, `154`, the fourteen numbers in unary
  on `139 … 152`, the primes on `130`, the level records on `131`, the modulus word on `132`, the count on `2`.

* `cX`, `tfP`, `tfV`, `tfMap`, `w6P`, `w6V`, `w6Map` (injective); `dockTF`, `dockW6`, `docksM`;
* **`DockIn`**, **`DockOut`**, **`docks_run`** (both docks from any cell state with the inputs; generic in the cell's
  other streams and registers, so the THR unit chain's front can dock the same way).

Paper quantities of the main type: the payloads `payOf (Cs i)`, the primes `≤ cut`, the fourteen THR numbers in unary
(`thrNumVals`), on the cell's streams. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimThrW.Joins NearCubicWires.SupplierPipeline

/-! ## The port tables -/

/-- The front end's ports `0 … 5` as stream indices. -/
def tfP : Fin 6 → ℕ := ![0, 2, 133, 134, 135, 136]

/-- The numbers machine's ports `0 … 20` as stream indices. -/
def w6P : Fin 21 → ℕ :=
  ![0, 153, 154, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 130, 131, 132, 2]

theorem tfP_le : ∀ i : Fin 6, tfP i ≤ 136 := by decide
theorem tfP_inj : Function.Injective tfP := by decide
theorem tfP_rng : ∀ i : Fin 6, tfP i = 0 ∨ tfP i = 2 ∨ (133 ≤ tfP i ∧ tfP i ≤ 136) := by decide
theorem tfP_mid : ∀ i : Fin 6, i.val ≠ 0 → i.val ≠ 1 → 133 ≤ tfP i ∧ tfP i ≤ 136 := by decide
theorem tfP_pay : ∀ i : Fin 4, tfP ⟨i.val + 2, by omega⟩ = 133 + i.val := by decide
theorem w6P_le : ∀ i : Fin 21, w6P i ≤ 154 := by decide
theorem w6P_inj : Function.Injective w6P := by decide
theorem w6P_rng : ∀ i : Fin 21, w6P i = 0 ∨ w6P i = 2 ∨ (130 ≤ w6P i ∧ w6P i ≤ 132) ∨ (139 ≤ w6P i ∧ w6P i ≤ 154) := by
  decide
theorem w6P_mid : ∀ i : Fin 21, i.val ≠ 0 → i.val ≠ 20 → (130 ≤ w6P i ∧ w6P i ≤ 132) ∨ (139 ≤ w6P i ∧ w6P i ≤ 154) := by
  decide
theorem w6P_blk : ∀ i : Fin 21, i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 20 →
    (130 ≤ w6P i ∧ w6P i ≤ 132) ∨ (139 ≤ w6P i ∧ w6P i ≤ 152) := by decide
theorem w6P_surj : ∀ k : Fin 155, (k.val = 0 ∨ k.val = 2 ∨ (130 ≤ k.val ∧ k.val ≤ 132) ∨ 139 ≤ k.val) →
    ∃ j : Fin 21, w6P j = k.val := by decide
theorem w6P_num : ∀ i : Fin 14, w6P ⟨i.val + 3, by omega⟩ = 139 + i.val := by decide

section Dock
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- The cell's extra streams: the front end's scratch, its four native-word ports, the numbers machine's scratch. -/
abbrev cX : ℕ := T.x + 4 + N.x

/-- The front end's tape `j` as a stream index. -/
def tfV (j : ℕ) : ℕ := if h : j < 6 then tfP ⟨j, h⟩ else if j < 10 then 161 + T.x + (j - 6) else 161 + (j - 10)

theorem tfV_lt (j : ℕ) (hj : j < 10 + T.x) : tfV T j < 161 + T.x + 4 := by
  unfold tfV
  split_ifs with h1 h2
  · have := tfP_le ⟨j, h1⟩; omega
  · omega
  · omega

/-- The front end's tapes on the cell's streams. -/
def tfMap (j : Fin (10 + T.x)) : Fin (LNS (cX T N) + 1) :=
  ⟨tfV T j.val, by have := tfV_lt T j.val j.isLt; unfold LNS cX; omega⟩

theorem tfMap_val (j : Fin (10 + T.x)) : (tfMap T N j).val = tfV T j.val := rfl

theorem tfMap_inj : Function.Injective (tfMap T N) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have e : tfV T a.val = tfV T b.val := congrArg Fin.val h
  apply Fin.ext
  unfold tfV at e
  by_cases h1 : a.val < 6 <;> by_cases h2 : b.val < 6
  · rw [dif_pos h1, dif_pos h2] at e
    have := congrArg Fin.val (tfP_inj e)
    simpa using this
  · rw [dif_pos h1, dif_neg h2] at e
    have := tfP_le ⟨a.val, h1⟩
    split_ifs at e <;> omega
  · rw [dif_neg h1, dif_pos h2] at e
    have := tfP_le ⟨b.val, h2⟩
    split_ifs at e <;> omega
  · rw [dif_neg h1, dif_neg h2] at e
    split_ifs at e <;> omega

/-- The numbers machine's tape `j` as a stream index. -/
def w6V (j : ℕ) : ℕ := if h : j < 21 then w6P ⟨j, h⟩ else 161 + T.x + 4 + (j - 21)

/-- The numbers machine's tapes on the cell's streams. -/
def w6Map (j : Fin (21 + N.x)) : Fin (LNS (cX T N) + 1) :=
  ⟨w6V T j.val, by
    have := j.isLt
    unfold w6V LNS cX
    split_ifs with h1
    · have := w6P_le ⟨j.val, h1⟩; omega
    · omega⟩

theorem w6Map_val (j : Fin (21 + N.x)) : (w6Map T N j).val = w6V T j.val := rfl

theorem w6Map_inj : Function.Injective (w6Map T N) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have e : w6V T a.val = w6V T b.val := congrArg Fin.val h
  apply Fin.ext
  unfold w6V at e
  by_cases h1 : a.val < 21 <;> by_cases h2 : b.val < 21
  · rw [dif_pos h1, dif_pos h2] at e
    have := congrArg Fin.val (w6P_inj e)
    simpa using this
  · rw [dif_pos h1, dif_neg h2] at e
    have := w6P_le ⟨a.val, h1⟩
    omega
  · rw [dif_neg h1, dif_pos h2] at e
    have := w6P_le ⟨b.val, h2⟩
    omega
  · rw [dif_neg h1, dif_neg h2] at e
    omega

theorem tf_sk (i : Fin 10) (h : i.val < 6) :
    tfMap T N (Fin.castAdd T.x i) = sk (cX T N) ⟨tfP ⟨i.val, h⟩, by have := tfP_le ⟨i.val, h⟩; omega⟩ :=
  Fin.ext (by rw [tfMap_val, sk_val]; simp only [Fin.val_castAdd, tfV, dif_pos h])

theorem tf_sT (i : Fin 10) (h : 6 ≤ i.val) :
    tfMap T N (Fin.castAdd T.x i) = sT (cX T N) ⟨T.x + (i.val - 6), by have := i.isLt; unfold cX; omega⟩ :=
  Fin.ext (by
    rw [tfMap_val, sT_val]
    simp only [Fin.val_castAdd, tfV, dif_neg (show ¬ i.val < 6 by omega), if_pos i.isLt]
    omega)

theorem tf_scr (k : Fin T.x) : tfMap T N (Fin.natAdd 10 k) = sT (cX T N) ⟨k.val, by have := k.isLt; unfold cX; omega⟩ :=
  Fin.ext (by
    rw [tfMap_val, sT_val]
    simp only [Fin.val_natAdd, tfV]
    rw [dif_neg (by omega), if_neg (by omega)]
    omega)

theorem w6_sk (i : Fin 21) : w6Map T N (Fin.castAdd N.x i) = sk (cX T N) ⟨w6P i, by have := w6P_le i; omega⟩ :=
  Fin.ext (by rw [w6Map_val, sk_val]; simp only [Fin.val_castAdd, w6V, dif_pos i.isLt])

theorem w6_scr (k : Fin N.x) :
    w6Map T N (Fin.natAdd 21 k) = sT (cX T N) ⟨T.x + 4 + k.val, by have := k.isLt; unfold cX; omega⟩ :=
  Fin.ext (by
    rw [w6Map_val, sT_val]
    simp only [Fin.val_natAdd, w6V]
    rw [dif_neg (by omega)]
    omega)

theorem tf_ne_sk (k : Fin 161) (h0 : k.val ≠ 0) (h2 : k.val ≠ 2) (hk : k.val < 133 ∨ 136 < k.val)
    (j : Fin (10 + T.x)) : tfMap T N j ≠ sk (cX T N) k := by
  intro h
  have e : tfV T j.val = k.val := by have := congrArg Fin.val h; rwa [tfMap_val, sk_val] at this
  have hj := j.isLt
  have hk' := k.isLt
  unfold tfV at e
  split_ifs at e with h1 h3
  · rcases tfP_rng ⟨j.val, h1⟩ with r | r | r <;> omega
  · omega
  · omega

theorem w6_ne_sk (k : Fin 161) (h0 : k.val ≠ 0) (h2 : k.val ≠ 2)
    (hk : k.val < 130 ∨ (133 ≤ k.val ∧ k.val ≤ 138) ∨ 154 < k.val) (j : Fin (21 + N.x)) :
    w6Map T N j ≠ sk (cX T N) k := by
  intro h
  have e : w6V T j.val = k.val := by have := congrArg Fin.val h; rwa [w6Map_val, sk_val] at this
  have hk' := k.isLt
  unfold w6V at e
  split_ifs at e with h1
  · rcases w6P_rng ⟨j.val, h1⟩ with r | r | r | r <;> omega
  · omega

theorem w6_ne_tf (j : Fin (21 + N.x)) (h0 : j.val ≠ 0) (h20 : j.val ≠ 20) (i : Fin (10 + T.x)) :
    tfMap T N i ≠ w6Map T N j := by
  intro h
  have e : tfV T i.val = w6V T j.val := by have := congrArg Fin.val h; rwa [tfMap_val, w6Map_val] at this
  have hlt := tfV_lt T i.val i.isLt
  unfold w6V at e
  split_ifs at e with h1
  · have r := w6P_mid ⟨j.val, h1⟩ h0 h20
    unfold tfV at e
    split_ifs at e with h3 h4
    · rcases tfP_rng ⟨i.val, h3⟩ with r' | r' | r' <;> omega
    · omega
    · omega
  · omega

/-- The front end, docked. -/
noncomputable def dockTF := RecoveryFocus.machine (fun j => sTape (nr := LNR) (tfMap T N j)) T.M

/-- The numbers machine, docked. -/
noncomputable def dockW6 := RecoveryFocus.machine (fun j => sTape (nr := LNR) (w6Map T N j)) N.M

/-- **Both docks**: the front end, then the numbers machine. -/
noncomputable def docksM := Composition.machine (dockTF T N) (dockW6 T N)

/-- **The docks' entry**: the request on `0`, `1^V` on `2`, `1^{|carriers|}`, `1^{cap_T}` on `153`, `154`, the
docks' other streams (`130 … 136`, `139 … 152`, the extra streams) blank, all their heads at `0`. -/
structure DockIn (σ : WState (LNS (cX T N)) LNR) (w : List Bool) (V ncar capT : ℕ) : Prop where
  s0 : σ.st (sk (cX T N) 0) = frame w
  s2 : σ.st (sk (cX T N) 2) = List.replicate V true
  s153 : σ.st (sk (cX T N) 153) = List.replicate ncar true
  s154 : σ.st (sk (cX T N) 154) = List.replicate capT true
  bl : ∀ k : Fin 161, ((130 ≤ k.val ∧ k.val ≤ 136) ∨ (139 ≤ k.val ∧ k.val ≤ 152)) → σ.st (sk (cX T N) k) = []
  blT : ∀ k : Fin (cX T N), σ.st (sT (cX T N) k) = []
  h0 : σ.sh (sk (cX T N) 0) = 0
  h2 : σ.sh (sk (cX T N) 2) = 0
  hP : ∀ k : Fin 161, ((130 ≤ k.val ∧ k.val ≤ 136) ∨ (139 ≤ k.val ∧ k.val ≤ 154)) → σ.sh (sk (cX T N) k) = 0
  hT : ∀ k : Fin (cX T N), σ.sh (sT (cX T N) k) = 0

/-- **The docks' exit**: the registers and the cell as before; the request, `1^V`, `1^{|carriers|}`, `1^{cap_T}`
kept; the primes, the level records, the modulus word on `130`, `131`, `132`; the payloads `pays` on `133 … 136`; the
fourteen numbers `v` in unary on `139 … 152`; those heads at `0`; every other stream `k < 161` unchanged. -/
structure DockOut (σ τ : WState (LNS (cX T N)) LNR) (w : List Bool) (V ncar capT : ℕ) (v : ThrNumVals)
    (pays : Fin 4 → List Bool) : Prop where
  val : τ.val = σ.val
  cell : τ.cell = σ.cell
  s0 : τ.st (sk (cX T N) 0) = frame w
  s2 : τ.st (sk (cX T N) 2) = List.replicate V true
  s153 : τ.st (sk (cX T N) 153) = List.replicate ncar true
  s154 : τ.st (sk (cX T N) 154) = List.replicate capT true
  sPr : τ.st (sk (cX T N) 130) = PrimAsm.Data.unaryList (primesList v.cut)
  sWin : τ.st (sk (cX T N) 131) = winRecs (thrMP v.M v.A v.Bs v.den)
  sMod : τ.st (sk (cX T N) 132) = frame (SignedSortKey.binary v.ell0 v.pMod)
  sPay : ∀ i : Fin 4, τ.st (sk (cX T N) ⟨133 + i.val, by omega⟩) = pays i
  sNum : ∀ i : Fin 14, τ.st (sk (cX T N) ⟨139 + i.val, by omega⟩) = List.replicate (v.get i) true
  hd : ∀ k : Fin 161, (k.val = 0 ∨ k.val = 2 ∨ (130 ≤ k.val ∧ k.val ≤ 136) ∨ (139 ≤ k.val ∧ k.val ≤ 154)) →
    τ.sh (sk (cX T N) k) = 0
  other : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 2 → (k.val < 130 ∨ (137 ≤ k.val ∧ k.val ≤ 138) ∨ 154 < k.val) →
    τ.st (sk (cX T N) k) = σ.st (sk (cX T N) k) ∧ τ.sh (sk (cX T N) k) = σ.sh (sk (cX T N) k)

theorem step_in {t s n : ℕ} {M : Machine t s} {h0 h0' : Fin t → ℕ} {t0 t0' : Fin t → List Bool}
    {h1 : Fin t → ℕ} {t1 : Fin t → List Bool} (h : Step M n h0 t0 h1 t1) (e1 : h0 = h0') (e2 : t0 = t0') :
    Step M n h0' t0' h1 t1 := by
  subst e1; subst e2; exact h

/-- The front end's entry, read off the docks' entry. -/
theorem tf_entry (σ : WState (LNS (cX T N)) LNR) (w : List Bool) (V ncar capT : ℕ) (hin : DockIn T N σ w V ncar capT) :
    (fun j => σ.sh (tfMap T N j)) = (fun _ => 0) ∧
    (fun j => σ.st (tfMap T N j)) = Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
      (PrimThrW.TopFront2.tf2InPorts w V) (fun _ => []) := by
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · by_cases h : i.val < 6
      · rw [tf_sk T N i h]
        rcases tfP_rng ⟨i.val, h⟩ with r | r | r
        · rw [show sk (cX T N) ⟨tfP ⟨i.val, h⟩, _⟩ = sk (cX T N) 0 from congrArg (sk (cX T N)) (Fin.ext r)]
          exact hin.h0
        · rw [show sk (cX T N) ⟨tfP ⟨i.val, h⟩, _⟩ = sk (cX T N) 2 from congrArg (sk (cX T N)) (Fin.ext r)]
          exact hin.h2
        · exact hin.hP _ (Or.inl ⟨(show 130 ≤ tfP ⟨i.val, h⟩ by omega), (show tfP ⟨i.val, h⟩ ≤ 136 by omega)⟩)
      · rw [tf_sT T N i (by omega)]; exact hin.hT _
    · rw [tf_scr]; exact hin.hT _
  · refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · rw [Fin.addCases_left]
      by_cases h : i.val < 6
      · rw [tf_sk T N i h]
        by_cases h0 : i.val = 0
        · have r : tfP ⟨i.val, h⟩ = 0 := by rw [show (⟨i.val, h⟩ : Fin 6) = 0 from Fin.ext h0]; rfl
          rw [show sk (cX T N) ⟨tfP ⟨i.val, h⟩, _⟩ = sk (cX T N) 0 from congrArg (sk (cX T N)) (Fin.ext r), hin.s0]
          simp [PrimThrW.TopFront2.tf2InPorts, h0]
        · by_cases h1 : i.val = 1
          · have r : tfP ⟨i.val, h⟩ = 2 := by rw [show (⟨i.val, h⟩ : Fin 6) = 1 from Fin.ext h1]; rfl
            rw [show sk (cX T N) ⟨tfP ⟨i.val, h⟩, _⟩ = sk (cX T N) 2 from congrArg (sk (cX T N)) (Fin.ext r), hin.s2]
            simp [PrimThrW.TopFront2.tf2InPorts, h1]
          · have r := tfP_mid ⟨i.val, h⟩ h0 h1
            rw [hin.bl _ (Or.inl ⟨(show 130 ≤ tfP ⟨i.val, h⟩ by omega), (show tfP ⟨i.val, h⟩ ≤ 136 by omega)⟩)]
            simp [PrimThrW.TopFront2.tf2InPorts, h0, h1]
      · rw [tf_sT T N i (by omega), hin.blT]
        have h0 : i.val ≠ 0 := by omega
        have h1 : i.val ≠ 1 := by omega
        simp [PrimThrW.TopFront2.tf2InPorts, h0, h1]
    · rw [Fin.addCases_right, tf_scr, hin.blT]

/-- The numbers machine's entry after the front end. -/
theorem w6_entry (σ : WState (LNS (cX T N)) LNR) (w : List Bool) (V ncar capT : ℕ) (hin : DockIn T N σ w V ncar capT)
    {q a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit q) (J1 : Fin T.x → List Bool) :
    (fun j => (updS (tfMap T N) σ (fun _ => 0) (Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
      (PrimThrW.TopFront2.tf2OutPorts alg w V Cs) J1)).sh (w6Map T N j)) = (fun _ => 0) ∧
    (fun j => (updS (tfMap T N) σ (fun _ => 0) (Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
      (PrimThrW.TopFront2.tf2OutPorts alg w V Cs) J1)).st (w6Map T N j)) =
      Fin.addCases (m := 21) (n := N.x) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3InPorts w ncar capT V)
        (fun _ => []) := by
  have e0 : w6Map T N (Fin.castAdd N.x 0) = tfMap T N (Fin.castAdd T.x 0) := Fin.ext rfl
  have e20 : w6Map T N (Fin.castAdd N.x 20) = tfMap T N (Fin.castAdd T.x 1) := Fin.ext rfl
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · show dockH (tfMap T N) σ.sh (fun _ => 0) (w6Map T N j) = 0
    by_cases h0 : j.val = 0
    · rw [show j = Fin.castAdd N.x 0 from Fin.ext h0, e0, dockH_slot _ (tfMap_inj T N)]
    · by_cases h20 : j.val = 20
      · rw [show j = Fin.castAdd N.x 20 from Fin.ext h20, e20, dockH_slot _ (tfMap_inj T N)]
      · rw [dockH_other _ _ _ _ (fun i => w6_ne_tf T N j h0 h20 i)]
        by_cases hl : j.val < 21
        · rw [show j = Fin.castAdd N.x ⟨j.val, hl⟩ from Fin.ext rfl, w6_sk]
          refine hin.hP _ ?_
          show (130 ≤ w6P ⟨j.val, hl⟩ ∧ w6P ⟨j.val, hl⟩ ≤ 136) ∨ (139 ≤ w6P ⟨j.val, hl⟩ ∧ w6P ⟨j.val, hl⟩ ≤ 154)
          rcases w6P_mid ⟨j.val, hl⟩ h0 h20 with r | r
          · exact Or.inl ⟨r.1, by omega⟩
          · exact Or.inr r
        · rw [show j = Fin.natAdd 21 ⟨j.val - 21, by have := j.isLt; omega⟩ from Fin.ext (by simp; omega), w6_scr]
          exact hin.hT _
  · show install (tfMap T N) σ.st _ (w6Map T N j) = _
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · rw [Fin.addCases_left]
      by_cases h0 : i.val = 0
      · rw [show i = 0 from Fin.ext h0, e0, install_slot _ (tfMap_inj T N), Fin.addCases_left]
        rfl
      · by_cases h20 : i.val = 20
        · rw [show i = 20 from Fin.ext h20, e20, install_slot _ (tfMap_inj T N), Fin.addCases_left]
          rfl
        · rw [install_other _ _ _ _ (fun i' => w6_ne_tf T N (Fin.castAdd N.x i) h0 h20 i'), w6_sk]
          by_cases h1 : i.val = 1
          · rw [show i = 1 from Fin.ext h1]
            exact hin.s153
          · by_cases h2 : i.val = 2
            · rw [show i = 2 from Fin.ext h2]
              exact hin.s154
            · have r := w6P_blk i h0 h1 h2 h20
              rw [hin.bl _ (by
                show (130 ≤ w6P i ∧ w6P i ≤ 136) ∨ (139 ≤ w6P i ∧ w6P i ≤ 152)
                rcases r with r | r
                · exact Or.inl ⟨r.1, by omega⟩
                · exact Or.inr r)]
              have h20' : i.val < 20 := by omega
              simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, h0, h1, h2, h20']
    · rw [Fin.addCases_right, install_other _ _ _ _ (fun i' => w6_ne_tf T N (Fin.natAdd 21 k)
        (by simp only [Fin.val_natAdd]; omega) (by simp only [Fin.val_natAdd]; omega) i'),
        w6_scr, hin.blT]

variable (cap : ℕ)

/-- **Both docks, run**: from a cell state with the docks' entry, at a THR tuple with the front end's `TF2Ok` and the
numbers machine's need, the docks' exit at the call's numbers `thrNumVals P Cs alg D ncar capT` and payloads. -/
theorem docks_run (σ : WState (LNS (cX T N)) LNR) (P : Shared.StarParams) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (codes : List ℕ) (tl : List Bool) (V ncar capT : ℕ)
    (hin : DockIn T N σ (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) V ncar capT)
    (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hnc : ncar ≤ 2)
    (hcap : 1 ≤ capT) (hok : PrimThrW.TopFront2.TF2Ok Cs codes V) (hneed : N.need (P.n + capT) ≤ V) :
    ∃ τ : WState (LNS (cX T N)) LNR,
      Step (docksM T N) (T.cost V + 1 + N.cost (P.n + V + capT)) (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H
        (wenc cap τ).A ∧
      DockOut T N σ τ (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) V ncar capT
        (thrNumVals P Cs alg Dexp ncar capT)
        (fun i => if h : i.val < a' then PrimThrW.TopFront.payOf alg (Cs ⟨i.val, h⟩) else []) := by
  obtain ⟨J1, -, r1⟩ := T.run Cs codes tl V hn ha hd hok
  obtain ⟨eH1, eA1⟩ := tf_entry T N σ _ V ncar capT hin
  have s1 := DockW.dockS cap (tfMap T N) (tfMap_inj T N) σ (step_in r1 eH1.symm eA1.symm)
  obtain ⟨eH2, eA2⟩ := w6_entry T N σ _ V ncar capT hin Cs J1
  obtain ⟨J2, -, r2⟩ := N.run P Cs codes tl ncar capT V hn ha hd hnc hcap hok hneed
  have s2 := DockW.dockS cap (w6Map T N) (w6Map_inj T N) _ (step_in r2 eH2.symm eA2.symm)
  refine ⟨_, Step.seq s1 s2, ?_⟩
  -- reading the exit
  have rdW : ∀ (k : Fin 161) (i : Fin 21), w6P i = k.val → (updS (w6Map T N) (updS (tfMap T N) σ (fun _ => 0)
      (Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
        (PrimThrW.TopFront2.tf2OutPorts alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) V Cs) J1))
      (fun _ => 0) (Fin.addCases (m := 21) (n := N.x) (motive := fun _ => List Bool)
        (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
          (thrNumVals P Cs alg Dexp ncar capT)) J2)).st (sk (cX T N) k) =
      PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
        (thrNumVals P Cs alg Dexp ncar capT) i ∧
      (updS (w6Map T N) (updS (tfMap T N) σ (fun _ => 0)
      (Fin.addCases (m := 10) (n := T.x) (motive := fun _ => List Bool)
        (PrimThrW.TopFront2.tf2OutPorts alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) V Cs) J1))
      (fun _ => 0) (Fin.addCases (m := 21) (n := N.x) (motive := fun _ => List Bool)
        (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
          (thrNumVals P Cs alg Dexp ncar capT)) J2)).sh (sk (cX T N) k) = 0 := by
    intro k i hk
    have e : sk (cX T N) k = w6Map T N (Fin.castAdd N.x i) := by rw [w6_sk]; exact congrArg (sk (cX T N)) (Fin.ext hk.symm)
    refine ⟨?_, ?_⟩
    · show install (w6Map T N) _ _ (sk (cX T N) k) = _
      rw [e, install_slot _ (w6Map_inj T N), Fin.addCases_left]
    · show dockH (w6Map T N) _ _ (sk (cX T N) k) = _
      rw [e, dockH_slot _ (w6Map_inj T N)]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(rdW 0 0 rfl).1]; rfl
  · rw [(rdW 2 20 rfl).1]; rfl
  · rw [(rdW 153 1 rfl).1]; rfl
  · rw [(rdW 154 2 rfl).1]; rfl
  · rw [(rdW 130 17 rfl).1]; rfl
  · rw [(rdW 131 18 rfl).1]; rfl
  · rw [(rdW 132 19 rfl).1]; rfl
  · intro i
    have hi := i.isLt
    show install (w6Map T N) (install (tfMap T N) σ.st _) _ (sk (cX T N) ⟨133 + i.val, _⟩) = _
    rw [install_other _ _ _ _ (fun j => w6_ne_sk T N _ (show 133 + i.val ≠ 0 by omega) (show 133 + i.val ≠ 2 by omega)
      (Or.inr (Or.inl ⟨show 133 ≤ 133 + i.val by omega, show 133 + i.val ≤ 138 by omega⟩)) j)]
    have e : sk (cX T N) ⟨133 + i.val, by omega⟩ = tfMap T N (Fin.castAdd T.x ⟨i.val + 2, by omega⟩) := by
      rw [tf_sk T N _ (by simp; omega)]
      exact congrArg (sk (cX T N)) (Fin.ext (by simp only; rw [tfP_pay i]))
    rw [e, install_slot _ (tfMap_inj T N), Fin.addCases_left]
    simp only [PrimThrW.TopFront2.tf2OutPorts]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    by_cases hh : i.val < a'
    · rw [dif_pos (show i.val + 2 - 2 < a' by omega), dif_pos hh]
      congr 2
    · rw [dif_neg (show ¬ (i.val + 2 - 2 < a') by omega), dif_neg hh]
  · intro i
    have hi := i.isLt
    rw [(rdW _ ⟨i.val + 3, by omega⟩ (by rw [w6P_num i])).1]
    simp only [PrimThrW.Nums3.nums3OutPorts, PrimThrW.NumsP.numsOutPorts]
    rw [dif_pos (show i.val + 3 < 20 by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      dif_pos (show i.val + 3 < 17 by omega)]
    congr 2
  · intro k hk
    by_cases hm : 133 ≤ k.val ∧ k.val ≤ 136
    · show dockH (w6Map T N) (dockH (tfMap T N) σ.sh (fun _ => 0)) (fun _ => 0) (sk (cX T N) k) = 0
      rw [dockH_other _ _ _ _ (fun j => w6_ne_sk T N _ (by omega) (by omega) (Or.inr (Or.inl ⟨hm.1, by omega⟩)) j)]
      have e : sk (cX T N) k = tfMap T N (Fin.castAdd T.x ⟨k.val - 131, by omega⟩) := by
        apply Fin.ext
        rw [sk_val, tfMap_val]
        simp only [Fin.val_castAdd, tfV]
        rw [dif_pos (show k.val - 131 < 6 by omega)]
        have e6 : (⟨k.val - 131, by omega⟩ : Fin 6) = ⟨(k.val - 133) + 2, by omega⟩ := Fin.ext (by simp only; omega)
        rw [e6, tfP_pay ⟨k.val - 133, by omega⟩]
        simp only
        omega
      rw [e, dockH_slot _ (tfMap_inj T N)]
    · obtain ⟨j, hj⟩ := w6P_surj ⟨k.val, by omega⟩ (by simp only; omega)
      exact (rdW k j hj).2
  · intro k h0 h2 hk
    have hk' : k.val < 133 ∨ 136 < k.val := by omega
    have hk6 : k.val < 130 ∨ (133 ≤ k.val ∧ k.val ≤ 138) ∨ 154 < k.val := by omega
    refine ⟨?_, ?_⟩
    · show install (w6Map T N) (install (tfMap T N) σ.st _) _ (sk (cX T N) k) = _
      rw [install_other _ _ _ _ (fun j => w6_ne_sk T N k h0 h2 hk6 j),
        install_other _ _ _ _ (fun j => tf_ne_sk T N k h0 h2 hk' j)]
    · show dockH (w6Map T N) (dockH (tfMap T N) σ.sh _) _ (sk (cX T N) k) = _
      rw [dockH_other _ _ _ _ (fun j => w6_ne_sk T N k h0 h2 hk6 j),
        dockH_other _ _ _ _ (fun j => tf_ne_sk T N k h0 h2 hk' j)]

end Dock

end NearCubicWires.WireExponent3_5.PrimAsm.HashCell
