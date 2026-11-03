import Lean
import Proof.Wire_3_5.Foundations.OutMachineCarBound
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.Primitive.Writers.ReqBridge
import Proof.Wire_3_5.FinalPass.S5TNum3Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceM
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Foundations.OutMachineCarIface
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Foundations.OutMachineCarGenBase


noncomputable section
set_option maxRecDepth 4096


/-! # X6 carrier phase, part 8: the phase

"For each name, use the regular filter of filt:gap on its signed mixed-residual population" (P3:3071-3076); the final
pass reads each named carrier's atoms as the table `gatesW h (maskGates X)` (P3:3049-3050, 3074-3080), in polynomial
time (P3:3175-3178). From the final pass's input `frame (fpIn r)` (the request's word, then the seed word), the pipeline
`carM DtC (eraseOf keepL)` at the capacity `2^{DtC}·(|fpIn| + 1)^{DtC}` writes the five carrier words:

* **`carRun`**: the run at every request, within `CsOf DtC·(|fpIn| + 1)^{2·DtC}` steps, the words on `sOutE`, the
  input kept, every other stream `0^T`, every head and register `0`;
* **`carPhase : ∀ l, CarPhaseM l`** (the `CoreWordsM`, the zero-residue contract);
* **`CarPhaseMJ l`** `:= CoreWordsMJ l 5 (carWords l)`, **`carPhaseJ := (carPhase l).toMJ`** (#240, the
  bounded-residue contract SA and SB dock).

Paper quantity of the main type: the carriers' mask tables and gate counts (P3:3049-3050, 3071-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarGen
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarS NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound

/-- **The carrier phase's run** at every request of every call family. -/
theorem carRun (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) (σ : OSt) (hin : σ.st (oS sIN) = frame (fpIn l F kclk coef A a ha r))
    (hsh : ∀ i, σ.sh i = 0) (hbl : ∀ i, i ≠ oS sIN → σ.st i = []) (hv : ∀ q, σ.val q = 0)
    (hc : σ.cell = false) :
    ∃ (τ : OSt) (m : ℕ), m ≤ CsOf DtC * ((fpIn l F kclk coef A a ha r).length + 1) ^ (2 * DtC) ∧
      Step (carM DtC (eraseOf keepL)) m
        (wenc (2 ^ DtC * ((fpIn l F kclk coef A a ha r).length + 1) ^ DtC) σ).H
        (wenc (2 ^ DtC * ((fpIn l F kclk coef A a ha r).length + 1) ^ DtC) σ).A
        (wenc (2 ^ DtC * ((fpIn l F kclk coef A a ha r).length + 1) ^ DtC) τ).H
        (wenc (2 ^ DtC * ((fpIn l F kclk coef A a ha r).length + 1) ^ DtC) τ).A ∧
      (∀ k : Fin 5, τ.st (sOutE k) = carWords l F kclk coef A a ha r k) ∧
      τ.st (oS sIN) = frame (fpIn l F kclk coef A a ha r) ∧
      (∀ i, i ≠ oS sIN → (∀ k, i ≠ sOutE k) →
        ∃ ℓ ≤ CsOf DtC * ((fpIn l F kclk coef A a ha r).length + 1) ^ (2 * DtC), τ.st i = List.replicate ℓ false) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  -- the call's fields
  obtain ⟨_, hcar, _, hcount, _, _, _⟩ := r.2
  have hk : r.1.carriers.length ≤ 2 := hcount
  have henv : ∀ X ∈ r.1.carriers, X.WithinEnvelope 26 := hcar
  have ha4 : (PrimAsm.Codec.codeList r.1).length ≤ 4 := by rw [PrimAsm.Codec.codeList_length]; exact r.1.ha
  have hLX : ∀ X ∈ r.1.carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ Lof r.1.n := by
    intro X hX g hg
    have := (henv X hX).2 g hg
    unfold Lof; omega
  -- the input is PA's request word (ReqBridge)
  obtain ⟨tl, hw⟩ : ∃ tl, reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl = fpIn l F kclk coef A a ha r :=
    ⟨_, PrimAsm.ReqBridge.reqW_word r.1 _⟩
  have hnN : r.1.n ≤ (reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl).length := by rw [hw]; exact FpInLen.n_le_fpIn r
  rw [← hw] at hin ⊢
  obtain ⟨hxN, hyN⟩ := S5T.natWord_le_reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
    (r.1.carriers.map Stars.Carrier.code) tl
  -- the bound `T` and the capacities
  obtain ⟨hT1, hT2⟩ := T_bounds _ r.1.n (PrimAsm.Codec.codeList r.1) r.1.carriers hnN ha4 hk hxN hyN
  obtain ⟨hc1, hc2, hNc⟩ := caps DtC _ r.1.n (PrimAsm.Codec.codeList r.1) r.1.carriers hT1 hT2
  have hTc := T_le_cap DtC (reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl).length
  -- the pipeline
  obtain ⟨τ, m, hm, hstep, h5, h3, h6, hkeep, hres, hτs, hτv, -⟩ :=
    carPipe DtC keepL (by simp [keepL]) (by simp [keepL]) r.1.n (PrimAsm.Codec.modeBit r.1.mode)
      (PrimAsm.Codec.codeList r.1) r.1.carriers tl ha4 hk hLX σ hin hbl hsh hv hc _ hnN hxN hyN hT1 hT2
      (hc1.trans hTc) (hc2.trans hTc) hTc (hNc.trans hTc)
  refine ⟨τ, m, le_trans hm (pipe_le DtC _ r.1.n one_le_DtC _ _ hT1 hT2), hstep, ?_, hkeep.trans hin,
    fun i h1 h2 => ⟨_, T_le_Cs DtC _, hres i ?_⟩, hτs, hτv⟩
  · intro k
    match k with
    | ⟨0, _⟩ => exact h3 0 (by simp [keepL])
    | ⟨1, _⟩ => exact h3 1 (by simp [keepL])
    | ⟨2, _⟩ => exact h5 0 (by simp [keepL])
    | ⟨3, _⟩ => exact h5 1 (by simp [keepL])
    | ⟨4, _⟩ => exact h6
  · by_cases hi : i.val < DS + 1
    · exact Or.inl (mem_keep i hi h1 h2)
    · right
      apply Fin.ext
      have := i.isLt
      have hNS : NS = DS + 1 := rfl
      show i.val = DS + 1
      omega

/-- **The carrier phase** at the zero-residue writer contract: one machine for every gate. -/
noncomputable def carPhase (l : Literals) : CarPhaseM l where
  ns := NS
  nr := NR
  s := fun _ => carMach.1
  M := fun _ => carMach.2
  sIn := oS sIN
  sOut := sOutE
  out_ne := sOutE_ne
  Kc := fun _ => 2 ^ DtC
  Dk := fun _ => DtC
  Cs := fun _ => CsOf DtC
  Ds := fun _ => 2 * DtC
  run := fun F kclk coef A a ha r σ hin hsh hbl hv hc => carRun l F kclk coef A a ha r σ hin hsh hbl hv hc

/-- **The carrier phase at the bounded-residue contract**: the form SA's and SB's writers dock. -/
abbrev CarPhaseMJ (l : Literals) : Type := Finish.CoreWordsMJ l 5 (carWords l)

/-- **The carrier phase, bounded residues** (zero residues are residues, the `toMJ`). -/
noncomputable def carPhaseJ (l : Literals) : CarPhaseMJ l := Finish.CoreWordsM.toMJ (carPhase l)

end NearCubicWires.WireExponent3_5.FinalPass.Out.CarGen

end
