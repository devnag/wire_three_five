import Setup.PhaseA
import CheckedPCPP.Composite
import CheckedPCPP.Harness
import CheckedPCPP.WMXReady
import Codec.Unframe
import OuterM.Spec
import Proof.CaseAnalysis.WitnessOracleRun

/-!
# W3c ((a′) form): the layout of the set-up's donor block

The near-cubic-gates paper's fixed weak machine (sec:gadget-transfer): the weak machine rejects unless `N = 2^ν`, computes the native width `q(N)`, reads
the guessed pair `B = (B_src, B_pf)` (proof 1's cold decoder, once per circuit), runs the guarded length walk and the
imported constructor on `⟨B_src⟩_ν` (A-run), and checks `B_src(bin_ν(i)0^{q−ν}) = z_i` (eq:source-check,
`checkW`). The donor block `aB` of `Setup.SetupData` (`tA` tapes, `Setup/Entry.lean`) is laid out as:

* `0` the set-up's flag `FL` (`SetupData.flag`), `1` the stream `NU = 1^ν` (the A-run's port `nIn`), `2 P`, `3 VV`,
  `4 TT` (CHECK's point, value and table streams);
* the width donors (`OuterM.WidthDonor`), twice each: `W1` (binary), `U1` (unary), `W2`, `U2`;
* proof 1's cold decoder twice, `O1` (field of `B_src`) and `O2` (field of `B_pf`), their tapes `2`, `3` ON the outputs
  of `W1`, `U1` (resp. `W2`, `U2`);
* the A-run (`OuterM.ARun`), its port `dIn` ON `O1`'s descriptor slot, `nIn` ON `NU`.

The composite (`D.cf`, block `kB`) docks its port `cIn` on the A-run's port `wOut` and `dIn` on `O2`'s descriptor slot.
Stream indices are computed modulo the stream count (total definitions); `Lay D W R` (`D.tA` is this layout's size,
the flag is slot `0`) makes them the intended streams.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Joins

/-! ## Registers of the guard phases (`110 … 127`; the term loop's, phase A's and phase D's are below `110`) -/

abbrev rNu : Fin nrW := 110
abbrev rBs : Fin nrW := 111
abbrev pT1 : Fin nrW := 112
abbrev pT2 : Fin nrW := 113
abbrev pT3 : Fin nrW := 114
abbrev pH : Fin nrW := 115
abbrev pB : Fin nrW := 116
abbrev pF : Fin nrW := 117
abbrev pU : Fin nrW := 118
abbrev pK : Fin nrW := 119
abbrev pT : Fin nrW := 120
abbrev pX1 : Fin nrW := 121
abbrev pX2 : Fin nrW := 122
abbrev pX3 : Fin nrW := 123

/-- Register-file case analysis (`split_ifs` on `Function.update_apply`): substitute the register variable, unfold the
named registers to literals (so clashes of distinct registers simplify to `False`), close by `rfl`/`omega`/`simp_all`. -/
macro "wregs" : tactic => `(tactic| (split_ifs <;> (try subst_vars) <;>
  (try simp only [rN, rM, rRB, rCL, rSC, rA, rLC, rPB, gN0, gU, gK, gT, gF, kQ, dS, hH, hBr, oW, bR, tW, rNu, rBs, pT1,
    pT2, pT3, pH, pB, pF, pU, pK, pT, pX1, pX2, pX3] at *) <;> (first
  | rfl
  | omega
  | (simp_all; done))))

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

section Sizes



end Sizes

section Streams
variable (D : SetupData s P g)

@[simp] theorem sX_val : (sX D).val = 0 := rfl
@[simp] theorem sBW_val : (sBW D).val = 1 := rfl
@[simp] theorem sWT_val : (sWT D).val = 2 := rfl
@[simp] theorem sCW_val : (sCW D).val = 3 := rfl
@[simp] theorem sVI_val : (sVI D).val = 4 := rfl
@[simp] theorem sS1_val : (sS1 D).val = 5 := rfl
@[simp] theorem sS2_val : (sS2 D).val = 6 := rfl
@[simp] theorem sTL_val : (sTL D).val = 7 := rfl
@[simp] theorem sG_val : (sG D).val = 8 := rfl
@[simp] theorem sL_val : (sL D).val = 9 := rfl
@[simp] theorem kB_val (j : Fin D.cf.t) : (kB D j).val = 16 + D.tA + j.val := rfl
@[simp] theorem cB_val (j : Fin D.tc) : (cB D j).val = 16 + D.tA + D.cf.t + j.val := rfl


end Streams

section Maps




end Maps

/-- A register write elsewhere does not change a register. -/
theorem upd_ne {ns nr : ℕ} (σ : WireExponent3_5.FinalPass.Tm.WState ns nr) {a r : Fin nr} (x : ℕ) (h : r ≠ a) : (σ.setv a x).val r = σ.val r := by
  simp [Function.update_of_ne h]

/-! ## Values of the stream indices under the layout -/

section Vals








end Vals

end

end NearCubicGates.Close.Setup
