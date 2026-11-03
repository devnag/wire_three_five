import Proof.Wire_3_5.Primitive.Writers.ShellERun
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base

/-! # gate 1: the THR/HASH writer shell over `ThrDataStage4` — machines and the run's statement

v4's numbers machine `S.M3` runs on `DS + 2 + DR + 1 + x3` tapes (v3's tapes, then `x3` extra scratch tapes, blank at the
start, their final contents `J` bounded by `cost3`). The v4 shell is v3's (`ShellH`) on `STx + x3` tapes: every v3 stage
is embedded (`TapeEmbedding.machine x3`, the extra tapes untouched), v3's pre-phase without its data stage (`preM7`) runs
under `pX`, v3's boot after the pre-phase is one embedded block (`bootRest`), and the data stage docks at v3's slots through `pX` plus the `x3` extra tapes (`dataSlotsX4`); the extra
tapes' final contents are residues of the writer's run (`WriterIfaceJ.WriterRun`, bounded by the budget).

* `preM7`, `dataSlotsX4`, `MX0TH4`, `bootRest`, `bootXMGH4`, **`shellMGH4`**, `shellInX4`, `shellOutX4`,
  `shellInX4_ne_out`;
* **`ShellRunH4`**: the statement of the v4 shell's run (`shell_runH`'s hypotheses verbatim, `S : ThrDataStage4`).

Paper quantity of the main type: the THR call's slice lengths and THR numbers on the writer's data tape
(lem:primitive P3:3068-3084; filt:soft P3:2220-2231), within the writer's budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.SupplierPipeline

section Machines4
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}

/-- The boot and stages 6, 7 (v3's `preMTH` without its data stage). -/
noncomputable def preM7 (x D D1 D2 C1 C2 : ℕ) :=
  Composition.machine (Composition.machine (bootM x D D1 D2 C1) (M6 x D D1 D2 C2)) (M7 x D D1 D2)

/-- **The v4 data stage's slots**: v3's `dataSlots` through `pX`, then the `x3` extra tapes after the shell's. -/
def dataSlotsX4 (x D D2 Dv DL x3 : ℕ) : Fin (E3 + x3) → Fin (STx x D D2 Dv DL + x3) :=
  Fin.addCases (fun j => Fin.castAdd x3 (pX (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) (dataSlots x D 0 D2 j)))
    (fun j => Fin.natAdd (STx x D D2 Dv DL) j)

/-- The v4 pre-phase on the shell's tapes: v3's pre-phase without the data stage (embedded), then the v4 data stage. -/
noncomputable def MX0TH4 (S : ThrData.ThrDataStage4 alg Dexp capT) (x D D2 Dv DL C2 : ℕ) :=
  Composition.machine
    (TapeEmbedding.machine S.x3 (RecoveryFocus.machine (pX (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL))
      (preM7 x D 0 D2 0 C2)))
    (RecoveryFocus.machine (dataSlotsX4 x D D2 Dv DL S.x3) S.M3)

/-- v3's boot after its pre-phase (`bootXMGH`'s stages `MX1 … act6`, on the shell's tapes). -/
noncomputable def bootRest (x D D2 Dv DL Cv CL : ℕ) {s2 : ℕ} (M2 : Machine NUn s2) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (MX1 x D D2 Dv DL Cv) (RecoveryFocus.machine (q2 x D D2 Dv DL) M2)) (MX3 x D D2 Dv DL)) (MX4 x D D2 Dv DL CL))
    (MX5 x D D2 Dv DL)) (act6 x D D2 Dv DL).compile

/-- **The v4 boot with any dimension stage**: the v4 pre-phase, then v3's `bootRest` embedded. -/
noncomputable def bootXMGH4 (S : ThrData.ThrDataStage4 alg Dexp capT) (x D D2 Dv DL C2 Cv CL : ℕ) {s2 : ℕ}
    (M2 : Machine NUn s2) :=
  Composition.machine (MX0TH4 S x D D2 Dv DL C2) (TapeEmbedding.machine S.x3 (bootRest x D D2 Dv DL Cv CL M2))

/-- **The v4 THR/HASH shell** (`shellMGH` over `ThrDataStage4`, on `STx + x3 + 1` tapes). -/
noncomputable def shellMGH4 (S : ThrData.ThrDataStage4 alg Dexp capT) (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU)
    (D C D2 C2 Dv Cv DL CL : ℕ) {s2 : ℕ} (M2 : Machine NUn s2) :=
  MaskedReset.machine (Composition.machine (Composition.machine (bootXMGH4 S x D D2 Dv DL C2 Cv CL M2)
    (TapeEmbedding.machine S.x3 (entryEX x D D2 Dv DL C)))
    (TapeEmbedding.machine S.x3 (PrimThrW.Shell.loopEU x U D D2 Dv DL))) (fun _ => true)

end Machines4

/-- The v4 shell's input port. -/
def shellInX4 (x D D2 Dv DL x3 : ℕ) : Fin (STx x D D2 Dv DL + x3 + 1) :=
  Fin.castAdd 1 (Fin.castAdd x3 (T0 x D D2 Dv DL))

/-- The v4 shell's output port. -/
def shellOutX4 (x D D2 Dv DL x3 : ℕ) : Fin (STx x D D2 Dv DL + x3 + 1) :=
  Fin.castAdd 1 (Fin.castAdd x3 (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)))

theorem shellInX4_ne_out (x D D2 Dv DL x3 : ℕ) : shellInX4 x D D2 Dv DL x3 ≠ shellOutX4 x D D2 Dv DL x3 := by
  intro h
  have := congrArg Fin.val h
  simp only [shellInX4, shellOutX4, Fin.val_castAdd, T0_val, lo_val, cs1_val] at this
  omega

/-- **The v4 shell's run** (statement): `shell_runH`'s hypotheses verbatim over a `ThrDataStage4`; the extra tapes'
contents are residues of the writer's run. -/
def ShellRunH4 : Prop :=
  ∀ {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
    (S : ThrData.ThrDataStage4 alg Dexp capT) (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU)
    (D C D2 C2 Dv Cv DL CL : ℕ) {s2 : ℕ} (M2 : Machine NUn s2) (c2 mD cap nU Bud : ℕ) (P : Shared.StarParams) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Stars.Carrier P.n))
    (tl w : List Bool) (emit : ℕ → List Bool),
    w = Data.reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl →
    PrimThrW.ShellE.ThrDataOK2 Cs carriers (UnaryCalc.value D2 C2 P.n) →
    2 * (Data.unaryList (ThrData.hashNums P Cs carriers alg Dexp (capT P.n) ++ ThrData.thrCounts Cs carriers)).length + 2 ≤
      2 * UnaryCalc.value D2 C2 P.n + 2 →
    (∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) →
    S.need P.n ≤ 2 * UnaryCalc.value D2 C2 P.n + 2 →
    DimOK x D D2 Dv DL M2 c2 mD w (UnaryCalc.value Dv Cv P.n) →
    cap + 1 ≤ UnaryCalc.value D C (2 ^ mD) → nU + 1 ≤ UnaryCalc.value D C (2 ^ mD) →
    bootCost w P.n 0 0 ≤ UnaryCalc.value D C (2 ^ mD) →
    (∀ j < UnaryCalc.value DL CL (2 ^ mD), ∀ out : List Bool,
      PrimThrW.Shell.UnitOK cap x U nU w
        (Data.unaryList (ThrData.hashNums P Cs carriers alg Dexp (capT P.n) ++ ThrData.thrCounts Cs carriers)) emit j out) →
    2 * shellCostG w P.n D C D2 C2 (S.cost3 a' Cs carriers (UnaryCalc.value D2 C2 P.n) (UnaryCalc.value D2 C2 P.n))
      Dv Cv c2 mD DL CL nU + 2 ≤ Bud →
    WriterIfaceJ.WriterRun (shellMGH4 S x U D C D2 C2 Dv Cv DL CL M2) Bud (shellInX4 x D D2 Dv DL S.x3)
      (shellOutX4 x D D2 Dv DL S.x3) w ((List.range (UnaryCalc.value DL CL (2 ^ mD))).flatMap emit ++ [false])

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
