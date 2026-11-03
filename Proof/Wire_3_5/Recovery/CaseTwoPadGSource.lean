import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyActual
import Proof.Wire_3_5.Recovery.CaseTwoPad
import Proof.Wire_3_5.FinalPass.WordAux
import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Proof.Wire_3_5.Assembly.FreeBase
import Proof.Wire_3_5.Recovery.CaseTwoPadSource
import Proof.CaseAnalysis.CaseTwoCompoundInput
import Proof.Amplification.RecoveryScratchErase
import Proof.Foundations.OrdinaryRewind

/-! # The padded source at a guessed width-`q` oracle (P3:3637-3644, 3669-3671, G3)

Realizes "the union machine [...] checks the PCPP of the substituted circuit of the guessed oracle" (P3:3669-3671) for
the verifier padded "to the exact width `q(N)`" (P3:3637-3644), on the raw description of a guessed oracle `O` of the
padded width `q`. From the framed hierarchy word, the raw description of `O`, `1^q` and a unary capacity `1^cap`, one
machine
1. frames the hierarchy word with an empty oracle field (base `CompoundInput`) and runs base's hierarchy stage
   (`PCPPNativeHierarchy.machine`, rewound), which writes the native width `R` as `frame (R.bits)`;
2. blanks the registers of the restriction program to `regTape (cap - 1) 0` (base `RecoveryScratchErase` from
   `1^cap`) and writes its result cell;
3. runs the restriction program (`restrictM`, rewound), which writes `frame (PCPPNative.descriptor (restrictHigh R O))`;
4. frames the hierarchy word with that description (base `CompoundInput`);
5. runs the padded source (`CaseTwoPadSource.omachine`) at the oracle `restrictHigh R O`.
The request it serves is `PCPPRequestBoundary.request a (padSubstituted … O)` (G1), the union setup's padded request
of `O` (`unionRequest_padG`, G2).

Donors checked: base `CompoundInput.pair_ready`, `PCPPNativeHierarchy.raw_run`, `Rewind.reset_run`,
`RecoveryScratchErase.erase_ready`, `ClockJoin.ReadyRun.focus` / `ClockJoin.join`, `TapeEmbedding.run_embed` (used);
C5's `WExec.exec` / `Exec.step` (used); C6's `FrontKit.cell_ready` / `ready_of_step` (same statements, restated here:
not in a verified list).

Paper quantity of the main type (`osourceG_run`): the PCPP clause data of the padded request of a guessed oracle. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.FinalPass.Tm

noncomputable section

/-! ## Generic composition steps -/

theorem inst_miss {t u : ℕ} {slot : Fin t → Fin u} {A : Fin u → List Bool} {out : Fin t → List Bool} {i : Fin u}
    (h : ∀ j, (slot j).val ≠ i.val) : RecoveryRootRound.install slot A out i = A i :=
  RecoveryRootRound.install_other _ _ _ _ (fun j he => h j (congrArg Fin.val he))

theorem inst_hit {t u : ℕ} {slot : Fin t → Fin u} (hs : Function.Injective slot) {A : Fin u → List Bool}
    {out : Fin t → List Bool} (j : Fin t) {i : Fin u} (h : (slot j).val = i.val) :
    RecoveryRootRound.install slot A out i = out j := by
  rw [← Fin.ext h]
  exact RecoveryRootRound.install_slot _ hs _ _ _

/-! ## The stages -/

/-! ## The layout -/

section Layout
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

/-- The tapes added beside the padded source. -/
def xtapes (k : ℕ) := PCPPNativeHierarchy.tapes source k + 33
abbrev gtapes (a : PointwisePCPPAlgorithm) (k : ℕ) := CaseTwoPadSource.otapes source a k + xtapes source k

/-- The hierarchy stage's width tape. -/
def widx (k : ℕ) : Fin (PCPPNativeHierarchy.tapes source k + 1) :=
  (PCPPNativeHierarchy.hierarchySlots source k (HierarchyStreams.old source k (HierarchyStreams.bitsR source k))).castAdd 1

/-! Added tapes (offsets past the block): `0` framed hierarchy word, `1` raw oracle description, `2` `1^cap`,
`3` empty-oracle frame cell, `4-6` first framing scratch, `7` result cell, `8` restricted description,
`9-26` registers, `27` rewind tape, `28` erase tape, `29-31` second framing scratch, `32-` hierarchy stage. -/

def sl1 (a : PointwisePCPPAlgorithm) (k : ℕ) (_ : Fin 1) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + 3, by simp only [gtapes, xtapes]; omega⟩
def sl2 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin 6) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k +
      (if j.val = 0 then 0 else if j.val = 1 then 3 else if j.val = 2 then 32 else j.val + 1),
    by have := j.isLt; simp only [gtapes, xtapes]; split_ifs <;> omega⟩
def sl3 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (PCPPNativeHierarchy.tapes source k + 1)) :
    Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + 32 + j.val, by have := j.isLt; simp only [gtapes, xtapes]; omega⟩
def sl4 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (18 + 1 + 1)) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + (if j.val < 18 then 9 + j.val else if j.val = 18 then 2 else 28),
    by have := j.isLt; simp only [gtapes, xtapes]; split_ifs <;> omega⟩
def sl5 (a : PointwisePCPPAlgorithm) (k : ℕ) (_ : Fin 1) : Fin (gtapes source a k) :=
  ⟨CaseTwoPadSource.otapes source a k + 7, by simp only [gtapes, xtapes]; omega⟩
def sl6 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin (2 + 2 + 18 + 1)) : Fin (gtapes source a k) :=
  ⟨if j.val = 0 then CaseTwoPadSource.otapes source a k + 32 + (widx source k).val
    else CaseTwoPadSource.otapes source a k + (if j.val = 1 then 7 else if j.val = 2 then 1 else if j.val = 3 then 8
      else if j.val < 22 then j.val + 5 else 27),
    by have := j.isLt; have := (widx source k).isLt; simp only [gtapes, xtapes]; split_ifs <;> omega⟩
def sl7 (a : PointwisePCPPAlgorithm) (k : ℕ) (j : Fin 6) : Fin (gtapes source a k) :=
  ⟨if j.val = 2 then 0 else CaseTwoPadSource.otapes source a k +
      (if j.val = 0 then 0 else if j.val = 1 then 8 else j.val + 26),
    by have := j.isLt; simp only [gtapes, xtapes]; split_ifs <;> omega⟩


/-! ## The machine -/



/-! ## The ambient tapes after each stage -/

/-- Closes a tape-index (in)equality of the layout. -/
local macro "vtac" : tactic => `(tactic| ((try simp only [sl1, sl2, sl3, sl4, sl5, sl6, sl7, Fin.val_mk,
  Fin.val_castAdd, ↓reduceIte, ite_true, ite_false, Nat.reduceEqDiff]) <;> (try split_ifs) <;>
  first | omega | contradiction))
/-- Passes an ambient tape through a stage that does not touch it. -/
local macro "down " h:ident : tactic => `(tactic| (rw [$h:ident, inst_miss] <;>
  first | (intro j'; have := j'.isLt; vtac) | skip))
/-- Reads an ambient tape written by a stage. -/
local macro "hitst " h:ident ", " s:term ", " j:term : tactic => `(tactic| (rw [$h:ident, inst_hit $s $j] <;>
  first | vtac | skip))

section Ambient


end Ambient

/-! ## The run -/

end Layout

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
