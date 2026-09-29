import Proof.Wire_3_5.Primitive.SeedFix.C4Loop
import Proof.Wire_3_5.Primitive.SeedFix.C4SI
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes

/-! # C4 Stage3 wrapper, the contract: a setup's exit bank, the decision loop, the finisher

"The processor writes the pool, the enumeration's rulers and constants, and the compiler request's numbers before the
loop" (P3:3011-3016); "For each candidate child prefix [...] sum the recovered integers. Choose a child with no larger
sum. After `S` decisions the actual trace objective is no larger than its random expectation" (P3:3034-3039); "The
sample positions are `S_j = π(f(λ_j))`" (P3:2932-2937). A C4 stage (`SeedFixTypes.Stage3`) of every mode is three
phases on the stage's `3 + x` tapes: a SETUP machine from `stageIn x w v`; the decision LOOP of a child family
(`C4Loop.ChildFam.loop_run`, docked by the M58 kit's `C4Set.slx`, its counter head moved to `1` and back); a FINISHER
docked by `C4Set.stageP` onto port `2`.

This file fixes the contract between the setup's producer (each mode) and the wrapper:
* `loopBank F R L j` (the loop's bank before decision `j`), `pfxL F`, `cntL F` (its prefix and counter tapes),
  `loopM F`, `hAt g`, `cfwdP g`, `cbwdP g`, **`loopZM F off hoff ext`** (counter head to `1`, the docked loop, the
  counter head to `0`), `loopZCost`;
* **`LoopEntry`**: the setup's exit bank carries the loop's entry at `slx off hoff ext` and the ports
  `frame w`, `v`, `[]`;
* `postLoop` (the bank after the loop: the prefix slot holds `frame (greedyLoop bound Rv)`, every other tape as
  before);
* **`FinDock`**: the finisher's inputs below its region `off₂` (never ports `0`, `1`), its output tape onto port `2`,
  the bank blank from `off₂` up;
* **`wrapM`**: the stage's machine `setup ; loopZM ; finisher (docked)`.

Paper quantities of the main types: the loop's entry `loopBank` (the child family's kept words, the empty prefix)
and the fixed prefix `frame (greedyLoop bound Rv)` the finisher reads. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Wrap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Set (slx)

section Loop
variable (F : C4Loop.ChildFam)

/-- **The loop's bank before decision `j`**: the child family's scrubbed bank (the prefix `gp j`, the kept words,
`R` falses on the scratch, the log `L` falses, the driver `1^R`) and the counter `word bound`. -/
def loopBank (R L j : ℕ) : Fin (F.T + 1 + 1 + 1) → List Bool :=
  Fin.addCases (Scrub.bank (F.src R j) R L) (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word F.bound)

/-- The loop's prefix tape. -/
def pfxL : Fin (F.T + 1 + 1 + 1) := Fin.castAdd 1 (Scrub.inner (F.sl0 F.PFX))

/-- The loop's counter tape. -/
def cntL : Fin (F.T + 1 + 1 + 1) := Fin.last (F.T + 1 + 1)

/-- The loop's machine (`loop_run`'s, with its body). -/
noncomputable def loopM := CloseoutRowsDegreeLoop.machine (Scrub.machine F.cellM (fun _ => true) F.cellS)

/-- The loop's step bound (`loop_run`'s). -/
def loopCost (R : ℕ) : ℕ := F.bound * (2 * F.cellCost + 2 + 1 + (2 * R + 4) + 3) + 3

end Loop

/-- The heads with tape `g` at `1`. -/
def hAt {u : ℕ} (g : Fin u) : Fin u → ℕ := fun i => if i = g then 1 else 0

/-- The counter head to `1`. -/
def cfwdP {u : ℕ} (g : Fin u) : Prog u := .act (fun _ => none) (moveAt g .right)

/-- The counter head back to `0`. -/
def cbwdP {u : ℕ} (g : Fin u) : Prog u := .act (fun _ => none) (moveAt g .left)

/-- **The docked loop**: the counter head to `1`, the loop at the slots `slx off hoff ext`, the counter head to `0`. -/
noncomputable def loopZM (F : C4Loop.ChildFam) {u : ℕ} (off : ℕ) (hoff : off + (F.T + 1 + 1 + 1) ≤ u)
    (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin u)) :=
  Composition.machine (cfwdP (slx off hoff ext (cntL F))).compile
    (Composition.machine (RecoveryFocus.machine (slx off hoff ext) (loopM F))
      (cbwdP (slx off hoff ext (cntL F))).compile)

/-- The docked loop's step bound. -/
def loopZCost (F : C4Loop.ChildFam) (R : ℕ) : ℕ := 1 + 1 + (loopCost F R + 1 + 1)

/-- **The loop's entry, left by a setup** on the stage's `3 + x` tapes: the loop's tapes docked by
`slx off hoff ext` (its kept tapes, log, driver and counter onto the setup's tapes below `off`, the rest onto the loop
region from `off`) carry `loopBank F R L 0`; the ports hold `frame w`, `v`, `[]`; no slot is port `0` or `2`, the
prefix slot is not port `1`; the scrub's pad `R` covers a decision and the log `L` the pad. -/
structure LoopEntry {x : ℕ} (F : C4Loop.ChildFam) (R L off : ℕ) (hoff : off + (F.T + 1 + 1 + 1) ≤ 3 + x)
    (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin (3 + x))) (w v : List Bool) (B : Fin (3 + x) → List Bool) : Prop where
  hR : F.cellCost + 1 ≤ R
  hL : R + 1 ≤ L
  h3 : 3 ≤ off
  inj : ∀ i j g, ext i = some g → ext j = some g → i = j
  lt : ∀ i g, ext i = some g → g.val < off
  port : ∀ i g, ext i = some g → g.val ≠ 0 ∧ g.val ≠ 2
  pfx : ∀ g, ext (pfxL F) = some g → g.val ≠ 1
  entry : ∀ j, B (slx off hoff ext j) = loopBank F R L 0 j
  p0 : B ⟨0, by omega⟩ = frame w
  p1 : B ⟨1, by omega⟩ = v
  p2 : B ⟨2, by omega⟩ = []

/-- **The bank after the loop**: the prefix slot holds the greedy's decisions, every other tape as before. -/
def postLoop {u : ℕ} (F : C4Loop.ChildFam) (off : ℕ) (hoff : off + (F.T + 1 + 1 + 1) ≤ u)
    (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin u)) (B : Fin u → List Bool) : Fin u → List Bool :=
  Function.update B (slx off hoff ext (pfxL F)) (frame (SeedFix.greedyLoop F.bound F.Rv))

/-- **The finisher's dock** at the bank `B` after the loop: its inputs `ext₂` below its region `off₂` (never port `0`
or `1`) carry `tin`, its output tape `o` sits on port `2`, its other tapes on the region (`tin` blank there), the bank
blank from `off₂` up. -/
structure FinDock {x t : ℕ} (off2 : ℕ) (hoff2 : off2 + t ≤ 3 + x) (ext2 : Fin t → Option (Fin (3 + x))) (o : Fin t)
    (tin : Fin t → List Bool) (B : Fin (3 + x) → List Bool) : Prop where
  inj : ∀ i j g, ext2 i = some g → ext2 j = some g → i = j
  lt : ∀ i g, ext2 i = some g → g.val < off2
  port : ∀ i g, ext2 i = some g → g.val ≠ 0 ∧ g.val ≠ 1
  out : ext2 o = some ⟨2, by omega⟩
  inp : ∀ j g, ext2 j = some g → B g = tin j
  own : ∀ j, ext2 j = none → tin j = []
  blank : ∀ i : Fin (3 + x), off2 ≤ i.val → B i = []

/-- **The stage's machine**: the setup, the docked loop, the docked finisher. -/
noncomputable def wrapM {x s0 tf sf : ℕ} (M0 : Machine (3 + x) s0) (F : C4Loop.ChildFam) (off : ℕ)
    (hoff : off + (F.T + 1 + 1 + 1) ≤ 3 + x) (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin (3 + x)))
    (Mf : Machine tf sf) (off2 : ℕ) (hoff2 : off2 + tf ≤ 3 + x) (ext2 : Fin tf → Option (Fin (3 + x))) :=
  Composition.machine M0 (Composition.machine (loopZM F off hoff ext) (RecoveryFocus.machine (slx off2 hoff2 ext2) Mf))

/-- The stage's step bound. -/
def wrapCost (c0 : ℕ) (F : C4Loop.ChildFam) (R nf : ℕ) : ℕ := c0 + 1 + (loopZCost F R + 1 + nf)

end NearCubicWires.WireExponent3_5.PrimT.C4Wrap
