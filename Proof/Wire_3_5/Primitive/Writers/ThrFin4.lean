import Proof.Wire_3_5.Primitive.Writers.ThrFin3
import Proof.Wire_3_5.Primitive.Writers.BigBank
import Proof.Wire_3_5.Primitive.SeedFix.C4SymWE

/-! # c4 THR block, the THR finisher: the sample expansion, then the hash bits

The THR stage's finisher `finM` on `34` tapes: C6's sample expansion (`UnionMachine.SampStage.sampM`, tapes `0 … 30`,
its output on tape `6`), then the frame append (`ThrFin.faM` on tapes `6`, `32`, `31`, `33`: the output, a blank tape, the
marked hash bits, the log). From the expansion's entry (`C4Iface.sampIn`) and `marks hbF` on tape `31`, tape `6` ends
with `sampleWord kh (seedPairs P s) ++ hbF` (**`finM_step`**). Docked on the big bank (**`thr_fin`**,
`C4Wrap.FinDock`): the expansion's inputs as `finExt` (lifted), the hash bits' tape below the finisher's region,
the output on port `2`.

Paper quantity of the main type: the THR seed word `sampleWord kh S ++ frame hb` (P3:2932-2937, 2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (FinDock postLoop pfxL)
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank

/-- The expansion's tapes. -/
def e31 (i : Fin 31) : Fin 34 := ⟨i.val, by have := i.isLt; omega⟩

theorem e31_inj : Function.Injective e31 := fun a b h => Fin.ext (by have h2 := congrArg Fin.val h; exact h2)

/-- The append's tapes: the output, a blank tape, the hash bits, the log. -/
def eA : Fin 4 → Fin 34 := ![6, 32, 31, 33]

theorem eA_inj : Function.Injective eA := by decide

/-- **The THR finisher.** -/
noncomputable def finM := Composition.machine (RecoveryFocus.machine e31 UnionMachine.SampStage.sampM)
  (RecoveryFocus.machine eA faM)

/-- The finisher's entry: the expansion's entry, the marked hash bits on tape `31`. -/
def tinF (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (hbF : List Bool) : Fin 34 → List Bool := fun j =>
  if h : j.val < 31 then C4Iface.sampIn (0 : Fin 31) 2 3 4 5 P s ⟨j.val, h⟩ else if j.val = 31 then marks hbF else []

/-- The finisher's step bound. -/
def finCost (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (hbF : List Bool) : ℕ :=
  C4Iface.sampCost P + 1 + (2 * faCost P.kh (C4Iface.seedPairs P s).length hbF.length + 2)

/-- **The THR finisher, run.** -/
theorem finM_step (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (hbF : List Bool) (hkh : 1 ≤ P.kh) :
    ∃ tout : Fin 34 → List Bool, Step finM (finCost P s hbF) (fun _ => 0) (tinF P s hbF) (fun _ => 0) tout ∧
      tout 6 = FinalPass.Sample.sampleWord P.kh (C4Iface.seedPairs P s) ++ hbF := by
  obtain ⟨A', hS, h6⟩ := UnionMachine.SampStage.samp_run P s
  have d1 := GeoFront.dockZ hS e31 e31_inj (fun _ => 0) (tinF P s hbF) (fun _ => rfl) (fun j => by
    unfold tinF e31; rw [dif_pos j.isLt])
  set B1 := install e31 (tinF P s hbF) A' with hB1
  obtain ⟨m, hF⟩ := fa_step P.kh hkh (C4Iface.seedPairs P s) hbF
  have n32 : ∀ j : Fin 31, e31 j ≠ 32 := fun j e => by have := congrArg Fin.val e; simp [e31] at this; omega
  have n31 : ∀ j : Fin 31, e31 j ≠ 31 := fun j e => by have := congrArg Fin.val e; simp [e31] at this; omega
  have n33 : ∀ j : Fin 31, e31 j ≠ 33 := fun j e => by have := congrArg Fin.val e; simp [e31] at this; omega
  have b6 : B1 6 = FinalPass.Sample.sampleWord P.kh (C4Iface.seedPairs P s) := by
    rw [hB1, show (6 : Fin 34) = e31 6 from rfl, install_slot _ e31_inj]; exact h6
  have b32 : B1 32 = [] := by rw [hB1, install_other _ _ _ _ n32]; rfl
  have b31 : B1 31 = marks hbF := by rw [hB1, install_other _ _ _ _ n31]; rfl
  have b33 : B1 33 = [] := by rw [hB1, install_other _ _ _ _ n33]; rfl
  have d2 := GeoFront.dockZ hF eA eA_inj (fun _ => 0) B1 (fun _ => rfl) (fun j => by
    fin_cases j
    · show B1 6 = _; rw [b6]; rfl
    · show B1 32 = _; rw [b32]; rfl
    · show B1 31 = _; rw [b31]; rfl
    · show B1 33 = _; rw [b33]; rfl)
  refine ⟨install eA B1 _, d1.seq d2, ?_⟩
  rw [show (6 : Fin 34) = eA 0 from rfl, install_slot _ eA_inj]
  rfl

/-! ## The finisher's dock on the big bank -/

variable (L : Lay) {x' : ℕ} (hx : 3 + L.X ≤ 3 + x')

/-- The finisher's slots on the big bank: the expansion's inputs as `finExt` (lifted), the hash bits' tape. -/
def extF (hbT : Fin (3 + x')) (j : Fin 34) : Option (Fin (3 + x')) :=
  if h : j.val < 31 then (C4SymW.finExt L ⟨j.val, h⟩).map (liftE hx) else if j.val = 31 then some hbT else none

/-- The loop's exit bank on the big bank is the first tapes' exit bank, lifted. -/
theorem postLoop_lift (F : C4Loop.ChildFam) (off : ℕ) (hoff : off + (F.T + 1 + 1 + 1) ≤ 3 + L.X)
    (hoff' : off + (F.T + 1 + 1 + 1) ≤ 3 + x') (ext : Fin (F.T + 1 + 1 + 1) → Option (Fin (3 + L.X)))
    (B : Fin (3 + L.X) → List Bool) (B' : Fin (3 + x') → List Bool) (hBB : ∀ i, B' (liftE hx i) = B i)
    (i : Fin (3 + L.X)) : postLoop F off hoff' (liftX hx ext) B' (liftE hx i) = postLoop F off hoff ext B i := by
  unfold postLoop
  rw [slx_lift hx off hoff hoff' ext]
  by_cases h : i = slx off hoff ext (pfxL F)
  · subst h; simp
  · rw [Function.update_of_ne (fun e => h (liftE_inj hx e)), Function.update_of_ne h, hBB]

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFin
