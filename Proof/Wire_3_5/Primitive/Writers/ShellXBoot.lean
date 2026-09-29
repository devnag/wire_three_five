import Proof.Wire_3_5.Primitive.Writers.ShellDRun
import Proof.Wire_3_5.Primitive.Writers.NumsX

/-! # PA (d), the writer shell dimensioned by `n' = 2^(2·kh + L)` (ShellX), part 1: the layout and the boot

P3:1188-1189 and P3:3823-3824: a SYM call's tape has `2^(2·kh)·poly(n)` units, `kh = s·r/2`, and each unit's records
carry labels up to `2^(2·kh)·poly(n)`; so the writer's scrub capacity and loop bound are dimensioned by
`n' = 2^(2·kh + L) ≥ 4^kh·(n+2)`, while the per-call data stage keeps the exact `n` (root's ShellX decision).

The layout is `STx = SD + (SD + ((E5 + NUMS) + CAPR) + E6)`: the M18 layout `SD = STd x D 0 D2` (the REAL loop
layout: cell, data tape, workspace, log, driver, counter), a second copy of it (the IMAGE, where the boot and data
phase leave their scratch), the fill-count run `E5` (`UnaryCalc.tapes Dv`), the dimension stage `NUMS`
(`NumsX.numsM`), base `CapReader` (`CAPR`, under a masked reset) and the loop bound's run `E6` (`UnaryCalc.tapes DL`).

The boot:
0. `ShellD.preM` docked with the cell and the data tape on the real layout, everything else on the image
   (`pre_step`: request kept, `OUT = [false]`, the data tape `dataWord (symCounts …)`, `1^n` on the image's calc input);
1. base `UnaryCalc.poly_step Dv Cv` on the image's `1^n`: the fill count `1^W`, `W = Cv(n+1)^Dv`;
2. `NumsX.numsM`: the source `srcWord m`, `m = 2·kh + L`;
3. base `CapReader.run` under C2's `maskBlank`: `1^(2^m)` on the REAL calc input and on `E6`'s input;
4. base `UnaryCalc.poly_step DL CL`: `1^b`, `b = CL(2^m+1)^DL`;
5. base `PacketsGlue.Stamp.run 0 b`: the REAL counter `word b`;
6. one action: the counter's head to `1`.

**`bootX_step`**: the boot as one `Step` from the writer's entry bank to the loop's entry data on the real layout
(workspace `Scrub.calcIn D (2^m)`), the image and the extension holding residues.

Paper quantity of the main type: the dimension `n' = 2^(2·kh + L)` (`kh = s·(r/2)` of star:partition, `L` of the
ledger) of the writer's scrub and loop. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires.SupplierPipeline

/-! ## The layout -/

/-- The M18 layout without a bound run of its own. -/
abbrev SD (x D D2 : ℕ) : ℕ := STd x D 0 D2
/-- The dimension stage's tapes (with its masked reset's log). -/
abbrev NUn : ℕ := NumsX.NS + 2 + NumsX.NR + 1
/-- The runs after the image. -/
abbrev EXr (Dv DL : ℕ) : ℕ := ((UnaryCalc.tapes Dv + NUn) + 12) + UnaryCalc.tapes DL
/-- The extension of the real layout. -/
abbrev EX (x D D2 Dv DL : ℕ) : ℕ := SD x D D2 + EXr Dv DL
/-- **ShellX's layout.** -/
abbrev STx (x D D2 Dv DL : ℕ) : ℕ := SD x D D2 + EX x D D2 Dv DL

section Tapes
variable {x D D2 Dv DL : ℕ}

def lo (i : Fin (SD x D D2)) : Fin (STx x D D2 Dv DL) := Fin.castAdd _ i
def im (i : Fin (SD x D D2)) : Fin (STx x D D2 Dv DL) := Fin.natAdd (SD x D D2) (Fin.castAdd (EXr Dv DL) i)
def e5 (k : Fin (UnaryCalc.tapes Dv)) : Fin (STx x D D2 Dv DL) :=
  Fin.natAdd (SD x D D2) (Fin.natAdd (SD x D D2)
    (Fin.castAdd (UnaryCalc.tapes DL) (Fin.castAdd 12 (Fin.castAdd NUn k))))
def nu (k : Fin NUn) : Fin (STx x D D2 Dv DL) :=
  Fin.natAdd (SD x D D2) (Fin.natAdd (SD x D D2)
    (Fin.castAdd (UnaryCalc.tapes DL) (Fin.castAdd 12 (Fin.natAdd (UnaryCalc.tapes Dv) k))))
def ca (k : Fin 12) : Fin (STx x D D2 Dv DL) :=
  Fin.natAdd (SD x D D2) (Fin.natAdd (SD x D D2) (Fin.castAdd (UnaryCalc.tapes DL) (Fin.natAdd (UnaryCalc.tapes Dv + NUn) k)))
def e6 (k : Fin (UnaryCalc.tapes DL)) : Fin (STx x D D2 Dv DL) :=
  Fin.natAdd (SD x D D2) (Fin.natAdd (SD x D D2) (Fin.natAdd ((UnaryCalc.tapes Dv + NUn) + 12) k))

theorem lo_val (i : Fin (SD x D D2)) : (lo (Dv := Dv) (DL := DL) i).val = i.val := rfl
theorem im_val (i : Fin (SD x D D2)) : (im (Dv := Dv) (DL := DL) i).val = SD x D D2 + i.val := rfl
theorem e5_val (k : Fin (UnaryCalc.tapes Dv)) :
    (e5 (x := x) (D := D) (D2 := D2) (DL := DL) k).val = SD x D D2 + (SD x D D2 + k.val) := rfl
theorem nu_val (k : Fin NUn) :
    (nu (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k).val =
      SD x D D2 + (SD x D D2 + (UnaryCalc.tapes Dv + k.val)) := rfl
theorem ca_val (k : Fin 12) :
    (ca (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k).val =
      SD x D D2 + (SD x D D2 + (UnaryCalc.tapes Dv + NUn + k.val)) := rfl
theorem e6_val (k : Fin (UnaryCalc.tapes DL)) :
    (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) k).val =
      SD x D D2 + (SD x D D2 + (UnaryCalc.tapes Dv + NUn + 12 + k.val)) := rfl

theorem lo_inj : Function.Injective (lo (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) := by
  intro a b h; exact Fin.ext (by simpa [lo_val] using congrArg Fin.val h)
theorem im_inj : Function.Injective (im (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) := by
  intro a b h; have := congrArg Fin.val h; rw [im_val, im_val] at this; exact Fin.ext (by omega)
theorem e5_inj : Function.Injective (e5 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) := by
  intro a b h; have := congrArg Fin.val h; rw [e5_val, e5_val] at this; exact Fin.ext (by omega)
theorem nu_inj : Function.Injective (nu (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) := by
  intro a b h; have := congrArg Fin.val h; rw [nu_val, nu_val] at this; exact Fin.ext (by omega)
theorem e6_inj : Function.Injective (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) := by
  intro a b h; have := congrArg Fin.val h; rw [e6_val, e6_val] at this; exact Fin.ext (by omega)

end Tapes

/-! ## Docking a zero-heads run -/

theorem dock0 {t u s n : ℕ} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (slots j) = 0) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A H (install slots A tout) := by
  have d := Rec.dockRun h slots hi H A hH hA
  exact d.congr (Shell.dockH_eq _ hi _ _ _ (fun j => hH j) (fun _ _ => rfl)) rfl

/-! ## Stage 0: the boot and data phase, the scratch on the image -/

section Stage0
variable {x D D2 Dv DL : ℕ}

/-- The pre-phase's tapes: the cell and the data tape on the real layout, every other tape on the image. -/
def pX (i : Fin (SD x D D2)) : Fin (STx x D D2 Dv DL) := if i.val < TT x + 1 then lo i else im i

theorem TT_lt_SD : TT x + 1 < SD x D D2 := by
  show TT x + 1 < TT x + 1 + Scrub.wk D + 1 + 1 + 1 + (E1 0 + E2 D2 + E3)
  omega

theorem pX_inj : Function.Injective (pX (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) := by
  have hT := TT_lt_SD (x := x) (D := D) (D2 := D2)
  intro a b h
  unfold pX at h
  split_ifs at h with ha hb hb
  · exact lo_inj h
  · exfalso; have := congrArg Fin.val h; rw [lo_val, im_val] at this; omega
  · exfalso; have := congrArg Fin.val h; rw [lo_val, im_val] at this; omega
  · exact im_inj h

theorem pX_lo (i : Fin (SD x D D2)) (h : i.val < TT x + 1) : pX (Dv := Dv) (DL := DL) i = lo i := by
  unfold pX; rw [if_pos h]

theorem pX_im (i : Fin (SD x D D2)) (h : TT x + 1 ≤ i.val) : pX (Dv := Dv) (DL := DL) i = im i := by
  unfold pX; rw [if_neg (by omega)]

/-- The pre-phase, docked. -/
noncomputable def MX0 (x D D2 Dv DL C2 : ℕ) :=
  RecoveryFocus.machine (pX (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) (preM x D 0 D2 0 C2)

/-- The writer's entry bank on ShellX's layout. -/
def A0 (w : List Bool) : Fin (STx x D D2 Dv DL) → List Bool := fun i => if i = lo (cs 0) then frame w else []

/-- The heads during the boot: the image counter's at `1`. -/
def HI : Fin (STx x D D2 Dv DL) → ℕ := fun i => if i = im (kT (x := x) (D := D) (D1 := 0) (D2 := D2)) then 1 else 0

theorem kT_ge : TT x + 1 ≤ (kT (x := x) (D := D) (D1 := 0) (D2 := D2)).val := by
  rw [kT_val]; omega

theorem cs0_lt : (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0).val < TT x + 1 := by
  have := cs_lt (x := x) (D := D) (D1 := 0) (D2 := D2) 0; omega

theorem x0_step {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (C2 : ℕ)
    (hw : w = Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : DataOK Cs carriers (UnaryCalc.value D2 C2 n)) :
    ∃ B8 : Fin (SD x D D2) → List Bool,
      Step (MX0 x D D2 Dv DL C2) (preCost w n 0 0 D2 C2
          (Data.coreCost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)))
        (fun _ => 0) (A0 w) HI (install pX (A0 w) B8) ∧
      B8 (cs 0) = frame w ∧ B8 (cs 1) = [false] ∧ B8 (cs 2) = [] ∧ (∀ j, B8 (wT j) = Scrub.calcIn D n j) ∧
      B8 dT = Data.dataWord (Data.symCounts a' Cs carriers) ∧
      (∀ c, kept x c = false → (B8 (cT c)).length ≤ bootCost w n 0 0) := by
  obtain ⟨B8, sp, h0, h1, h2, hwk, -, -, -, hdt, hs⟩ :=
    pre_step (x := x) (D := D) (D1 := 0) (D2 := D2) Cs carriers tl w 0 C2 hw hD
  have d := Rec.dockRun sp (pX (Dv := Dv) (DL := DL)) (pX_inj (Dv := Dv) (DL := DL)) (fun _ => 0) (A0 w)
    (fun _ => rfl) (by
    intro j
    by_cases hj : j = cs 0
    · subst hj
      rw [pX_lo _ cs0_lt]
      simp [A0, B0]
    · have hne : pX (Dv := Dv) (DL := DL) j ≠ lo (cs 0) := by
        intro e
        rw [← pX_lo (Dv := Dv) (DL := DL) _ cs0_lt] at e
        exact hj (pX_inj e)
      simp only [A0, B0, if_neg hne, if_neg hj])
  have hk := kT_ge (x := x) (D := D) (D2 := D2)
  refine ⟨B8, d.congr ?_ rfl, h0, h1, h2, hwk, hdt, hs⟩
  refine Shell.dockH_eq _ pX_inj _ _ _ ?_ ?_
  · intro j
    by_cases hj : j = kT
    · subst hj
      rw [pX_im _ hk, hK_kT]
      simp [HI]
    · have hne : pX (Dv := Dv) (DL := DL) j ≠ im kT := by
        intro e
        rw [← pX_im (Dv := Dv) (DL := DL) _ hk] at e
        exact hj (pX_inj e)
      rw [hK_ne _ hj]
      simp [HI, hne]
  · intro i hi
    have hne : i ≠ im kT := by
      intro e
      rw [e, ← pX_im (Dv := Dv) (DL := DL) _ hk] at hi
      exact hi _ rfl
    simp [HI, hne]

end Stage0

/-! ## Region bounds -/

section Bounds
variable {x D D2 Dv DL : ℕ}

theorem lo_lt (i : Fin (SD x D D2)) : (lo (Dv := Dv) (DL := DL) i).val < SD x D D2 := by rw [lo_val]; exact i.isLt
theorem im_ge (i : Fin (SD x D D2)) : SD x D D2 ≤ (im (Dv := Dv) (DL := DL) i).val := by rw [im_val]; omega
theorem im_lt (i : Fin (SD x D D2)) : (im (Dv := Dv) (DL := DL) i).val < SD x D D2 + SD x D D2 := by
  rw [im_val]; have := i.isLt; omega
theorem e5_ge (k : Fin (UnaryCalc.tapes Dv)) :
    SD x D D2 + SD x D D2 ≤ (e5 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k).val := by
  rw [e5_val]; omega
theorem nu_ge (k : Fin NUn) :
    SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv ≤ (nu (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k).val := by
  rw [nu_val]; omega
theorem ca_ge (k : Fin 12) :
    SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv + NUn ≤ (ca (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k).val := by
  rw [ca_val]; omega
theorem e6_ge (k : Fin (UnaryCalc.tapes DL)) :
    SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv + NUn + 12 ≤ (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k).val := by
  rw [e6_val]; omega

end Bounds

/-! ## Named tapes -/

section Named
variable (x D D2 Dv DL : ℕ)

/-- The real request. -/
def T0 : Fin (STx x D D2 Dv DL) := lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0)
/-- The image's calc input (`1^n`). -/
def TI : Fin (STx x D D2 Dv DL) := im (wT (x := x) (D1 := 0) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D)))
/-- The fill count (`E5`'s output). -/
def TW : Fin (STx x D D2 Dv DL) := e5 (x := x) (D := D) (D2 := D2) (DL := DL) (UnaryCalc.outputTape Dv)
/-- The real calc input. -/
def TC : Fin (STx x D D2 Dv DL) := lo (wT (x := x) (D1 := 0) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D)))
/-- The bound run's input and output. -/
def TE : Fin (STx x D D2 Dv DL) := e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (UnaryCalc.inputTape DL)
def TO : Fin (STx x D D2 Dv DL) := e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (UnaryCalc.outputTape DL)
/-- The real counter. -/
def TK : Fin (STx x D D2 Dv DL) := lo (kT (x := x) (D := D) (D1 := 0) (D2 := D2))
/-- The image's counter. -/
def TJ : Fin (STx x D D2 Dv DL) := im (kT (x := x) (D := D) (D1 := 0) (D2 := D2))

end Named

section NamedV
variable {x D D2 Dv DL : ℕ}

theorem T0_val : (T0 x D D2 Dv DL).val = 0 := rfl
theorem TC_val : (TC x D D2 Dv DL).val = TT x + 1 := rfl
theorem TK_val : (TK x D D2 Dv DL).val = TT x + 1 + Scrub.wk D + 2 := rfl
theorem TI_val : (TI x D D2 Dv DL).val = SD x D D2 + (TT x + 1) := rfl
theorem TJ_val : (TJ x D D2 Dv DL).val = SD x D D2 + (TT x + 1 + Scrub.wk D + 2) := rfl
theorem TW_val : (TW x D D2 Dv DL).val = SD x D D2 + (SD x D D2 + (3 + 2 * Dv)) := rfl
theorem TE_val : (TE x D D2 Dv DL).val = SD x D D2 + (SD x D D2 + (UnaryCalc.tapes Dv + NUn + 12 + 0)) := rfl
theorem TO_val : (TO x D D2 Dv DL).val = SD x D D2 + (SD x D D2 + (UnaryCalc.tapes Dv + NUn + 12 + (3 + 2 * DL))) := rfl

theorem SD_ge : TT x + 1 + Scrub.wk D + 3 ≤ SD x D D2 := by
  show TT x + 1 + Scrub.wk D + 3 ≤ TT x + 1 + Scrub.wk D + 1 + 1 + 1 + (E1 0 + E2 D2 + E3)
  omega

theorem HI_eq (i : Fin (STx x D D2 Dv DL)) : HI i = if i = TJ x D D2 Dv DL then 1 else 0 := rfl

end NamedV

/-! ## Stage 1: the fill count `1^W`, `W = Cv(n+1)^Dv` -/

section Stage1
variable {x D D2 Dv DL : ℕ}

/-- The fill-count run's tapes: its input on the image's calc input (`1^n`), the rest in `E5`. -/
def q1 (x D D2 Dv DL : ℕ) (k : Fin (UnaryCalc.tapes Dv)) : Fin (STx x D D2 Dv DL) :=
  if k = UnaryCalc.inputTape Dv then TI x D D2 Dv DL else e5 k

theorem q1_inj : Function.Injective (q1 x D D2 Dv DL) := by
  intro a b h
  unfold q1 at h
  have hI : (TI x D D2 Dv DL).val < SD x D D2 + SD x D D2 := by
    rw [TI_val]; have := TT_lt_SD (x := x) (D := D) (D2 := D2); omega
  split_ifs at h with ha hb hb
  · rw [ha, hb]
  · exfalso
    have h2 := e5_ge (x := x) (D := D) (D2 := D2) (DL := DL) b
    have hv := congrArg Fin.val h; omega
  · exfalso
    have h2 := e5_ge (x := x) (D := D) (D2 := D2) (DL := DL) a
    have hv := congrArg Fin.val h; omega
  · exact e5_inj h

noncomputable def MX1 (x D D2 Dv DL Cv : ℕ) :=
  RecoveryFocus.machine (q1 x D D2 Dv DL) (PCPSerializerCapacity.Power.machine Dv Cv)

theorem HI_ne (i : Fin (STx x D D2 Dv DL)) (h : i ≠ TJ x D D2 Dv DL) : HI i = 0 := by rw [HI_eq, if_neg h]

theorem ne_TJ (i : Fin (STx x D D2 Dv DL)) (h : i.val ≠ (TJ x D D2 Dv DL).val) : i ≠ TJ x D D2 Dv DL :=
  fun e => h (congrArg Fin.val e)

theorem x1_step (Cv n : ℕ) (B : Fin (STx x D D2 Dv DL) → List Bool)
    (hin : B (TI x D D2 Dv DL) = List.replicate n true) (hb : ∀ k, B (e5 k) = []) :
    ∃ out : Fin (UnaryCalc.tapes Dv) → List Bool,
      Step (MX1 x D D2 Dv DL Cv) (PCPSerializerCapacity.Power.budget Dv Cv n) HI B HI (install (q1 x D D2 Dv DL) B out) ∧
      out (UnaryCalc.outputTape Dv) = List.replicate (UnaryCalc.value Dv Cv n) true := by
  obtain ⟨out, h, -, ho⟩ := UnaryCalc.poly_step Dv Cv n
  have hJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hH : ∀ k, HI (q1 x D D2 Dv DL k) = 0 := by
    intro k
    apply HI_ne
    apply ne_TJ
    unfold q1
    split_ifs
    · rw [TI_val, hJ]; omega
    · have := e5_ge (x := x) (D := D) (D2 := D2) (DL := DL) k
      have := TT_lt_SD (x := x) (D := D) (D2 := D2)
      omega
  have hA : ∀ k, B (q1 x D D2 Dv DL k) = RepairSource.ProjectionNormalization.DimensionPolynomial.input Dv n k := by
    intro k
    unfold q1
    split_ifs with hk
    · rw [hin, hk]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape]
    · rw [hb k]
      have hv : k.val ≠ 0 := fun e => hk (Fin.ext e)
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hv]
  exact ⟨out, dock0 h (q1 x D D2 Dv DL) q1_inj HI B hH hA, ho⟩

end Stage1

/-! ## Stage 2: the dimension stage -/

section Stage2
variable {x D D2 Dv DL : ℕ}

/-- The dimension stage's request port. -/
def iN : Fin NUn := Fin.castAdd 1 (sTape (ns := NumsX.NS) (nr := NumsX.NR) NumsX.xIN)
/-- The dimension stage's fill-count port. -/
def cN : Fin NUn := Fin.castAdd 1 (sTape (ns := NumsX.NS) (nr := NumsX.NR) NumsX.xCT)
/-- The dimension stage's output. -/
def oN : Fin NUn := Fin.castAdd 1 (sTape (ns := NumsX.NS) (nr := NumsX.NR) NumsX.xOUT)

/-- The source's tape. -/
def TS (x D D2 Dv DL : ℕ) : Fin (STx x D D2 Dv DL) := nu oN

/-- The dimension stage's tapes: the request on the real request, the fill count on `E5`'s output, the rest in
`NUMS`. -/
def q2 (x D D2 Dv DL : ℕ) (j : Fin NUn) : Fin (STx x D D2 Dv DL) :=
  if j = iN then T0 x D D2 Dv DL else if j = cN then TW x D D2 Dv DL else nu j

theorem q2_cases (j : Fin NUn) :
    (j = iN ∧ q2 x D D2 Dv DL j = T0 x D D2 Dv DL) ∨ (j ≠ iN ∧ j = cN ∧ q2 x D D2 Dv DL j = TW x D D2 Dv DL) ∨
      (j ≠ iN ∧ j ≠ cN ∧ q2 x D D2 Dv DL j = nu j) := by
  unfold q2
  by_cases h1 : j = iN
  · exact Or.inl ⟨h1, if_pos h1⟩
  · by_cases h2 : j = cN
    · exact Or.inr (Or.inl ⟨h1, h2, by rw [if_neg h1, if_pos h2]⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, by rw [if_neg h1, if_neg h2]⟩)

theorem q2_inj : Function.Injective (q2 x D D2 Dv DL) := by
  have v0 := T0_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have vW := TW_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hW : 3 + 2 * Dv < UnaryCalc.tapes Dv := outTape_lt Dv
  intro a b h
  have na := nu_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) a
  have nb := nu_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) b
  rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) a with ⟨a1, ea⟩ | ⟨-, a2, ea⟩ | ⟨-, -, ea⟩ <;>
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) b with ⟨b1, eb⟩ | ⟨-, b2, eb⟩ | ⟨-, -, eb⟩ <;>
    rw [ea, eb] at h
  · rw [a1, b1]
  · exfalso; have hv := congrArg Fin.val h; omega
  · exfalso; have hv := congrArg Fin.val h; omega
  · exfalso; have hv := congrArg Fin.val h; omega
  · rw [a2, b2]
  · exfalso; have hv := congrArg Fin.val h; omega
  · exfalso; have hv := congrArg Fin.val h; omega
  · exfalso; have hv := congrArg Fin.val h; omega
  · exact nu_inj h

noncomputable def MX2 (x D D2 Dv DL cr : ℕ) := RecoveryFocus.machine (q2 x D D2 Dv DL) (NumsX.numsM cr)

theorem x2_step (cr W : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (sfx w : List Bool)
    (hw : w = RepairRepresentation.natWord P.n ++ sfx) (hW : 2 * P.n + cr + 16 ≤ W)
    (B : Fin (STx x D D2 Dv DL) → List Bool) (h0 : B (T0 x D D2 Dv DL) = frame w)
    (hct : B (TW x D D2 Dv DL) = List.replicate W true) (hb : ∀ k, B (nu k) = []) :
    ∃ tout : Fin NUn → List Bool,
      Step (MX2 x D D2 Dv DL cr) (2 * NumsX.numsStageCost P.n cr W + 2) HI B HI (install (q2 x D D2 Dv DL) B tout) ∧
      tout oN = NumsX.srcWord (NumsX.mOf P) ∧ tout iN = frame w := by
  obtain ⟨tout, m, h, o, i, -⟩ := NumsX.nums_step cr W P hrP sfx w hw hW
  have hJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hH : ∀ j, HI (q2 x D D2 Dv DL j) = 0 := by
    intro j
    apply HI_ne
    apply ne_TJ
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;>
      rw [e, hJ]
    · rw [T0_val]; omega
    · rw [TW_val]; omega
    · have := nu_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j; omega
  have hA : ∀ j, B (q2 x D D2 Dv DL j) =
      Fin.addCases (NumsX.rawInX w W) (fun _ : Fin 1 => List.replicate 0 false) j := by
    intro j
    rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;>
      rw [e]
    · subst h1
      rw [h0]
      simp [iN, NumsX.rawInX]
    · subst h2
      rw [hct]
      simp [cN, NumsX.rawInX, NumsX.xIN, NumsX.xCT, NumsX.sTape_eq_iffX]
    · rw [hb j]
      revert h1 h2
      refine Fin.addCases (fun t => ?_) (fun u => ?_) j
      · intro h1 h2
        have t1 : t ≠ sTape NumsX.xIN := fun e => h1 (by rw [e]; rfl)
        have t2 : t ≠ sTape NumsX.xCT := fun e => h2 (by rw [e]; rfl)
        simp [NumsX.rawInX, t1, t2]
      · intro _ _
        simp
  have d := dock0 h (q2 x D D2 Dv DL) q2_inj HI B hH hA
  refine ⟨_, d, ?_, ?_⟩
  · simp only [oN, Fin.addCases_left]
    exact o
  · simp only [iN, Fin.addCases_left]
    exact i

end Stage2

/-! ## Stage 3: `1^(2^m)` by base `CapReader` -/

section Stage3
variable {x D D2 Dv DL : ℕ}

/-- CapReader's tapes (with the masked reset's log): the source, its scratch in `CAPR`, the outputs `8` and `9` on the
real calc input and on the bound run's input. -/
def q3 (x D D2 Dv DL : ℕ) (j : Fin 12) : Fin (STx x D D2 Dv DL) :=
  if j = 0 then TS x D D2 Dv DL else if j = 8 then TC x D D2 Dv DL else if j = 9 then TE x D D2 Dv DL else ca j

theorem q3_cases (j : Fin 12) :
    (j = 0 ∧ q3 x D D2 Dv DL j = TS x D D2 Dv DL) ∨ (j = 8 ∧ q3 x D D2 Dv DL j = TC x D D2 Dv DL) ∨
      (j = 9 ∧ q3 x D D2 Dv DL j = TE x D D2 Dv DL) ∨ (j ≠ 0 ∧ j ≠ 8 ∧ j ≠ 9 ∧ q3 x D D2 Dv DL j = ca j) := by
  unfold q3
  by_cases h0 : j = 0
  · exact Or.inl ⟨h0, if_pos h0⟩
  · by_cases h8 : j = 8
    · exact Or.inr (Or.inl ⟨h8, by rw [if_neg h0, if_pos h8]⟩)
    · by_cases h9 : j = 9
      · exact Or.inr (Or.inr (Or.inl ⟨h9, by rw [if_neg h0, if_neg h8, if_pos h9]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h0, h8, h9, by rw [if_neg h0, if_neg h8, if_neg h9]⟩))

theorem TS_val : (TS x D D2 Dv DL).val = SD x D D2 + (SD x D D2 + (UnaryCalc.tapes Dv + 4)) := rfl

theorem q3_val (j : Fin 12) : (q3 x D D2 Dv DL j).val = TT x + 1 ∨
    SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv ≤ (q3 x D D2 Dv DL j).val := by
  rcases q3_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, e⟩ <;>
    rw [e]
  · right; rw [TS_val]; omega
  · left; rfl
  · right; rw [TE_val]; omega
  · right; exact le_trans (Nat.le_add_right _ _) (ca_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j)

theorem q3_inj : Function.Injective (q3 x D D2 Dv DL) := by
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hT := TT_lt_SD (x := x) (D := D) (D2 := D2)
  have hN : NUn = 38 := rfl
  intro a b h
  have hv := congrArg Fin.val h
  have ha := a.isLt
  have hb := b.isLt
  rcases q3_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) a with
      ⟨a1, ea⟩ | ⟨a1, ea⟩ | ⟨a1, ea⟩ | ⟨a1, a2, a3, ea⟩ <;>
    rcases q3_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) b with
      ⟨b1, eb⟩ | ⟨b1, eb⟩ | ⟨b1, eb⟩ | ⟨b1, b2, b3, eb⟩ <;>
    rw [ea, eb] at hv <;>
    simp only [TS_val, TC_val, TE_val, ca_val, hN] at hv
  all_goals first
    | (subst_vars; rfl)
    | (exact Fin.ext (by omega))

noncomputable def MX3 (x D D2 Dv DL : ℕ) :=
  RecoveryFocus.machine (q3 x D D2 Dv DL) (MaskedReset.machine PCJ45bee56da9f34d5a_CapReader.machine (fun _ => true))

/-- The unary source run's cost. -/
def capCost (m : ℕ) : ℕ := 2 * (8 * 2 ^ m + 20 * (m + 1) + 17) + 2

theorem x3_step (m : ℕ) (B : Fin (STx x D D2 Dv DL) → List Bool) (hs : B (TS x D D2 Dv DL) = NumsX.srcWord m)
    (hc : B (TC x D D2 Dv DL) = []) (he : B (TE x D D2 Dv DL) = []) (hca : ∀ k, B (ca k) = []) :
    ∃ out : Fin 12 → List Bool, Step (MX3 x D D2 Dv DL) (capCost m) HI B HI (install (q3 x D D2 Dv DL) B out) ∧
      out 8 = List.replicate (2 ^ m) true ∧ out 9 = List.replicate (2 ^ m) true := by
  have hne : (List.replicate m false ++ [true]) ≠ [] := by simp
  obtain ⟨H3, A3, h3, f3⟩ := PCJ45bee56da9f34d5a_CapReader.run [] (List.replicate m false ++ [true]) [] hne
  obtain ⟨m3, hm⟩ := ListMachine.Row.maskBlank h3 (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have eh0 : (Fin.addCases (PCJ45bee56da9f34d5a_CapReader.initialHeads ([] : List Bool).length) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · fin_cases a <;> rfl
    · simp
  have eh1 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else H3 i) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have hm' := (hm.congr_in eh0 rfl).congr eh1 rfl
  have vJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hH : ∀ j, HI (q3 x D D2 Dv DL j) = 0 := by
    intro j
    apply HI_ne
    apply ne_TJ
    rcases q3_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with e | e <;> omega
  have hsrc := NumsX.srcWord_eq m
  have hA : ∀ j, B (q3 x D D2 Dv DL j) = Fin.addCases (PCJ45bee56da9f34d5a_CapReader.initialBank
      ([] ++ List.replicate (List.replicate m false ++ [true]).length true ++
        false :: ((List.replicate m false ++ [true]) ++ []))) (fun _ : Fin 1 => List.replicate 0 false) j := by
    intro j
    rcases q3_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with
        ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h1, e⟩ | ⟨h0, h8, h9, e⟩ <;> rw [e]
    · subst h1
      rw [hs, hsrc]
      rfl
    · subst h1
      rw [hc]
      rfl
    · subst h1
      rw [he]
      rfl
    · rw [hca j]
      fin_cases j <;> simp_all <;> rfl
  have d := dock0 hm' (q3 x D D2 Dv DL) q3_inj HI B hH hA
  obtain ⟨-, -, a8, -, a9, -, -, -⟩ := f3
  have hv := NumsX.src_value m
  refine ⟨_, d.enlarge ?_, ?_, ?_⟩
  · unfold capCost
    simp only [List.length_append, List.length_replicate, List.length_singleton, hv]
    omega
  · show A3 8 = _
    rw [a8, hv]
  · show A3 9 = _
    rw [a9, hv]

end Stage3

/-! ## Stage 4: the loop bound `b = CL(n'+1)^DL`; stage 5: the counter; stage 6: its head -/

section Stage456
variable {x D D2 Dv DL : ℕ}

noncomputable def MX4 (x D D2 Dv DL CL : ℕ) :=
  RecoveryFocus.machine (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) (PCPSerializerCapacity.Power.machine DL CL)

theorem x4_step (CL n' : ℕ) (B : Fin (STx x D D2 Dv DL) → List Bool) (hi : B (TE x D D2 Dv DL) = List.replicate n' true)
    (hb : ∀ k, k ≠ UnaryCalc.inputTape DL → B (e6 k) = []) :
    ∃ out : Fin (UnaryCalc.tapes DL) → List Bool,
      Step (MX4 x D D2 Dv DL CL) (PCPSerializerCapacity.Power.budget DL CL n') HI B HI (install e6 B out) ∧
      out (UnaryCalc.outputTape DL) = List.replicate (UnaryCalc.value DL CL n') true := by
  obtain ⟨out, h, -, ho⟩ := UnaryCalc.poly_step DL CL n'
  have vJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hH : ∀ k, HI (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) = 0 := by
    intro k
    apply HI_ne
    apply ne_TJ
    have := e6_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k
    omega
  have hA : ∀ k, B (e6 k) = RepairSource.ProjectionNormalization.DimensionPolynomial.input DL n' k := by
    intro k
    by_cases hk : k = UnaryCalc.inputTape DL
    · subst hk
      rw [show e6 (UnaryCalc.inputTape DL) = TE x D D2 Dv DL from rfl, hi]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape]
    · rw [hb k hk]
      have hv : k.val ≠ 0 := fun e => hk (Fin.ext e)
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hv]
  exact ⟨out, dock0 h e6 e6_inj HI B hH hA, ho⟩

theorem TO_ne_TK : TO x D D2 Dv DL ≠ TK x D D2 Dv DL := by
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  intro e
  have := congrArg Fin.val e
  rw [TO_val, TK_val] at this
  omega

noncomputable def MX5 (x D D2 Dv DL : ℕ) :=
  RecoveryFocus.machine ![TO x D D2 Dv DL, TK x D D2 Dv DL] (PacketsGlue.Stamp.machine 0)

theorem x5_step (b : ℕ) (B : Fin (STx x D D2 Dv DL) → List Bool) (ho : B (TO x D D2 Dv DL) = List.replicate b true)
    (hk : B (TK x D D2 Dv DL) = []) :
    Step (MX5 x D D2 Dv DL) (2 * b + 3) HI B HI
      (install ![TO x D D2 Dv DL, TK x D D2 Dv DL] B
        (fun i => if i.val = 0 then List.replicate b true else RepairSource.VerifierDecoding.CompareMachine.word b)) := by
  have vJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  refine dock0 (PacketsGlue.Stamp.run 0 b) _ (ListMachine.Row.pair_inj TO_ne_TK) HI B ?_ ?_
  · intro j
    apply HI_ne
    apply ne_TJ
    fin_cases j
    · show (TO x D D2 Dv DL).val ≠ _
      rw [TO_val]; omega
    · show (TK x D D2 Dv DL).val ≠ _
      rw [TK_val]; omega
  · intro j
    fin_cases j
    · exact ho
    · exact hk

/-- Stage 6: the real counter's head to `1` (the write keeps `OUT = [false]`). -/
def act6 (x D D2 Dv DL : ℕ) : Prog (STx x D D2 Dv DL) :=
  .act (writeAt (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)) false) (moveAt (TK x D D2 Dv DL) .right)

/-- The heads after the boot: both counters' at `1`. -/
def HF (x D D2 Dv DL : ℕ) : Fin (STx x D D2 Dv DL) → ℕ :=
  fun i => if i = TK x D D2 Dv DL then 1 else if i = TJ x D D2 Dv DL then 1 else 0

theorem x6_step (B : Fin (STx x D D2 Dv DL) → List Bool)
    (h1 : B (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)) = [false]) :
    Step (act6 x D D2 Dv DL).compile 1 HI B (HF x D D2 Dv DL) B := by
  have h := act_step (⟨HI, B⟩ : Bank (STx x D D2 Dv DL)) (writeAt (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)) false)
    (moveAt (TK x D D2 Dv DL) .right)
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have vJ := TJ_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have vK := TK_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
  have hKJ : TK x D D2 Dv DL ≠ TJ x D D2 Dv DL := ne_TJ _ (by rw [vK, vJ]; omega)
  have h1v : (lo (Dv := Dv) (DL := DL) (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)).val = 2 := rfl
  have h1J : lo (Dv := Dv) (DL := DL) (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1) ≠ TJ x D D2 Dv DL :=
    ne_TJ _ (by rw [h1v, vJ]; omega)
  refine h.congr ?_ ?_
  · funext i
    by_cases hi : i = TK x D D2 Dv DL
    · subst hi
      simp [Bank.act, moveAt, HeadMove.apply, HF, HI_ne _ hKJ]
    · simp [Bank.act, moveAt, hi, HeadMove.apply, HF, HI_eq]
  · funext i
    by_cases hi : i = lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)
    · subst hi
      simp [Bank.act, writeAt, h1, HI_ne _ h1J, writeTapeBit]
    · simp [Bank.act, writeAt, hi]

end Stage456

/-! ## The boot as one run -/

section Boot
variable {x D D2 Dv DL : ℕ}

theorem inst_keep {t u : ℕ} (slots : Fin t → Fin u) (A : Fin u → List Bool) (L : Fin t → List Bool) (i : Fin u)
    (h : ∀ j, (slots j).val ≠ i.val) : install slots A L i = A i :=
  install_other _ _ _ _ (fun j e => h j (congrArg Fin.val e))

theorem q1_val_ge (k : Fin (UnaryCalc.tapes Dv)) : SD x D D2 ≤ (q1 x D D2 Dv DL k).val := by
  unfold q1
  split_ifs
  · rw [TI_val]; omega
  · rw [e5_val]; omega

theorem q2_val (j : Fin NUn) : (q2 x D D2 Dv DL j).val = 0 ∨ SD x D D2 + SD x D D2 ≤ (q2 x D D2 Dv DL j).val := by
  rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> rw [e]
  · left; rfl
  · right; rw [TW_val]; omega
  · right; rw [nu_val]; omega

theorem q5_val (j : Fin (2 + 0)) : (![TO x D D2 Dv DL, TK x D D2 Dv DL] j).val = (TO x D D2 Dv DL).val ∨
    (![TO x D D2 Dv DL, TK x D D2 Dv DL] j).val = (TK x D D2 Dv DL).val := by
  fin_cases j
  · left; rfl
  · right; rfl

theorem TC_lt : (TC x D D2 Dv DL).val < SD x D D2 := by rw [TC_val]; exact TT_lt_SD
theorem TK_lt : (TK x D D2 Dv DL).val < SD x D D2 := by
  have := SD_ge (x := x) (D := D) (D2 := D2); rw [TK_val]; omega
theorem T0_lt : (T0 x D D2 Dv DL).val < SD x D D2 := by
  have := TT_lt_SD (x := x) (D := D) (D2 := D2); rw [T0_val]; omega
theorem sd_le2 : SD x D D2 ≤ SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv := by omega
theorem sd_le3 : SD x D D2 ≤ SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv + NUn + 12 := by omega
theorem cs1_val : (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1).val = 2 := rfl
theorem cs2_val : (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 2).val = 3 := rfl

end Boot

end NearCubicWires.WireExponent3_5.PrimAsm.ShellX
