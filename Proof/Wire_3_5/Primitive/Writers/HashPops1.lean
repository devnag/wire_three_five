import Proof.Wire_3_5.Primitive.Writers.Emit
import Proof.Wire_3_5.FinalPass.ThrPtPad
import Proof.Wire_3_5.Primitive.SeedFix.HbPops
import Proof.Wire_3_5.FinalPass.DigsIface

/-! # HASH setup (C), P2a part 1: the populations loop's layout, tracked state and bit copies

The HASH call's populations stream `popsWord (hashPopsOf …)` (`HbM.popsWord`, `filt:soft` P3:2253-2293) is written
row by row: for each selection `g` and prime `p ≤ cut`, C1's digit program `Digs.DigsW` writes the row's digit
populations as `digsWord` (one segment `gis.flatMap elemW ++ [false]` per digit), and each segment is copied twice
behind the headers `[1, 0]` and `[1, 1]` (the records `popRec (false, gis)`, `popRec (true, gis)`). This part fixes
the loop's layout (`PL`: payload streams, the digit stream `Dg`, the primes stream `PR`, the output `O`, the digit
program's registers `R` and the loop's registers), its tracked state (`LS`, `LS.w`: output, digit stream, heads and
counters over a base state) with its update lemmas, and the bit copies:

* `cpBit`, **`cpBit_spec`**; `onesCW`, **`ones_spec`**; `elemCW`, **`elem_spec`**; `segCW`, **`seg_spec`** (a digit
  population's segment copied from `Dg` to `O`, its length counted in `K`).

Paper quantity of the main type: the words of the HASH call's populations (`popRec`, P3:2253-2293). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashPops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-- **The loop's layout**: payload streams, the digit stream, the primes stream, the output, the digit program's
registers and the loop's registers (`OP` the output's length, `K` a segment's length, `DL` the digit word's length,
`DC` the digit counter, `T` a copy temporary, `GR` the selections left, `PH` the primes stream's head). -/
structure PL (ns nr : ℕ) where
  Pay : Fin 4 → Fin (ns + 1)
  Dg : Fin (ns + 1)
  PR : Fin (ns + 1)
  O : Fin (ns + 1)
  R : Fin FinalPass.Digs.digsK ↪ Fin nr
  OP : Fin nr
  K : Fin nr
  DL : Fin nr
  DC : Fin nr
  T : Fin nr
  GR : Fin nr
  PH : Fin nr

/-- The tracked registers, in order. -/
def PL.regs {ns nr : ℕ} (L : PL ns nr) : Fin 9 → Fin nr := ![L.OP, L.K, L.DL, L.DC, L.GR, L.R 1, L.R 2, L.PH, L.T]

/-- **The layout's distinctness.** -/
structure PL.Ok {ns nr : ℕ} (L : PL ns nr) : Prop where
  sInj : Function.Injective ![L.O, L.Dg, L.PR]
  payInj : Function.Injective L.Pay
  payNe : ∀ i, L.Pay i ≠ L.O ∧ L.Pay i ≠ L.Dg ∧ L.Pay i ≠ L.PR
  rInj : Function.Injective L.regs
  rOut : ∀ j : Fin FinalPass.Digs.digsK, j.val ≠ 1 → j.val ≠ 2 → ∀ k : Fin 9, L.R j ≠ L.regs k

section Ok
variable {ns nr : ℕ} {L : PL ns nr} (h : L.Ok)
include h

theorem rne {a b : Fin 9} (hab : a ≠ b) : L.regs a ≠ L.regs b := fun e => hab (h.rInj e)

theorem O_Dg : L.O ≠ L.Dg := fun e => absurd (h.sInj (a₁ := 0) (a₂ := 1) (by simpa using e)) (by decide)
theorem O_PR : L.O ≠ L.PR := fun e => absurd (h.sInj (a₁ := 0) (a₂ := 2) (by simpa using e)) (by decide)
theorem Dg_PR : L.Dg ≠ L.PR := fun e => absurd (h.sInj (a₁ := 1) (a₂ := 2) (by simpa using e)) (by decide)

end Ok

/-- **The loop's tracked state**: the output, the digit stream and its head, the counters. -/
@[ext] structure LS where
  out : List Bool
  dg : List Bool
  dh : ℕ
  k : ℕ
  dl : ℕ
  dc : ℕ
  gr : ℕ
  gi : ℕ
  p : ℕ
  ph : ℕ

/-- The tracked state over a base state `σB`: the output with its head at its end and `OP = |out|`, the digit stream,
the primes stream's head `= PH`, the counters; everything else as in `σB`. -/
def LS.w {ns nr : ℕ} (L : PL ns nr) (σB : WState ns nr) (t : LS) : WState ns nr :=
  ⟨fun s => if s = L.O then t.out.length else if s = L.Dg then t.dh else if s = L.PR then t.ph else σB.sh s,
   fun s => if s = L.O then t.out else if s = L.Dg then t.dg else σB.st s,
   fun r => if r = L.OP then t.out.length else if r = L.K then t.k else if r = L.DL then t.dl else
     if r = L.DC then t.dc else if r = L.GR then t.gr else if r = L.R 1 then t.gi else if r = L.R 2 then t.p else
     if r = L.PH then t.ph else σB.val r,
   σB.cell⟩

section W
variable {ns nr : ℕ} (L : PL ns nr) (h : L.Ok) (σB : WState ns nr) (t : LS)
include h

theorem neOP_K : L.OP ≠ L.K := rne h (a := 0) (b := 1) (by decide)
theorem neOP_DL : L.OP ≠ L.DL := rne h (a := 0) (b := 2) (by decide)
theorem neOP_DC : L.OP ≠ L.DC := rne h (a := 0) (b := 3) (by decide)
theorem neOP_GR : L.OP ≠ L.GR := rne h (a := 0) (b := 4) (by decide)
theorem neOP_1 : L.OP ≠ L.R 1 := rne h (a := 0) (b := 5) (by decide)
theorem neOP_2 : L.OP ≠ L.R 2 := rne h (a := 0) (b := 6) (by decide)
theorem neOP_PH : L.OP ≠ L.PH := rne h (a := 0) (b := 7) (by decide)
theorem neK_DL : L.K ≠ L.DL := rne h (a := 1) (b := 2) (by decide)
theorem neK_DC : L.K ≠ L.DC := rne h (a := 1) (b := 3) (by decide)
theorem neK_GR : L.K ≠ L.GR := rne h (a := 1) (b := 4) (by decide)
theorem neK_1 : L.K ≠ L.R 1 := rne h (a := 1) (b := 5) (by decide)
theorem neK_2 : L.K ≠ L.R 2 := rne h (a := 1) (b := 6) (by decide)
theorem neK_PH : L.K ≠ L.PH := rne h (a := 1) (b := 7) (by decide)
theorem neDL_DC : L.DL ≠ L.DC := rne h (a := 2) (b := 3) (by decide)
theorem neDL_GR : L.DL ≠ L.GR := rne h (a := 2) (b := 4) (by decide)
theorem neDL_1 : L.DL ≠ L.R 1 := rne h (a := 2) (b := 5) (by decide)
theorem neDL_2 : L.DL ≠ L.R 2 := rne h (a := 2) (b := 6) (by decide)
theorem neDL_PH : L.DL ≠ L.PH := rne h (a := 2) (b := 7) (by decide)
theorem neDC_GR : L.DC ≠ L.GR := rne h (a := 3) (b := 4) (by decide)
theorem neDC_1 : L.DC ≠ L.R 1 := rne h (a := 3) (b := 5) (by decide)
theorem neDC_2 : L.DC ≠ L.R 2 := rne h (a := 3) (b := 6) (by decide)
theorem neDC_PH : L.DC ≠ L.PH := rne h (a := 3) (b := 7) (by decide)
theorem neGR_1 : L.GR ≠ L.R 1 := rne h (a := 4) (b := 5) (by decide)
theorem neGR_2 : L.GR ≠ L.R 2 := rne h (a := 4) (b := 6) (by decide)
theorem neGR_PH : L.GR ≠ L.PH := rne h (a := 4) (b := 7) (by decide)
theorem ne1_2 : L.R 1 ≠ L.R 2 := rne h (a := 5) (b := 6) (by decide)
theorem ne1_PH : L.R 1 ≠ L.PH := rne h (a := 5) (b := 7) (by decide)
theorem ne2_PH : L.R 2 ≠ L.PH := rne h (a := 6) (b := 7) (by decide)
theorem neT_OP : L.T ≠ L.OP := rne h (a := 8) (b := 0) (by decide)
theorem neT_K : L.T ≠ L.K := rne h (a := 8) (b := 1) (by decide)
theorem neT_DL : L.T ≠ L.DL := rne h (a := 8) (b := 2) (by decide)
theorem neT_DC : L.T ≠ L.DC := rne h (a := 8) (b := 3) (by decide)
theorem neT_GR : L.T ≠ L.GR := rne h (a := 8) (b := 4) (by decide)
theorem neT_1 : L.T ≠ L.R 1 := rne h (a := 8) (b := 5) (by decide)
theorem neT_2 : L.T ≠ L.R 2 := rne h (a := 8) (b := 6) (by decide)
theorem neT_PH : L.T ≠ L.PH := rne h (a := 8) (b := 7) (by decide)

@[simp] theorem w_st_O : (t.w L σB).st L.O = t.out := by simp [LS.w]
@[simp] theorem w_sh_O : (t.w L σB).sh L.O = t.out.length := by simp [LS.w]
theorem w_st_Dg : (t.w L σB).st L.Dg = t.dg := by simp [LS.w, (O_Dg h).symm]
theorem w_sh_Dg : (t.w L σB).sh L.Dg = t.dh := by simp [LS.w, (O_Dg h).symm]
theorem w_st_PR : (t.w L σB).st L.PR = σB.st L.PR := by simp [LS.w, (O_PR h).symm, (Dg_PR h).symm]
theorem w_sh_PR : (t.w L σB).sh L.PR = t.ph := by simp [LS.w, (O_PR h).symm, (Dg_PR h).symm]
theorem w_st_other (s : Fin (ns + 1)) (h1 : s ≠ L.O) (h2 : s ≠ L.Dg) : (t.w L σB).st s = σB.st s := by
  simp [LS.w, h1, h2]
theorem w_sh_other (s : Fin (ns + 1)) (h1 : s ≠ L.O) (h2 : s ≠ L.Dg) (h3 : s ≠ L.PR) : (t.w L σB).sh s = σB.sh s := by
  simp [LS.w, h1, h2, h3]
@[simp] theorem w_OP : (t.w L σB).val L.OP = t.out.length := by simp [LS.w]
theorem w_K : (t.w L σB).val L.K = t.k := by simp [LS.w, (neOP_K L h).symm]
theorem w_DL : (t.w L σB).val L.DL = t.dl := by simp [LS.w, (neOP_DL L h).symm, (neK_DL L h).symm]
theorem w_DC : (t.w L σB).val L.DC = t.dc := by
  simp [LS.w, (neOP_DC L h).symm, (neK_DC L h).symm, (neDL_DC L h).symm]
theorem w_GR : (t.w L σB).val L.GR = t.gr := by
  simp [LS.w, (neOP_GR L h).symm, (neK_GR L h).symm, (neDL_GR L h).symm, (neDC_GR L h).symm]
theorem w_1 : (t.w L σB).val (L.R 1) = t.gi := by
  simp [LS.w, (neOP_1 L h).symm, (neK_1 L h).symm, (neDL_1 L h).symm, (neDC_1 L h).symm, (neGR_1 L h).symm]
theorem w_2 : (t.w L σB).val (L.R 2) = t.p := by
  simp [LS.w, (neOP_2 L h).symm, (neK_2 L h).symm, (neDL_2 L h).symm, (neDC_2 L h).symm, (neGR_2 L h).symm,
    (ne1_2 L h).symm]
theorem w_PH : (t.w L σB).val L.PH = t.ph := by
  simp [LS.w, (neOP_PH L h).symm, (neK_PH L h).symm, (neDL_PH L h).symm, (neDC_PH L h).symm, (neGR_PH L h).symm,
    (ne1_PH L h).symm, (ne2_PH L h).symm]
theorem w_T : (t.w L σB).val L.T = σB.val L.T := by
  simp [LS.w, neT_OP L h, neT_K L h, neT_DL L h, neT_DC L h, neT_GR L h, neT_1 L h, neT_2 L h, neT_PH L h]
theorem w_val_other (r : Fin nr) (h1 : r ≠ L.OP) (h2 : r ≠ L.K) (h3 : r ≠ L.DL) (h4 : r ≠ L.DC) (h5 : r ≠ L.GR)
    (h6 : r ≠ L.R 1) (h7 : r ≠ L.R 2) (h8 : r ≠ L.PH) : (t.w L σB).val r = σB.val r := by
  simp [LS.w, h1, h2, h3, h4, h5, h6, h7, h8]
@[simp] theorem w_cell : (t.w L σB).cell = σB.cell := rfl

end W

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
