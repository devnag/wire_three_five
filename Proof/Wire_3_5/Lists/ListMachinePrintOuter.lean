import Proof.Wire_3_5.Lists.ListMachinePrintInner

/-! # C2p, the outer pass: print, reset, step the support (P3:1482-1488)

Realizes the part of one pass of the interpolation printer after the coefficient of the support `S = supp X` is known:
the record `recW S` is printed when the coefficient is one (`printBr`), the coefficient and result cells are cleared,
the flag `[pop X = d]` is computed (`PopEq`), the lowest-one mask of `X` is written (`M`), and `X` becomes the next
support bitmap `Interp.sw d X` (add the lowest one when `X` has `d` ones, else add one), with the outer loop's flag
`[X ≠ 0]`. The paper quantity is the printed record and the next support. Result: **`outerRest_step`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Rec (dockRun maskRun)
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## Slot maps -/

def sFI : Fin 3 → Fin 14 := ![4, 3, 2]
theorem sFI_inj : Function.Injective sFI := by decide
def pFI : Fin 14 → Option (Fin 3) :=
  ![none, none, some 2, some 1, some 0, none, none, none, none, none, none, none, none, none]
theorem pick_sFI : ∀ i, RecoveryFocus.pick sFI i = pFI i := by pick_table sFI_inj

def sRA : Fin 3 → Fin 14 := ![2, 3, 4]
theorem sRA_inj : Function.Injective sRA := by decide
def pRA : Fin 14 → Option (Fin 3) :=
  ![none, none, some 0, some 1, some 2, none, none, none, none, none, none, none, none, none]
theorem pick_sRA : ∀ i, RecoveryFocus.pick sRA i = pRA i := by pick_table sRA_inj

def sPA : Fin 3 → Fin 14 := ![6, 3, 2]
theorem sPA_inj : Function.Injective sPA := by decide
def pPA : Fin 14 → Option (Fin 3) :=
  ![none, none, some 2, some 1, none, none, some 0, none, none, none, none, none, none, none]
theorem pick_sPA : ∀ i, RecoveryFocus.pick sPA i = pPA i := by pick_table sPA_inj

def sXDPL : Fin 4 → Fin 14 := ![0, 9, 6, 12]
theorem sXDPL_inj : Function.Injective sXDPL := by decide
def pXDPL : Fin 14 → Option (Fin 4) :=
  ![some 0, none, none, none, none, none, some 2, none, none, some 1, none, none, some 3, none]
theorem pick_sXDPL : ∀ i, RecoveryFocus.pick sXDPL i = pXDPL i := by pick_table sXDPL_inj

def sMXL : Fin 3 → Fin 14 := ![7, 0, 12]
theorem sMXL_inj : Function.Injective sMXL := by decide
def pMXL : Fin 14 → Option (Fin 3) :=
  ![some 1, none, none, none, none, none, none, some 0, none, none, none, none, some 2, none]
theorem pick_sMXL : ∀ i, RecoveryFocus.pick sMXL i = pMXL i := by pick_table sMXL_inj

def sXML : Fin 3 → Fin 14 := ![0, 7, 12]
theorem sXML_inj : Function.Injective sXML := by decide
def pXML : Fin 14 → Option (Fin 3) :=
  ![some 0, none, none, none, none, none, none, some 1, none, none, none, none, some 2, none]
theorem pick_sXML : ∀ i, RecoveryFocus.pick sXML i = pXML i := by pick_table sXML_inj

def sXZL : Fin 3 → Fin 14 := ![0, 8, 12]
theorem sXZL_inj : Function.Injective sXZL := by decide
def pXZL : Fin 14 → Option (Fin 3) :=
  ![some 0, none, none, none, none, none, none, none, some 1, none, none, none, some 2, none]
theorem pick_sXZL : ∀ i, RecoveryFocus.pick sXZL i = pXZL i := by pick_table sXZL_inj

def sXZFL : Fin 4 → Fin 14 := ![0, 8, 5, 12]
theorem sXZFL_inj : Function.Injective sXZFL := by decide
def pXZFL : Fin 14 → Option (Fin 4) :=
  ![some 0, none, none, none, none, some 2, none, none, some 1, none, none, none, some 3, none]
theorem pick_sXZFL : ∀ i, RecoveryFocus.pick sXZFL i = pXZFL i := by pick_table sXZFL_inj

/-! ## The operations -/

def constOp (c : Bool) (_ _ _ : Bool) : Bool := c

/-- The lowest-one mask of the operand, the target's old content ignored. -/
def gL' (_ x s : Bool) : Bool := x && !s
def hL' (_ x s : Bool) : Bool := s || x

theorem ripple_gL' (m xs : List Bool) (hl : m.length = xs.length) (c : Bool) :
    Block.ripple gL' hL' c m xs = Block.ripple Interp.gL Interp.hL c xs xs := by
  induction m generalizing xs c with
  | nil =>
    cases xs with
    | nil => rfl
    | cons x xs => simp at hl
  | cons a m ih =>
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      simp only [Block.ripple, gL', hL', Interp.gL, Interp.hL]
      rw [ih xs (by simpa using hl)]

theorem ripple_length (g h : Bool → Bool → Bool → Bool) (c : Bool) (u v : List Bool) (hl : u.length = v.length) :
    (Block.ripple g h c u v).length = u.length := by
  induction u generalizing v c with
  | nil => cases v <;> rfl
  | cons a u ih =>
    cases v with
    | nil => simp at hl
    | cons b v => simp [Block.ripple, ih _ v (by simpa using hl)]

theorem sw_length (d : ℕ) (xs : List Bool) : (Interp.sw d xs).length = xs.length := by
  unfold Interp.sw
  split_ifs
  · rw [ripple_length _ _ _ _ _ (ripple_length _ _ _ _ _ rfl).symm]
  · rw [ripple_length _ _ _ _ _ (by simp)]

/-! ## The stages -/

noncomputable def resetAM := RecoveryFocus.machine sAR (GF2.CellOp.machine (constOp false))
noncomputable def resetRM := RecoveryFocus.machine sRA (GF2.CellOp.machine (constOp false))
noncomputable def resetPFM := RecoveryFocus.machine sPA (GF2.CellOp.machine (constOp false))
noncomputable def popM := RecoveryFocus.machine sXDPL (MaskedReset.machine PopEq.machine selTTF)
noncomputable def lowM :=
  RecoveryFocus.machine sMXL (MaskedReset.machine (Block.RippleIn.machine gL' hL' false) selTT)
noncomputable def addBr := Block.branchM (6 : Fin 14)
  (RecoveryFocus.machine sXML (MaskedReset.machine (Block.RippleIn.machine Block.sum3 Block.carry3 false) selTT))
  (RecoveryFocus.machine sXZL (MaskedReset.machine (Block.RippleIn.machine Block.sum3 Block.carry3 true) selTT))
noncomputable def foM := RecoveryFocus.machine sXZFL (MaskedReset.machine (Block.FoldCell.machine orFold false) selTTF)

theorem reset_step (s : Fin 3 → Fin 14) (hs : Function.Injective s) (o : ℕ) (b b' : Bank) (x y z : Bool)
    (hH : ∀ j, bh o (s j) = 0) (hA : ∀ j, b.tapes (s j) = ![[x], [y], [z]] j)
    (hb : RecoveryRootRound.install s b.tapes ![[false], [y], [z]] = b'.tapes) :
    Step (RecoveryFocus.machine s (GF2.CellOp.machine (constOp false))) 1 (bh o) b.tapes (bh o) b'.tapes :=
  cell_step (constOp false) s hs o b b' x y z hH hA hb

theorem pop_step (b : Bank) (o : ℕ) (xs : List Bool) (d : ℕ) (dtail : List Bool) (pf0 : Bool) (cap : ℕ)
    (hx : b.x = frame xs) (hd : b.d = List.replicate d true ++ false :: dtail) (hpf : b.pf = [pf0])
    (hl : b.l1 = List.replicate cap false) (hpop : Interp.pop xs ≤ d) (hcap : 2 * xs.length + 1 ≤ cap) :
    Step popM (2 * (2 * xs.length + 1) + 2) (bh o) b.tapes (bh o)
      { b with pf := [decide (Interp.pop xs = d)] }.tapes :=
  pop_stage sXDPL sXDPL_inj o b _ xs d dtail pf0 hpop cap hcap (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hx
        · exact hd
        · exact hpf
        · exact hl)
    (by rw [install_of_pick sXDPL pXDPL pick_sXDPL]
        funext i; fin_cases i <;> simp [pXDPL, Bank.tapes, hx, hd, hl])

theorem low_step (b : Bank) (o : ℕ) (xs m : List Bool) (cap : ℕ) (hm : b.m = frame m) (hx : b.x = frame xs)
    (hl : b.l1 = List.replicate cap false) (hmL : m.length = xs.length) (hcap : 2 * xs.length + 1 ≤ cap) :
    Step lowM (2 * (2 * m.length + 1) + 2) (bh o) b.tapes (bh o)
      { b with m := frame (Block.ripple Interp.gL Interp.hL false xs xs) }.tapes :=
  ripple_stage gL' hL' false sMXL sMXL_inj o b _ m xs hmL cap (by rw [hmL]; exact hcap)
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hm
        · exact hx
        · exact hl)
    (by rw [install_of_pick sMXL pMXL pick_sMXL, ripple_gL' m xs hmL]
        funext i; fin_cases i <;> simp [pMXL, Bank.tapes, hx, hl])

theorem addBr_step (b : Bank) (o : ℕ) (xs : List Bool) (d : ℕ) (cap : ℕ) (hx : b.x = frame xs)
    (hm : b.m = frame (Block.ripple Interp.gL Interp.hL false xs xs))
    (hz : b.z = frame (List.replicate xs.length false)) (hpf : b.pf = [decide (Interp.pop xs = d)])
    (hl : b.l1 = List.replicate cap false) (hcap : 2 * xs.length + 1 ≤ cap) :
    Step addBr (2 * (2 * xs.length + 1) + 2 + 2) (bh o) b.tapes (bh o)
      { b with x := frame (Interp.sw d xs) }.tapes := by
  have hml : (Block.ripple Interp.gL Interp.hL false xs xs).length = xs.length := ripple_length _ _ _ _ _ rfl
  by_cases hp : Interp.pop xs = d
  · have hs := ripple_stage Block.sum3 Block.carry3 false sXML sXML_inj o b { b with x := frame (Interp.sw d xs) }
      xs _ hml.symm cap hcap (by intro j; fin_cases j <;> rfl)
      (by intro j; fin_cases j
          · exact hx
          · exact hm
          · exact hl)
      (by rw [install_of_pick sXML pXML pick_sXML]
          unfold Interp.sw; rw [if_pos hp]
          funext i; fin_cases i <;> simp [pXML, Bank.tapes, hm, hl])
    exact Block.branch_true (6 : Fin 14) _ hs (by simp [Bank.tapes, hpf, hp, bh, readTapeBit])
  · have hs := ripple_stage Block.sum3 Block.carry3 true sXZL sXZL_inj o b { b with x := frame (Interp.sw d xs) }
      xs (List.replicate xs.length false) (by simp) cap hcap (by intro j; fin_cases j <;> rfl)
      (by intro j; fin_cases j
          · exact hx
          · exact hz
          · exact hl)
      (by rw [install_of_pick sXZL pXZL pick_sXZL]
          unfold Interp.sw; rw [if_neg hp]
          funext i; fin_cases i <;> simp [pXZL, Bank.tapes, hz, hl])
    exact Block.branch_false (6 : Fin 14) _ hs (by simp [Bank.tapes, hpf, hp, bh, readTapeBit])

theorem fo_step (b : Bank) (o : ℕ) (ys : List Bool) (fo0 : Bool) (cap : ℕ) (hx : b.x = frame ys)
    (hz : b.z = frame (List.replicate ys.length false)) (hfo : b.fo = [fo0]) (hl : b.l1 = List.replicate cap false)
    (hcap : 2 * ys.length + 1 ≤ cap) :
    Step foM (2 * (2 * ys.length + 1) + 2) (bh o) b.tapes (bh o) { b with fo := [ys.any id] }.tapes :=
  fold_stage orFold false sXZFL sXZFL_inj o b _ ys (List.replicate ys.length false) fo0 (by simp) cap hcap
    (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j
        · exact hx
        · exact hz
        · exact hfo
        · exact hl)
    (by rw [install_of_pick sXZFL pXZFL pick_sXZFL, foldBits_orFold _ _ (by simp)]
        funext i; fin_cases i <;> simp [pXZFL, Bank.tapes, hx, hz, hl])


end NearCubicWires.WireExponent3_5.ListMachine.Print
