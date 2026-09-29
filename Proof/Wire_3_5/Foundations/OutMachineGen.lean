import Proof.Wire_3_5.Foundations.OutMachineP5
import Proof.Wire_3_5.Primitive.SeedFix.C4KWd

/-! # The output machine: the out machine (`Bank.OutGen mOut`)

"At one sampled input, [...] This takes polynomial time without evaluating a monomial expansion" (P3:3175-3178); the
final pass prints its estimate `ratWord (Num/Den)` (P3:3044-3048). The six phases (`Out.Iface`) compose by
`WExec.seq` into ONE word program `outP`; base's masked reset (`C4KW.wm_blankR`) turns its run from blank registers
into a machine run with every head back at `0` (cost `2n + 2`); `Block.dockKeep` docks it by `slotsO` (`O, N, D` on
`o, tN, tD`, the other 21 tapes on the room `e`).

* **`outP_run`**: from the entry (`Num`, `Den` on `N`, `D`), the phases' values chain (`strip_spec`, `oddPart_spec`,
  `gcd_oddPart`, `reduce_eq`) to `O = ratWord (Num/Den)`, every register `0`;
* `roomIdx`, **`slotsO`**, `slotsO_inj`, `entryOf` (the word state read off the bank), `tin_eq`;
* **`outOfPhases : OutOfPhases`**; **`outGen : Bank.OutGen mOut`** (the six proved phases);
  **`outGen_D`** (`= Dout = 2`), **`outGen_C`** (`= Cout = 6620`), plain constants for every layout.

Paper quantity of the main type: the printed rational `ratWord (Num/Den)` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Gen
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot)

/-! ## The word program -/

/-- **The out machine's word program**: the six phases in sequence. -/
def outP (p1 : Ph1) (p2 : Ph2) (p3 : Ph3) (p4 : Ph4) (p5 : Ph5) (p6 : Ph6) : WM nsO nrO :=
  .seq p1.P (.seq p2.P (.seq p3.P (.seq p4.P (.seq p5.P p6.P))))

/-- Its cost. -/
def nTot (p1 : Ph1) (p2 : Ph2) (p3 : Ph3) (p4 : Ph4) (p5 : Ph5) (p6 : Ph6) (W : ℕ) : ℕ :=
  p1.cost W + 1 + (p2.cost W + 1 + (p3.cost W + 1 + (p4.cost W + 1 + (p5.cost W + 1 + p6.cost W))))

/-- **The phases chain**: from the entry, `O = ratWord (Num/Den)`, every register `0`, the cell `false`. -/
theorem outP_run (p1 : Ph1) (p2 : Ph2) (p3 : Ph3) (p4 : Ph4) (p5 : Ph5) (p6 : Ph6) (W num den : ℕ) (σ : St)
    (h : Entry σ W num den) (hn : num < 2 ^ W) (hd : den < 2 ^ W) (hd0 : 0 < den) :
    ∃ τ, WExec (capO W) (outP p1 p2 p3 p4 p5 p6) σ τ (nTot p1 p2 p3 p4 p5 p6 W) ∧ τ.cell = false ∧
      (∀ r, τ.val r = 0) ∧ τ.st sO = ratWord ((num : ℚ) / den) := by
  obtain ⟨τ1, e1, w1⟩ := p1.run W num den σ h hn hd
  obtain ⟨j, hja, hjb, hodd, hb0⟩ := Val.strip_spec W num den hd0 hd
  have hle := Val.strip_le W (num, den)
  have ha : (strip W num den).1 < 2 ^ W := lt_of_le_of_lt hle.1 hn
  have hb : (strip W num den).2 < 2 ^ W := lt_of_le_of_lt hle.2 hd
  obtain ⟨τ2, e2, w2⟩ := p2.run W _ _ 0 0 τ1 w1 ha hb
  obtain ⟨i, hbo, hoo⟩ := Val.oddPart_spec W _ hb0 hb
  have ho : oddPart W (strip W num den).2 < 2 ^ W := lt_of_le_of_lt (Val.oddPart_le W _) hb
  obtain ⟨τ3, e3, w3⟩ := p3.run W _ _ _ _ τ2 w2 hoo ho ha
  have hg := Val.gcd_oddPart _ _ _ i hodd hbo
  rw [hg] at w3
  have hgodd : Nat.gcd (strip W num den).1 (strip W num den).2 % 2 = 1 := by
    rw [← hg]
    rcases Nat.mod_two_eq_zero_or_one (Nat.gcd (oddPart W (strip W num den).2) (strip W num den).1) with h2 | h2
    · exfalso
      have : 2 ∣ oddPart W (strip W num den).2 := (Nat.dvd_of_mod_eq_zero h2).trans (Nat.gcd_dvd_left _ _)
      omega
    · exact h2
  obtain ⟨τ4, e4, w4⟩ := p4.run W _ _ 0 τ3 w3 hgodd ha hb hb0
  have hgpos : 0 < Nat.gcd (strip W num den).1 (strip W num den).2 := Nat.gcd_pos_of_pos_right _ hb0
  obtain ⟨τ5, e5, w5⟩ := p5.run W _ _ τ4 w4 (Nat.coprime_div_gcd_div_gcd hgpos)
    (Nat.div_pos (Nat.gcd_le_right _ hb0) hgpos) (lt_of_le_of_lt (Nat.div_le_self _ _) ha)
    (lt_of_le_of_lt (Nat.div_le_self _ _) hb)
  rw [Val.reduce_eq num den _ _ j hja hjb hb0] at w5
  obtain ⟨τ6, e6, c6, v6, o6⟩ := p6.run W _ τ5 w5
  exact ⟨τ6, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6)))), c6, v6, o6⟩

/-! ## The dock -/

/-- The room index of a compiled tape (the cell `1 ↦ 0`, the tapes `4 … 23 ↦ 1 … 20`). -/
def roomIdx (c : Fin (nsO + 2 + nrO + 1)) : Fin mOut :=
  ⟨if c.val = 1 then 0 else c.val - 3, by have : c.val < 24 := c.isLt; show _ < 21; split_ifs <;> omega⟩

/-- **The slots**: `O ↦ o`, `N ↦ tN`, `D ↦ tD`, the rest into the room. -/
def slotsO {t : ℕ} (o tN tD : Fin t) (e : Fin mOut ↪ Fin t) (c : Fin (nsO + 2 + nrO + 1)) : Fin t :=
  if c.val = 0 then o else if c.val = 2 then tN else if c.val = 3 then tD else e (roomIdx c)

theorem slotsO_inj {t : ℕ} (o tN tD : Fin t) (e : Fin mOut ↪ Fin t) (he : ∀ i, e i ≠ o ∧ e i ≠ tN ∧ e i ≠ tD)
    (hoN : o ≠ tN) (hoD : o ≠ tD) (hND : tN ≠ tD) : Function.Injective (slotsO o tN tD e) := by
  intro a b h
  unfold slotsO at h
  apply Fin.ext
  have ha : a.val < 24 := a.isLt
  have hb : b.val < 24 := b.isLt
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 <;>
    first
    | omega
    | exact absurd h hoN
    | exact absurd h hoD
    | exact absurd h hND
    | exact absurd h.symm hoN
    | exact absurd h.symm hoD
    | exact absurd h.symm hND
    | exact absurd h.symm (he _).1
    | exact absurd h.symm (he _).2.1
    | exact absurd h.symm (he _).2.2
    | exact absurd h (he _).1
    | exact absurd h (he _).2.1
    | exact absurd h (he _).2.2
    | (have := congrArg Fin.val (e.injective h); simp only [roomIdx] at this; split_ifs at this <;> omega)

/-- The word state read off the bank: the streams from their slots, heads and registers `0`. -/
def entryOf {t : ℕ} (o tN tD : Fin t) (e : Fin mOut ↪ Fin t) (Ab : Fin t → List Bool) : St :=
  ⟨fun _ => 0, fun i => Ab (slotsO o tN tD e (Fin.castAdd 1 (sTape i))), fun _ => 0, false⟩

theorem slotsO_room {t : ℕ} (o tN tD : Fin t) (e : Fin mOut ↪ Fin t) (c : Fin (nsO + 2 + nrO + 1))
    (h0 : c.val ≠ 0) (h2 : c.val ≠ 2) (h3 : c.val ≠ 3) : slotsO o tN tD e c = e (roomIdx c) := by
  unfold slotsO; rw [if_neg h0, if_neg h2, if_neg h3]

theorem entry_of {t : ℕ} (o tN tD : Fin t) (e : Fin mOut ↪ Fin t) (sc : Fin t → Bool) (Ab : Fin t → List Bool)
    (W num den : ℕ) (hsc : ∀ i, sc (e i) = true) (hbl : ∀ j, sc j = true → Ab j = []) (hO : Ab o = [])
    (hN : Ab tN = frame (binary W num)) (hD : Ab tD = frame (binary W den)) :
    Entry (entryOf o tN tD e Ab) W num den := by
  refine ⟨⟨fun _ => rfl, rfl, rfl, fun _ _ => rfl⟩, hN, hD, fun i h1 h2 => ?_⟩
  show Ab (slotsO o tN tD e (Fin.castAdd 1 (sTape i))) = []
  by_cases h0 : i = sO
  · subst h0; exact hO
  · have hv : 3 ≤ i.val := by
      have e1 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      have e2 : i.val ≠ 1 := fun h => h1 (Fin.ext h)
      have e3 : i.val ≠ 2 := fun h => h2 (Fin.ext h)
      omega
    have hs : (Fin.castAdd 1 (sTape (nr := nrO) i)).val = i.val + 1 := by
      simp only [Fin.val_castAdd, sTape]; split_ifs <;> omega
    rw [slotsO_room o tN tD e _ (by omega) (by omega) (by omega)]
    exact hbl _ (hsc _)

theorem tin_eq {t : ℕ} (o tN tD : Fin t) (e : Fin mOut ↪ Fin t) (sc : Fin t → Bool) (Ab : Fin t → List Bool)
    (hsc : ∀ i, sc (e i) = true) (hbl : ∀ j, sc j = true → Ab j = []) (c : Fin (nsO + 2 + nrO + 1)) :
    Ab (slotsO o tN tD e c) = Fin.addCases (PrimT.C4Pipe.wblank (entryOf o tN tD e Ab)) (fun _ : Fin 1 => []) c := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) c
  · rw [Fin.addCases_left]
    simp only [PrimT.C4Pipe.wblank]
    cases hr : role j with
    | stream i =>
      have hj := role_stream hr
      subst hj
      rfl
    | cell =>
      have hj := role_cell hr
      subst hj
      rw [slotsO_room o tN tD e _ (by decide) (by decide) (by decide)]
      exact hbl _ (hsc _)
    | reg r =>
      have hj := role_reg hr
      subst hj
      have hv : (Fin.castAdd 1 (rTape (ns := nsO) r)).val = 13 + r.val := by simp [rTape]
      rw [slotsO_room o tN tD e _ (by omega) (by omega) (by omega)]
      exact hbl _ (hsc _)
  · rw [Fin.addCases_right]
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    rw [slotsO_room o tN tD e _ (by decide) (by decide) (by decide)]
    exact hbl _ (hsc _)

/-! ## The out machine -/

/-- The compiled word program under the masked reset, docked by `slotsO`. -/
noncomputable def machO {t : ℕ} (o tN tD : Fin t) (e : Fin mOut ↪ Fin t) (p1 : Ph1) (p2 : Ph2) (p3 : Ph3)
    (p4 : Ph4) (p5 : Ph5) (p6 : Ph6) : Machine t ((outP p1 p2 p3 p4 p5 p6).toProg.size + 2) :=
  RecoveryFocus.machine (slotsO o tN tD e)
    (MaskedReset.machine (outP p1 p2 p3 p4 p5 p6).toProg.compile (fun _ => true))

/-- The exit tapes: the machine's own run (determined, no choice). -/
def exitO {t s : ℕ} (M : Machine t s) (cost : ℕ → ℕ) (Ab : Fin t → List Bool) (W : ℕ) : Fin t → List Bool :=
  match runFrom M (cost W) ⟨M.start, fun _ => 0, Ab⟩ with
  | some r => r.final.tapes
  | none => Ab

theorem cost_bound (p1 : Ph1) (p2 : Ph2) (p3 : Ph3) (p4 : Ph4) (p5 : Ph5) (p6 : Ph6) (W : ℕ) :
    2 * nTot p1 p2 p3 p4 p5 p6 W + 2 ≤ (2 * (p1.C + p2.C + p3.C + p4.C + p5.C + p6.C) + 12) * (W + 1) ^ 2 := by
  have h1 := p1.cost_le W
  have h2 := p2.cost_le W
  have h3 := p3.cost_le W
  have h4 := p4.cost_le W
  have h5 := p5.cost_le W
  have h6 := p6.cost_le W
  have hX : 1 ≤ (W + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold nTot
  nlinarith

theorem outOf_run (p1 : Ph1) (p2 : Ph2) (p3 : Ph3) (p4 : Ph4) (p5 : Ph5) (p6 : Ph6) {t : ℕ} (o tN tD : Fin t)
    (sc : Fin t → Bool) (e : Fin mOut ↪ Fin t) (hsc : ∀ i, sc (e i) = true)
    (he : ∀ i, e i ≠ o ∧ e i ≠ tN ∧ e i ≠ tD) (hoN : o ≠ tN) (hoD : o ≠ tD) (hND : tN ≠ tD)
    (Ab : Fin t → List Bool) (W num den : ℕ) (hN : Ab tN = frame (binary W num)) (hD : Ab tD = frame (binary W den))
    (hO : Ab o = []) (hbl : ∀ j, sc j = true → Ab j = []) (hn : num < 2 ^ W) (hd : den < 2 ^ W) (hd0 : 0 < den) :
    Step (machO o tN tD e p1 p2 p3 p4 p5 p6) (2 * nTot p1 p2 p3 p4 p5 p6 W + 2) (fun _ => 0) Ab (fun _ => 0)
        (exitO (machO o tN tD e p1 p2 p3 p4 p5 p6) (fun W => 2 * nTot p1 p2 p3 p4 p5 p6 W + 2) Ab W) ∧
      exitO (machO o tN tD e p1 p2 p3 p4 p5 p6) (fun W => 2 * nTot p1 p2 p3 p4 p5 p6 W + 2) Ab W o =
        ratWord ((num : ℚ) / den) := by
  have hent := entry_of o tN tD e sc Ab W num den hsc hbl hO hN hD
  obtain ⟨τ, hw, hc, hv, ho⟩ := outP_run p1 p2 p3 p4 p5 p6 W num den (entryOf o tN tD e Ab) hent hn hd hd0
  obtain ⟨A', hA', hs', _⟩ := PrimT.C4KW.wm_blankR (capO W) (outP p1 p2 p3 p4 p5 p6) (entryOf o tN tD e Ab) τ _ hw
    (fun _ => rfl) (fun _ => rfl) rfl hc hv
  have hinj := slotsO_inj o tN tD e he hoN hoD hND
  obtain ⟨r, hr, hh, ht, hs⟩ := Block.dockKeep hA' (slotsO o tN tD e) hinj (fun _ => 0) Ab (fun _ => rfl)
    (tin_eq o tN tD e sc Ab hsc hbl)
  have hex : exitO (machO o tN tD e p1 p2 p3 p4 p5 p6) (fun W => 2 * nTot p1 p2 p3 p4 p5 p6 W + 2) Ab W =
      install (slotsO o tN tD e) Ab A' := by
    unfold exitO machO
    rw [hr]
    exact ht
  refine ⟨?_, ?_⟩
  · rw [hex]
    exact ⟨r, hr, hh, ht, hs⟩
  · rw [hex]
    have e0 : slotsO o tN tD e (Fin.castAdd 1 (sTape (nr := nrO) sO)) = o := by
      unfold slotsO; rw [if_pos (by decide)]
    have hi := install_slot (slotsO o tN tD e) hinj Ab A' (Fin.castAdd 1 (sTape (nr := nrO) sO))
    rw [e0] at hi
    rw [hi, hs' sO, ho]

/-- **The assembly**: the six phases give the out machine's target. -/
noncomputable def outOfPhases : OutOfPhases := fun p1 p2 p3 p4 p5 p6 _t o tN tD sc e hsc he hoN hoD hND =>
  { s := (outP p1 p2 p3 p4 p5 p6).toProg.size + 2
    M := machO o tN tD e p1 p2 p3 p4 p5 p6
    cost := fun W => 2 * nTot p1 p2 p3 p4 p5 p6 W + 2
    C := 2 * (p1.C + p2.C + p3.C + p4.C + p5.C + p6.C) + 12
    D := 2
    cost_le := cost_bound p1 p2 p3 p4 p5 p6
    exitA := exitO (machO o tN tD e p1 p2 p3 p4 p5 p6) (fun W => 2 * nTot p1 p2 p3 p4 p5 p6 W + 2)
    run := fun Ab W num den hN hD hO hbl hn hd hd0 =>
      outOf_run p1 p2 p3 p4 p5 p6 o tN tD sc e hsc he hoN hoD hND Ab W num den hN hD hO hbl hn hd hd0 }

def Cout : ℕ := 6620


end NearCubicWires.WireExponent3_5.FinalPass.Out.Gen
