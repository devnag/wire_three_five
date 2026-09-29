import Proof.Wire_3_5.Primitive.SeedFix.C4HfH

/-! # The HASH child family, part 9: the Hb unit's run

`filt:soft`, P3:2253-2290: **`unit_step`**: from the kept framed words `hb0` (at `0, 0`) and the framed prefix `p`, the
Hb unit leaves on its output tape `95` the expression word `exprWord (hV D (p ++ [b]))` of the printed conditional
objective at the child prefix, the kept words and the prefix unchanged, given the printer conditions at the child.

Paper quantity of the main type: the printed conditional objective `V_{p ++ [b]}` as the expression word. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-- The unit's step count at the child prefix `p ++ [b]` and the printer's cell bound `Kc`. -/
def unitCost (D : HashData) (c : HbCaps) (Kc : ℕ) (p : List Bool) (b : Bool) : ℕ :=
  (2 * prepCost (hb0 (hbX D c 0 0)) p + 2) + 1 +
    (((hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).n * (Kc + 2) + 1) + 1 +
      (2 * (5 * (ListMachine.Rec.exprWord (hV D (p ++ [b]))).length + 3) + 2))

theorem stepMono {t s : ℕ} {p : Machine t s} {n m : ℕ} {hin hout : Fin t → ℕ} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (hle : n ≤ m) : Step p m hin tin hout tout := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact ⟨r, RepairOrdinary.runFrom_moreFuel p n e _ r hr, hh, ht, by omega⟩

theorem out_word (D : HashData) (p : List Bool) (b : Bool) (x : List Bool)
    (hx : x = (HashB.hashTermsM D.MP D.G D.N D.nE D.Fs D.pops (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).flatMap
      (fun t => true :: ListMachine.Rec.termWord t)) :
    x ++ [false] = ListMachine.Rec.exprWord (hV D (p ++ [b])) := by
  rw [hx]; rfl

/-- **The Hb unit's run.** -/
theorem unit_step (D : HashData) (c : HbCaps) (Kc : ℕ) (p : List Bool) (b : Bool)
    (hplen : p.length + 1 ≤ 2 * D.MP.t * D.MP.ell0) (hcC : 2 * D.MP.t * D.MP.ell0 ≤ c.cC)
    (hok : (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).HbOk)
    (hcell : ∀ cc < (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).n,
      (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).CellOk cc)
    (hK : ∀ cc < (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).n,
      (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).cellCost cc ≤ Kc) :
    ∃ Au : Fin HU → List Bool, Step (unitM b) (unitCost D c Kc p b) (fun _ => 0) (uIn (hb0 (hbX D c 0 0)) p)
      (fun _ => 0) Au ∧ Au ⟨95, by rw [HU_eq]; omega⟩ = ListMachine.Rec.exprWord (hV D (p ++ [b])) ∧
      ∀ u : Fin HU, u.val < 95 → Au u = uIn (hb0 (hbX D c 0 0)) p u := by
  set KW := hb0 (hbX D c 0 0) with hKW
  set X' := hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b])) with hX'
  -- 1: the prep
  obtain ⟨τ, hw, hW, hlow⟩ := prep_spec (p.length + 3) D c p b hplen hcC (by omega)
  obtain ⟨A1, s1, hA1⟩ := C4Pipe.wm_blank (p.length + 3) (prepCost KW p) (prepW b) (prepIn KW p) τ (prepCost KW p) hw
    (fun _ => rfl) (fun _ => rfl) rfl le_rfl
  have sd1 := s1.dock prepSl prepSl_inj (fun _ => 0) (uIn KW p) (fun _ => rfl) (prep_entry KW p)
  rw [C4Pipe.dockH_zero'] at sd1
  set B1 := install prepSl (uIn KW p) A1 with hB1
  have hB1w : ∀ j, B1 (hbSl j) = hb0 X' j := by
    intro j
    have e : hbSl j = prepSl (Fin.castAdd 1 (sTape (ns := 188) (nr := 2) (wS j))) := by
      apply Fin.ext
      rw [prepSl_val]
      simp [hbSl, sTape, wS]
      omega
    rw [e, hB1, install_slot _ prepSl_inj, hA1, hW]
  have hB1low : ∀ u : Fin HU, u.val < 95 → B1 u = uIn KW p u := by
    intro u hu
    have e : u = prepSl (Fin.castAdd 1 (sTape (ns := 188) (nr := 2) (⟨u.val, by omega⟩ : Fin (188 + 1)))) := by
      apply Fin.ext
      rw [prepSl_val]
      by_cases h0 : u.val = 0
      · simp [sTape, h0]
      · simp [sTape, h0]; omega
    have h1 := hlow ⟨u.val, by omega⟩ hu
    calc B1 u = B1 (prepSl (Fin.castAdd 1 (sTape (ns := 188) (nr := 2) (⟨u.val, by omega⟩ : Fin (188 + 1))))) := by rw [← e]
      _ = τ.st ⟨u.val, by omega⟩ := by rw [hB1, install_slot _ prepSl_inj, hA1]
      _ = uIn KW p u := by rw [h1]; rfl
  have hB1hi : ∀ u : Fin HU, 193 ≤ u.val → B1 u = [] := by
    intro u hu
    rw [hB1, install_other _ _ _ _ (fun t e => by
      have hv := congrArg Fin.val e; rw [prepSl_val] at hv; have := t.isLt; split_ifs at hv <;> omega)]
    simp only [uIn]
    rw [dif_neg (by omega), if_neg (by omega)]
  -- 2: the printer
  have hM : Matches X' D.MP D.G D.N D.nE D.Fs D.pops (p ++ [b]).length (SeedFix.listNum (p ++ [b])) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨A2, s2, hinv, hout⟩ := hbMachine_spec X' D.MP D.G D.N D.nE D.Fs D.pops _ _ hM hok hcell Kc hK (hb0 X')
    (hb0_inv X')
  have sd2 := s2.dock hbSl hbSl_inj (fun _ => 0) B1 (fun _ => rfl) hB1w
  rw [C4Pipe.dockH_zero'] at sd2
  set B2 := install hbSl B1 A2 with hB2
  obtain ⟨st, R, O, W, P, g, v, hA2, -, hSt, -, -⟩ := hinv
  set x := X'.outAt X'.n with hx
  have a0 : A2 ⟨0, by omega⟩ = x := by
    rw [hA2, hbBank_lt _ _ _ _ 0 (by omega)]
    exact hSt.out
  have a2 : A2 ⟨2, by omega⟩ = List.replicate x.length true := by
    rw [hA2, hbBank_lt _ _ _ _ 2 (by omega)]
    exact hSt.olen
  -- 3: the terminator
  obtain ⟨τa, ha, hta⟩ := app_spec 0 x
  obtain ⟨A3, s3, hA3⟩ := C4Pipe.wm_blank 0 (5 * x.length + 3) appW (apSt x 0) τa (5 * x.length + 3) ha
    (fun _ => rfl) (fun r => r.elim0) rfl le_rfl
  have hentry : ∀ t, B2 (appSl t) = Fin.addCases (m := 1 + 2 + 0) (n := 1) (C4Pipe.wblank (apSt x 0))
      (fun _ : Fin 1 => []) t := by
    intro t
    have hBt : ∀ u : Fin HU, 193 ≤ u.val → B2 u = [] := by
      intro u hu
      rw [hB2, install_other _ _ _ _ (fun j e => by have hv := congrArg Fin.val e; simp [hbSl] at hv; omega)]
      exact hB1hi u hu
    fin_cases t
    · show B2 (hbSl ⟨0, by omega⟩) = x
      rw [hB2, install_slot _ hbSl_inj, a0]
    · show B2 ⟨193, _⟩ = []
      exact hBt _ (by simp)
    · show B2 (hbSl ⟨2, by omega⟩) = List.replicate x.length true
      rw [hB2, install_slot _ hbSl_inj, a2]
    · show B2 ⟨194, _⟩ = []
      exact hBt _ (by simp)
  have sd3 := s3.dock appSl appSl_inj (fun _ => 0) B2 (fun _ => rfl) hentry
  rw [C4Pipe.dockH_zero'] at sd3
  have hlenx : (ListMachine.Rec.exprWord (hV D (p ++ [b]))).length = x.length + 1 := by
    rw [← out_word D p b x hout]; simp
  refine ⟨_, stepMono (Step.seq sd1 (Step.seq sd2 sd3)) (by unfold unitCost; rw [hlenx, ← hKW, ← hX']; omega), ?_, ?_⟩
  · have e : (⟨95, by rw [HU_eq]; omega⟩ : Fin HU) = appSl (Fin.castAdd 1 (sTape (ns := 1) (nr := 0) 0)) := rfl
    rw [e, install_slot _ appSl_inj, hA3, hta]
    exact out_word D p b x hout
  · intro u hu
    rw [install_other _ _ _ _ (fun t e => by
      have hv := congrArg Fin.val e; simp only [appSl] at hv; split_ifs at hv <;> omega)]
    rw [hB2, install_other _ _ _ _ (fun j e => by have hv := congrArg Fin.val e; simp [hbSl] at hv; omega)]
    exact hB1low u hu

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
