import Proof.Wire_3_5.Primitive.SeedFix.C4KWd

/-! # C4KW, part 5: B4, the framed copies of the HASH tape and the populations

The kept words `3`, `4` are the HASH tape `htWord Fs` and the populations' stream `popsWord pops` (the Hb printer's
streams `2`, `3`); the setup has them raw. A word program reads each by its grammar (every record self-delimiting) and
appends its framed pairs:

* `Cp P x n` (P appends `prs x` while reading `x`), `cp_mono`, `cp_seq`, `cp_copyF`, `cp_copyN`, **`cp_loop`** (a loop
  over records starting with `true`, ended by `false`);
* `cp_frame`, `cp_poly`, `cp_entry`, **`cp_ht`** (the HASH tape), `cp_elem`, `cp_rec`, **`cp_pops`**;
* **`partB4 : PartB4`**.

Paper quantity of the main type: the Hb printer's static streams `htWord Fs`, `popsWord pops` (P3:2253-2290). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

theorem fm_flat {α β : Type} (f : α → List β) (l : List α) : l.flatMap f = (l.map f).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem prs_nil : prs [] = [] := rfl

section Copy
variable {ns nr : ℕ} (cap : ℕ) (S O : Fin (ns + 1))

/-- **`P` copies `x` framed**: from the head of `S` at the start of `x`, it appends `prs x` to `O` (its head at the
end) and moves `S` past `x`, within `n` steps. -/
def Cp (P : WM ns nr) (x : List Bool) (n : ℕ) : Prop :=
  ∀ (σ : WState ns nr) (pre rest : List Bool), σ.st S = pre ++ x ++ rest → σ.sh S = pre.length →
    σ.sh O = (σ.st O).length → WExec cap P σ ((apd σ O (prs x)).seth S (pre.length + x.length)) n

variable {cap S O}

theorem cp_mono {P : WM ns nr} {x : List Bool} {n m : ℕ} (h : Cp cap S O P x n) (hnm : n ≤ m) : Cp cap S O P x m :=
  fun σ pre rest h1 h2 h3 => WExec.mono (h σ pre rest h1 h2 h3) hnm

theorem cp_seq (hSO : S ≠ O) {P Q : WM ns nr} {x y : List Bool} {n m : ℕ} (hP : Cp cap S O P x n)
    (hQ : Cp cap S O Q y m) : Cp cap S O (.seq P Q) (x ++ y) (n + 1 + m) := by
  intro σ pre rest h1 h2 h3
  have t1 := hP σ pre (y ++ rest) (by rw [h1]; simp) h2 h3
  have t2 := hQ ((apd σ O (prs x)).seth S (pre.length + x.length)) (pre ++ x) rest
    (by simp only [WState.seth_st]; rw [apd_st_ne σ O S hSO, h1]; simp)
    (by simp)
    (by simp only [WState.seth_sh, WState.seth_st]; rw [Function.update_of_ne (Ne.symm hSO), apd_sh_d, apd_st_d,
      List.length_append])
  have e : (apd ((apd σ O (prs x)).seth S (pre.length + x.length)) O (prs y)).seth S ((pre ++ x).length + y.length) =
      (apd σ O (prs (x ++ y))).seth S (pre.length + (x ++ y).length) := by
    rw [apd_seth _ S O hSO, seth_seth', apd_apd, prs_append]; congr 1
    simp only [List.length_append]; omega
  rw [e] at t2
  exact WExec.seq t1 t2

/-- Copy the scanned bit framed. -/
def copyF (S O : Fin (ns + 1)) : WM ns nr := .seq (.ifs S (wlist O [true, true]) (wlist O [true, false])) (.fwd S)

theorem cp_copyF (hSO : S ≠ O) (b : Bool) : Cp cap S O (copyF (nr := nr) S O) [b] 11 := by
  intro σ pre rest h1 h2 h3
  have hb : wbit σ S = b := by
    show readTapeBit _ _ = b
    rw [h1, h2]; simp [readTapeBit, List.getD_append_right]
  have tI : WExec cap (.ifs S (wlist O [true, true]) (wlist O [true, false]) : WM ns nr) σ (apd σ O [true, b]) 9 := by
    cases b
    · exact WExec.ifsF hb (wlist_spec cap O [true, false] σ h3)
    · exact WExec.ifsT hb (wlist_spec cap O [true, true] σ h3)
  have tF := WExec.fwd (cap := cap) S (apd σ O [true, b])
  rw [apd_sh_ne σ O S hSO, h2] at tF
  exact WExec.cast cap (WExec.seq tI tF) rfl (by omega)

/-- `k` framed copies. -/
def copyN (S O : Fin (ns + 1)) : ℕ → WM ns nr
  | 0 => .skip
  | k + 1 => .seq (copyF S O) (copyN S O k)

theorem cp_copyN (hSO : S ≠ O) : ∀ (x : List Bool), Cp cap S O (copyN (nr := nr) S O x.length) x (12 * x.length)
  | [] => by
    intro σ pre rest _ h2 h3
    simp only [List.length_nil, Nat.add_zero, Nat.mul_zero]
    rw [prs_nil, apd_nil σ O h3, seth_same σ S _ h2]
    exact WExec.skip σ
  | b :: x => by
    have h := cp_seq hSO (cp_copyF (nr := nr) (cap := cap) hSO b) (cp_copyN hSO x)
    exact cp_mono h (by simp; omega)

/-- **A loop over records** each starting with `true` and copied by `body`, the list ended by a `false`. -/
theorem cp_loop (hSO : S ≠ O) (body : WM ns nr) (a b : ℕ) :
    ∀ (xs : List (List Bool)), (∀ x ∈ xs, Cp cap S O body x (a * x.length + b) ∧ x.head? = some true) →
      ∀ (σ : WState ns nr) (pre r : List Bool), σ.st S = pre ++ xs.flatten ++ false :: r → σ.sh S = pre.length →
        σ.sh O = (σ.st O).length →
        WExec cap (.whs S body) σ ((apd σ O (prs xs.flatten)).seth S (pre.length + xs.flatten.length))
          ((a + b + 2) * xs.flatten.length + 1)
  | [], _, σ, pre, r, h1, h2, h3 => by
    have e : (apd σ O (prs ([] : List (List Bool)).flatten)).seth S (pre.length + ([] : List (List Bool)).flatten.length)
        = σ := by
      simp only [List.flatten_nil, List.length_nil, Nat.add_zero]
      rw [show prs [] = [] from rfl, apd_nil σ O h3]; exact seth_same σ S _ h2
    rw [e]
    refine WExec.cast cap (WExec.whsF ?_) rfl (by simp)
    show readTapeBit _ _ = false
    rw [h1, h2]; simp [readTapeBit, List.getD_append_right]
  | x :: xs, hx, σ, pre, r, h1, h2, h3 => by
    obtain ⟨hc, hh⟩ := hx x List.mem_cons_self
    obtain ⟨y, rfl⟩ : ∃ y, x = true :: y := by
      cases x with
      | nil => simp at hh
      | cons c y => simp at hh; exact ⟨y, by rw [hh]⟩
    have hb : wbit σ S = true := by
      show readTapeBit _ _ = true
      rw [h1, h2]; simp [readTapeBit, List.getD_append_right]
    have t1 := hc σ pre (xs.flatten ++ false :: r) (by rw [h1]; simp) h2 h3
    have ih := cp_loop hSO body a b xs (fun z hz => hx z (List.mem_cons_of_mem _ hz))
      ((apd σ O (prs (true :: y))).seth S (pre.length + (true :: y).length)) (pre ++ true :: y) r
      (by simp only [WState.seth_st]; rw [apd_st_ne σ O S hSO, h1]; simp)
      (by simp)
      (by simp only [WState.seth_sh, WState.seth_st]; rw [Function.update_of_ne (Ne.symm hSO), apd_sh_d, apd_st_d,
        List.length_append])
    have e : (apd ((apd σ O (prs (true :: y))).seth S (pre.length + (true :: y).length)) O (prs xs.flatten)).seth S
        ((pre ++ true :: y).length + xs.flatten.length) =
        (apd σ O (prs ((true :: y) :: xs).flatten)).seth S (pre.length + ((true :: y) :: xs).flatten.length) := by
      rw [apd_seth _ S O hSO, seth_seth', apd_apd, ← prs_append, List.flatten_cons]; congr 1
      simp only [List.length_append, List.length_cons]; omega
    rw [e] at ih
    refine WExec.cast cap (WExec.whsT hb t1 ih) rfl ?_
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have : (a + b + 2) * (y.length + 1 + xs.flatten.length) =
        (a + b + 2) * (y.length + 1) + (a + b + 2) * xs.flatten.length := by ring
    rw [this]
    have : a * (y.length + 1) + b ≤ (a + b) * (y.length + 1) := by nlinarith
    nlinarith

/-- The loop and its terminator. -/
theorem cp_loopT (hSO : S ≠ O) (body : WM ns nr) (a b : ℕ) (xs : List (List Bool))
    (hx : ∀ x ∈ xs, Cp cap S O body x (a * x.length + b) ∧ x.head? = some true) :
    Cp cap S O (.seq (.whs S body) (copyF S O)) (xs.flatten ++ [false]) ((a + b + 2) * (xs.flatten ++ [false]).length + 13) := by
  intro σ pre rest h1 h2 h3
  have t1 := cp_loop hSO body a b xs hx σ pre rest (by rw [h1]; simp) h2 h3
  have t2 := cp_copyF (nr := nr) (cap := cap) hSO false ((apd σ O (prs xs.flatten)).seth S (pre.length + xs.flatten.length))
    (pre ++ xs.flatten) rest (by simp only [WState.seth_st]; rw [apd_st_ne σ O S hSO, h1]; simp) (by simp)
    (by simp only [WState.seth_sh, WState.seth_st]; rw [Function.update_of_ne (Ne.symm hSO), apd_sh_d, apd_st_d,
      List.length_append])
  have e : (apd ((apd σ O (prs xs.flatten)).seth S (pre.length + xs.flatten.length)) O (prs [false])).seth S
      ((pre ++ xs.flatten).length + [false].length) =
      (apd σ O (prs (xs.flatten ++ [false]))).seth S (pre.length + (xs.flatten ++ [false]).length) := by
    rw [apd_seth _ S O hSO, seth_seth', apd_apd, ← prs_append]; congr 1
    simp only [List.length_append, List.length_singleton]; omega
  rw [e] at t2
  refine WExec.cast cap (WExec.seq t1 t2) rfl ?_
  simp only [List.length_append, List.length_singleton]
  nlinarith

/-! ## The HASH tape -/

/-- A frame's framed copy. -/
def frameCopy (S O : Fin (ns + 1)) : WM ns nr := .seq (.whs S (.seq (copyF S O) (copyF S O))) (copyF S O)

theorem frame_flat (y : List Bool) : frame y = (y.map fun b => [true, b]).flatten ++ [false] := by
  rw [frame_prs]; simp [prs, fm_flat]

theorem cp_frame (hSO : S ≠ O) (y : List Bool) :
    Cp cap S O (frameCopy (nr := nr) S O) (frame y) (14 * (frame y).length + 13) := by
  rw [frame_flat]
  have h := cp_loopT (nr := nr) (cap := cap) hSO (.seq (copyF S O) (copyF S O)) 12 0 (y.map fun b => [true, b])
    (fun x hx => by
      obtain ⟨b, _, rfl⟩ := List.mem_map.1 hx
      have hp : Cp cap S O (.seq (copyF (nr := nr) S O) (copyF S O)) ([true] ++ [b]) (11 + 1 + 11) :=
        cp_seq hSO (cp_copyF hSO true) (cp_copyF hSO b)
      exact ⟨cp_mono hp (by simp), rfl⟩)
  exact cp_mono h (by simp)

/-- A polynomial word's framed copy. -/
def polyCopy (S O : Fin (ns + 1)) : WM ns nr := .seq (.whs S (.seq (copyF S O) (frameCopy S O))) (copyF S O)

theorem polyWord_flat (P : List (List ℕ)) : ListMachine.Rec.polyWord P = (P.map ListMachine.Rec.recW).flatten ++ [false] := by
  simp [ListMachine.Rec.polyWord, fm_flat]

theorem cp_poly (hSO : S ≠ O) (P : List (List ℕ)) :
    Cp cap S O (polyCopy (nr := nr) S O) (ListMachine.Rec.polyWord P) (41 * (ListMachine.Rec.polyWord P).length + 13) := by
  rw [polyWord_flat]
  have h := cp_loopT (nr := nr) (cap := cap) hSO (.seq (copyF S O) (frameCopy S O)) 14 25 (P.map ListMachine.Rec.recW)
    (fun x hx => by
      obtain ⟨m, _, rfl⟩ := List.mem_map.1 hx
      refine ⟨?_, rfl⟩
      have h1 := cp_seq hSO (cp_copyF (nr := nr) (cap := cap) hSO true) (cp_frame hSO (ListMachine.Rec.monoBits m))
      have e : [true] ++ frame (ListMachine.Rec.monoBits m) = ListMachine.Rec.recW m := rfl
      rw [e] at h1
      refine cp_mono h1 ?_
      have : (ListMachine.Rec.recW m).length = (frame (ListMachine.Rec.monoBits m)).length + 1 := by
        rw [← e]; simp
      rw [this]; ring_nf; omega)
  exact cp_mono h (by simp)

/-- An entry's framed copy: the head, the polynomial, the three terminators. -/
def entryCopy (S O : Fin (ns + 1)) : WM ns nr := .seq (copyN S O 9) (.seq (polyCopy S O) (copyN S O 3))

theorem cp_entry (hSO : S ≠ O) (P : List (List ℕ)) :
    Cp cap S O (entryCopy (nr := nr) S O) (SeedFix.entryRec [[((1 : ℤ), [P])]]) (41 * (SeedFix.entryRec [[((1 : ℤ), [P])]]).length + 160) := by
  rw [HbM.entry_single]
  have h := cp_seq hSO (cp_copyN (nr := nr) (cap := cap) hSO [true, true, true, true, false, true, true, false, true])
    (cp_seq hSO (cp_poly (nr := nr) (cap := cap) hSO P) (cp_copyN (nr := nr) (cap := cap) hSO [false, false, false]))
  refine cp_mono (by rw [List.append_assoc]; exact h) ?_
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- **The HASH tape's framed copy.** -/
def htCopy (S O : Fin (ns + 1)) : WM ns nr := .seq (.whs S (entryCopy S O)) (copyF S O)

theorem cp_ht (hSO : S ≠ O) (Fs : List (List (List ℕ))) :
    Cp cap S O (htCopy (nr := nr) S O) (HbM.htWord Fs) (203 * (HbM.htWord Fs).length + 13) := by
  have e : HbM.htWord Fs = (Fs.map fun P => SeedFix.entryRec [[((1 : ℤ), [P])]]).flatten ++ [false] := by
    rw [HbM.htWord_eq]; simp [fm_flat]
  rw [e]
  exact cp_loopT (nr := nr) (cap := cap) hSO (entryCopy S O) 41 160 _ (fun x hx => by
    obtain ⟨P, _, rfl⟩ := List.mem_map.1 hx
    exact ⟨cp_entry hSO P, by rw [HbM.entry_single]; rfl⟩)

/-! ## The populations -/

/-- An element's framed copy: its marker, its ones, its terminator. -/
def elemCopy (S O : Fin (ns + 1)) : WM ns nr := .seq (copyF S O) (.seq (.whs S (copyF S O)) (copyF S O))

theorem cp_elem (hSO : S ≠ O) (gi : ℕ) :
    Cp cap S O (elemCopy (nr := nr) S O) (HbM.elemW gi) (13 * (HbM.elemW gi).length + 13) := by
  have hL := cp_loopT (nr := nr) (cap := cap) hSO (copyF S O) 0 11 (List.replicate gi [true])
    (fun x hx => by rw [(List.mem_replicate.1 hx).2]; exact ⟨cp_mono (cp_copyF hSO true) (by simp), rfl⟩)
  rw [show (List.replicate gi [true]).flatten = List.replicate gi true from repW_single gi true] at hL
  have h := cp_seq hSO (cp_copyF (nr := nr) (cap := cap) hSO true) hL
  have e : HbM.elemW gi = [true] ++ (List.replicate gi true ++ [false]) := rfl
  rw [e]
  refine cp_mono h ?_
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

/-- A population record's framed copy: its marker and sign, its elements, its terminator. -/
def recCopy (S O : Fin (ns + 1)) : WM ns nr :=
  .seq (copyF S O) (.seq (copyF S O) (.seq (.whs S (elemCopy S O)) (copyF S O)))

theorem cp_rec (hSO : S ≠ O) (pop : Bool × List ℕ) :
    Cp cap S O (recCopy (nr := nr) S O) (HbM.popRec pop) (28 * (HbM.popRec pop).length + 40) := by
  have e : HbM.popRec pop = [true] ++ ([pop.1] ++ ((pop.2.map HbM.elemW).flatten ++ [false])) := by
    simp [HbM.popRec, fm_flat]
  rw [e]
  have hL := cp_loopT (nr := nr) (cap := cap) hSO (elemCopy S O) 13 13 (pop.2.map HbM.elemW) (fun x hx => by
    obtain ⟨gi, _, rfl⟩ := List.mem_map.1 hx
    exact ⟨cp_elem hSO gi, rfl⟩)
  have h := cp_seq hSO (cp_copyF (nr := nr) (cap := cap) hSO true) (cp_seq hSO (cp_copyF (nr := nr) (cap := cap) hSO pop.1) hL)
  refine cp_mono h ?_
  simp only [List.length_append, List.length_singleton]
  omega

/-- **The populations' framed copy.** -/
def popsCopy (S O : Fin (ns + 1)) : WM ns nr := .seq (.whs S (recCopy S O)) (copyF S O)

theorem cp_pops (hSO : S ≠ O) (pops : List (Bool × List ℕ)) :
    Cp cap S O (popsCopy (nr := nr) S O) (HbM.popsWord pops) (70 * (HbM.popsWord pops).length + 13) := by
  have e : HbM.popsWord pops = (pops.map HbM.popRec).flatten ++ [false] := by
    simp [HbM.popsWord, fm_flat]
  rw [e]
  exact cp_loopT (nr := nr) (cap := cap) hSO (recCopy S O) 28 40 _ (fun x hx => by
    obtain ⟨pop, _, rfl⟩ := List.mem_map.1 hx
    exact ⟨cp_rec hSO pop, rfl⟩)

end Copy

end NearCubicWires.WireExponent3_5.PrimT.C4KW
