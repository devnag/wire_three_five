import Proof.Wire_3_5.Stage35.Fold

/-!
# The uniform Case-2 XOR fold over a Case-2 source block

Paper v2, §H.5 Case 2 and §H.6: "`f^{⊕t(q)}`" for a copy count given as DATA (the counter word
`CompareMachine.word c`), as the growing XOR schedule requires (one fixed `E^NP` program serves every `q`): `c` rounds
of `Stage35.Fold.worker` on ONE reused bank (`uniformFold_ready`), the scratch erased between rounds and the offset
advanced by the block width `w` (base `CaseTwoAdvance`). The earlier padded-source fold of this proof, at any
`SBlock`.

Paper quantity of the main type (`fold_run`): the accumulator after `c` rounds is the padded XOR power of the request's
unsigned honest proof table, `padCore (xorPower (paddedUnsigned (a.output (S.req ins)) hcb) c) hfit x` (base
`FixedFold.padded_xor`), at every copy count `c` and address `x` with `c·w ≤ |x|`.
-/

set_option autoImplicit false

namespace Stage35.Fold

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open W3.NearCubicWires.RepairSource.Outer3.Case2
open NearCubicWires.WireExponent3_5.Transfer (ready_pad ready_lengths ready_of_root foldLoop foldBody padScratch
  blankScratch scratchCap roundTapes uniformFold_ready)
open NearCubicWires.RecoveryPipeline (padCore)
open NearCubicWires.SourceInterfaces (xorPower)

noncomputable section
variable {a : PointwisePCPPAlgorithm} (S : SBlock a)

/-! ## The scratch tapes -/

/-- The number of scratch tapes: the accumulator block's positions `2 … wtapes` and the five extra scratch tapes. -/
def ks (D : ℕ) : ℕ := (S.wtapes D - 1) + 5

/-- The scratch tapes, in order. -/
def scratch (D : ℕ) (j : Fin (ks S D)) : Fin (tw S D) :=
  if h : j.val < S.wtapes D - 1 then
    ⟨j.val + 2, by have := wtapes_ge S D; show j.val + 2 < S.wtapes D + 1 + 1 + 9; omega⟩
  else ⟨xt S D + 4 + (j.val - (S.wtapes D - 1)), by
    have hj := j.isLt; unfold ks at hj; show _ < xt S D + 9; omega⟩

theorem scratch_val (D : ℕ) (j : Fin (ks S D)) : (scratch S D j).val =
    if j.val < S.wtapes D - 1 then j.val + 2
    else xt S D + 4 + (j.val - (S.wtapes D - 1)) := by
  unfold scratch; split_ifs <;> rfl

theorem scratch_injective (D : ℕ) : Function.Injective (scratch S D) := by
  have hw := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  intro i j h
  have hv := congrArg Fin.val h
  rw [scratch_val, scratch_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- **Which tapes are scratch**: everything but the seven ports. -/
theorem scratch_iff (D : ℕ) (t : Fin (tw S D)) :
    (∃ j, scratch S D j = t) ↔
      (2 ≤ t.val ∧ t.val ≤ S.wtapes D) ∨ xt S D + 4 ≤ t.val := by
  have hw := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  have ht := t.isLt
  constructor
  · rintro ⟨j, rfl⟩
    have hj := j.isLt
    unfold ks at hj
    rw [scratch_val]
    split_ifs <;> omega
  · intro h
    rcases h with h | h
    · refine ⟨⟨t.val - 2, by unfold ks; omega⟩, ?_⟩
      apply Fin.ext
      rw [scratch_val, if_pos (by show t.val - 2 < _; omega)]
      show t.val - 2 + 2 = t.val
      omega
    · refine ⟨⟨(S.wtapes D - 1) + (t.val - (xt S D + 4)), by
        unfold ks; unfold tw at ht; omega⟩, ?_⟩
      apply Fin.ext
      rw [scratch_val, if_neg (by show ¬ (_ + _ < _); omega)]
      show xt S D + 4 + (S.wtapes D - 1 + (t.val - (xt S D + 4)) - (S.wtapes D - 1)) =
        t.val
      omega

section Pad
variable {tw' ks' : ℕ} (sc : Fin ks' → Fin tw') (total : ℕ) (X : Fin tw' → List Bool) (t : Fin tw')

theorem padScratch_port (ht : ¬ ∃ j, sc j = t) : padScratch sc total X t = X t := by
  unfold padScratch scratchCap; rw [if_neg ht, ZeroPadding.pad_zero]
theorem padScratch_scr (ht : ∃ j, sc j = t) : padScratch sc total X t = ZeroPadding.pad total (X t) := by
  unfold padScratch scratchCap; rw [if_pos ht]
theorem blankScratch_port (ht : ¬ ∃ j, sc j = t) : blankScratch sc X t = X t := by
  unfold blankScratch; rw [if_neg ht]
theorem blankScratch_scr (ht : ∃ j, sc j = t) : blankScratch sc X t = [] := by
  unfold blankScratch; rw [if_pos ht]

end Pad

/-! ## The advance -/

/-- The advance's slots: the block width, the offset, and a scratch log (it holds `0^total` after the erase). -/
def advSlots (D : ℕ) : Fin 3 → Fin (tw S D + 2) :=
  ![(ee S D 2).castAdd 2, (ee S D 1).castAdd 2, (ee S D 4).castAdd 2]

theorem advSlots_val (D : ℕ) (i : Fin 3) :
    (advSlots S D i).val = xt S D + (![2, 1, 4] : Fin 3 → ℕ) i := by
  fin_cases i <;> rfl

theorem advSlots_injective (D : ℕ) : Function.Injective (advSlots S D) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [advSlots_val, advSlots_val] at hv
  apply Fin.ext
  revert hv
  fin_cases i <;> fin_cases j <;> simp

/-- **The advance**: the offset `1^{i·w}` becomes `1^{(i+1)·w}` in place (base `CaseTwoAdvance`). -/
def advance (D : ℕ) := RecoveryFocus.machine (advSlots S D) Advance.machine

/-- **The fold**: `c` rounds of the worker on one bank, the copy count read from the counter word. -/
def foldMachine (D : ℕ) :=
  foldLoop (foldBody (worker S D) (scratch S D) (advance S D))

theorem ee_not_scratch' (D : ℕ) (j : Fin 9) (hj : j.val < 4) :
    ¬ ∃ i, scratch S D i = ee S D j := by
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  rw [scratch_iff]
  simp only [ee_val]
  omega

theorem ee4_scratch (D : ℕ) : ∃ i, scratch S D i = ee S D 4 := by
  rw [scratch_iff]; right; show _ ≤ xt S D + 4; omega

/-! ## The fold -/

section Fold
variable (D : ℕ) (ins : S.ι)

/-- The round tapes at blocks `i` and `i+1` agree off the offset and the accumulator. -/
theorem roundIn_succ {N : ℕ} (point : BitInput N) (i total : ℕ) (p p' : Bool) (t : Fin (tw S D))
    (h1 : t.val ≠ xt S D + 1) (h2 : t.val ≠ S.wtapes D + 1) :
    roundIn S D ins point i total p t =
      roundIn S D ins point (i + 1) total p' t := by
  rw [roundIn_val, roundIn_val]
  unfold bankN
  split_ifs <;> rfl

/-- Every round tape fits the bank capacity. -/
theorem roundIn_length_le {N : ℕ} (point : BitInput N) (i total : ℕ) (p : Bool)
    (hh : (S.w0 ins).length ≤ total)
    (hd : (RepairOrdinary.frame (S.d ins)).length ≤ total)
    (ha : (RepairOrdinary.frame (List.ofFn point)).length ≤ total) (hqt : (S.req ins).arity ≤ total)
    (hi : i * widthOf S D ins ≤ total)
    (hw : widthOf S D ins ≤ total) (h1 : 1 ≤ total) (t : Fin (tw S D)) :
    (roundIn S D ins point i total p t).length ≤ total := by
  rw [roundIn_val]
  unfold bankN
  split_ifs <;> (try simp only [ZeroPadding.pad_length, List.length_replicate, List.length_cons, List.length_nil]) <;>
    omega

/-- **The advance is ready**: after the erase, the offset moves from block `i` to block `i+1`; everything else is
already the next round's tapes (the accumulator carries the new parity). -/
theorem advance_run {N : ℕ} (point : BitInput N) (i total capT : ℕ) (p p' : Bool) (out : Fin (tw S D) → List Bool)
    (hbound : widthOf S D ins + i * widthOf S D ins + 2 ≤ total)
    (hee : ∀ j : Fin 4, out (ee S D (j.castAdd 5)) =
      roundIn S D ins point i total p (ee S D (j.castAdd 5)))
    (hxe : ∀ j : Fin (xt S D), j.val < 2 → out (xe S D j) =
      roundIn S D ins point i total p (xe S D j))
    (hacc : out (xe S D (xacc S D)) = [p']) :
    ClockJoin.ReadyRun (advance S D)
      (2 * (widthOf S D ins + i * widthOf S D ins) + 6)
      (roundTapes (padScratch (scratch S D) total (blankScratch (scratch S D) out)) total capT)
      (roundTapes (padScratch (scratch S D) total
        (roundIn S D ins point (i + 1) total p')) total capT) := by
  have hw9 := wtapes_ge S D
  have hxt : xt S D = S.wtapes D + 1 + 1 := rfl
  set w := widthOf S D ins with hw
  set sc := scratch S D with hsc
  set X := padScratch sc total (blankScratch sc out) with hX
  have hA := ready_of_root (Advance.ready w (i * w) total (by omega))
  have f := hA.focus (advSlots S D) (advSlots_injective S D) (roundTapes X total capT) (by
    intro j
    fin_cases j
    · show roundTapes X total capT ((ee S D 2).castAdd 2) = ZeroPadding.pad total (List.replicate w true)
      simp only [roundTapes, Fin.addCases_left]
      rw [hX, padScratch_port _ _ _ _ (ee_not_scratch' S D 2 (by decide)),
        blankScratch_port _ _ _ (ee_not_scratch' S D 2 (by decide))]
      exact (hee 2).trans (roundIn_e2 S D ins point i total p)
    · show roundTapes X total capT ((ee S D 1).castAdd 2) = ZeroPadding.pad total (List.replicate (i * w) true)
      simp only [roundTapes, Fin.addCases_left]
      rw [hX, padScratch_port _ _ _ _ (ee_not_scratch' S D 1 (by decide)),
        blankScratch_port _ _ _ (ee_not_scratch' S D 1 (by decide))]
      exact (hee 1).trans (roundIn_e1 S D ins point i total p)
    · show roundTapes X total capT ((ee S D 4).castAdd 2) = _
      simp only [roundTapes, Fin.addCases_left]
      rw [hX, padScratch_scr _ _ _ _ (ee4_scratch S D),
        blankScratch_scr _ _ _ (ee4_scratch S D)]
      simp [ZeroPadding.pad])
  set Y := padScratch sc total (roundIn S D ins point (i + 1) total p') with hY
  have heq : install (advSlots S D) (roundTapes X total capT)
      ![ZeroPadding.pad total (List.replicate w true), ZeroPadding.pad total (List.replicate (i * w + w) true),
        List.replicate total false] = roundTapes Y total capT := by
    funext t
    refine Fin.addCases (fun x => ?_) (fun y => ?_) t
    · by_cases hx2 : x = ee S D 2
      · rw [hx2, show (ee S D 2).castAdd 2 = advSlots S D 0 from rfl,
          install_slot _ (advSlots_injective S D)]
        show ZeroPadding.pad total (List.replicate w true) = roundTapes Y total capT ((ee S D 2).castAdd 2)
        simp only [roundTapes, Fin.addCases_left]
        rw [hY, padScratch_port _ _ _ _ (ee_not_scratch' S D 2 (by decide))]
        exact (roundIn_e2 S D ins point (i + 1) total p').symm
      by_cases hx1 : x = ee S D 1
      · rw [hx1, show (ee S D 1).castAdd 2 = advSlots S D 1 from rfl,
          install_slot _ (advSlots_injective S D)]
        show ZeroPadding.pad total (List.replicate (i * w + w) true) =
          roundTapes Y total capT ((ee S D 1).castAdd 2)
        simp only [roundTapes, Fin.addCases_left]
        rw [hY, padScratch_port _ _ _ _ (ee_not_scratch' S D 1 (by decide)), roundIn_e1, Nat.succ_mul]
      by_cases hx4 : x = ee S D 4
      · rw [hx4, show (ee S D 4).castAdd 2 = advSlots S D 2 from rfl,
          install_slot _ (advSlots_injective S D)]
        show List.replicate total false = roundTapes Y total capT ((ee S D 4).castAdd 2)
        simp only [roundTapes, Fin.addCases_left]
        rw [hY, padScratch_scr _ _ _ _ (ee4_scratch S D),
          roundIn_other S D ins point (i + 1) total p' _
            (by simp [ee]) (by simp [ee]) (by simp [ee]; omega) (by simp [ee]) (by simp [ee]) (by simp [ee])
            (by simp [ee])]
        simp [ZeroPadding.pad]
      have hxv := x.isLt
      have hne : ∀ j, advSlots S D j ≠ x.castAdd 2 := by
        intro j h
        have hv := congrArg Fin.val h
        rw [advSlots_val] at hv
        simp only [Fin.val_castAdd] at hv
        revert hv
        fin_cases j
        · intro hv; exact hx2 (Fin.ext (by simp [ee] at hv ⊢; omega))
        · intro hv; exact hx1 (Fin.ext (by simp [ee] at hv ⊢; omega))
        · intro hv; exact hx4 (Fin.ext (by simp [ee] at hv ⊢; omega))
      rw [install_other _ _ _ _ hne]
      simp only [roundTapes, Fin.addCases_left]
      by_cases hs : ∃ j, sc j = x
      · rw [hX, hY, padScratch_scr _ _ _ _ hs, blankScratch_scr _ _ _ hs, padScratch_scr _ _ _ _ hs]
        rw [hsc, scratch_iff] at hs
        rw [roundIn_other S D ins point (i + 1) total p' x (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)]
      · rw [hX, hY, padScratch_port _ _ _ _ hs, blankScratch_port _ _ _ hs, padScratch_port _ _ _ _ hs]
        rw [hsc, scratch_iff] at hs
        have hs1 : ¬ (2 ≤ x.val ∧ x.val ≤ S.wtapes D) := fun h => hs (Or.inl h)
        have hs2 : ¬ (xt S D + 4 ≤ x.val) := fun h => hs (Or.inr h)
        have hx1v : x.val ≠ xt S D + 1 := fun h => hx1 (Fin.ext (by simp [ee]; omega))
        by_cases hacc' : x.val = S.wtapes D + 1
        · have he : x = xe S D (xacc S D) := Fin.ext hacc'
          rw [he, hacc, roundIn_val, show (xe S D (xacc S D)).val = S.wtapes D + 1 from rfl,
            bankN_acc]
        rw [← roundIn_succ S D ins point i total p p' x hx1v hacc']
        by_cases hlow : x.val < xt S D
        · have hx2' : x.val < 2 := by omega
          have he : x = xe S D ⟨x.val, hlow⟩ := Fin.ext rfl
          rw [he]
          exact hxe ⟨x.val, hlow⟩ hx2'
        · have h4 : x.val - xt S D < 4 := by omega
          have he : x = ee S D ((⟨x.val - xt S D, h4⟩ : Fin 4).castAdd 5) :=
            Fin.ext (by simp [ee]; omega)
          rw [he]
          exact hee _
    · have hne : ∀ j, advSlots S D j ≠ Fin.natAdd (tw S D) y := by
        intro j h
        have hv := congrArg Fin.val h
        rw [advSlots_val, show (Fin.natAdd (tw S D) y : Fin _).val = tw S D + y.val from rfl] at hv
        have htw : tw S D = xt S D + 9 := rfl
        have hj : (![2, 1, 4] : Fin 3 → ℕ) j ≤ 4 := by fin_cases j <;> decide
        omega
      rw [install_other _ _ _ _ hne]
      simp only [roundTapes, Fin.addCases_right]
  rw [← heq]
  exact ClockJoin.enlarge _ _ _ _ _ f (by omega)

/-- The cost bound of the first `c` rounds. -/
def foldCost {N : ℕ} (point : BitInput N) (c : ℕ) : ℕ :=
  (Finset.range c).sup (roundCost S D ins point)

/-- The bank capacity the fold needs: every port word, the offsets `≤ c·w + 2`, and every round's cost. -/
def foldNeed {N : ℕ} (point : BitInput N) (c : ℕ) : ℕ :=
  max (max (S.w0 ins).length (RepairOrdinary.frame (S.d ins)).length)
    (max (max (RepairOrdinary.frame (List.ofFn point)).length (S.req ins).arity)
      (max (c * widthOf S D ins + 2) (foldCost S D ins point c + 1)))

/-- The fold's step budget. -/
def foldBudget {N : ℕ} (point : BitInput N) (c total : ℕ) : ℕ :=
  1 + 1 + (c * (foldCost S D ins point c + 1 +
    (2 * total + 4 + 1 + (2 * (c * widthOf S D ins) + 6)) + 2) + c + 3 + 1 + 1)

/-- **The uniform fold is ready**: from the round tapes at block `0` with accumulator `false`, `c` rounds (the copy
count read from the counter word) end at the round tapes at block `c` whose accumulator is the padded XOR power of the
padded request's unsigned honest proof table at the address. -/
theorem fold_run (hD : 1 ≤ D) {N : ℕ} (point : BitInput N)
    (hcb : (a.output (S.req ins)).clauseBits ≤
      capOf S D ins)
    (c total capT : ℕ) (hfit : c * widthOf S D ins ≤ N)
    (htotal : foldNeed S D ins point c ≤ total) (hcapT : total + 1 ≤ capT) :
    ClockJoin.ReadyRun (foldMachine S D)
      (foldBudget S D ins point c total)
      (Fin.addCases (roundTapes (padScratch (scratch S D) total
          (roundIn S D ins point 0 total false)) total capT)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c))
      (Fin.addCases (roundTapes (padScratch (scratch S D) total
          (roundIn S D ins point c total
            (padCore (xorPower (CloseoutLanguage.paddedUnsigned (a.output (S.req ins)) hcb)
              c) hfit point))) total capT)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c)) := by
  have hN := htotal
  unfold foldNeed at hN
  set seed := CloseoutLanguage.paddedUnsigned (a.output (S.req ins)) hcb with hseed
  set bit : ℕ → Bool := fun n => seed (AddressWindow.field point (n * (widthOf S D ins)) (widthOf S D ins)) with hbit
  set Q : ℕ → Fin (tw S D) → List Bool :=
    fun i => roundIn S D ins point i total (FixedFold.value bit i) with hQ
  have hround : ∀ i, ∃ out, i < c →
      ClockJoin.ReadyRun (worker S D)
        (roundCost S D ins point i) (Q i) out ∧
      out (xe S D (xacc S D)) = [FixedFold.value bit (i + 1)] ∧
      (∀ j : Fin 4, out (ee S D (j.castAdd 5)) = Q i (ee S D (j.castAdd 5))) ∧
      (∀ j : Fin (xt S D), j.val < 2 → out (xe S D j) = Q i (xe S D j)) := by
    intro i
    by_cases hi : i < c
    · have hfi : (i + 1) * (widthOf S D ins) ≤ N := (Nat.mul_le_mul_right (widthOf S D ins) (show i + 1 ≤ c by omega)).trans hfit
      obtain ⟨out, h1, h2, h3, h4⟩ := round_run S D ins hD point hcb i total
        (FixedFold.value bit i) hfi
      exact ⟨out, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨fun _ => [], fun h => absurd h hi⟩
  choose Q' hQ' using hround
  have hcost : ∀ i, i < c → roundCost S D ins point i ≤
      foldCost S D ins point c :=
    fun i hi => Finset.le_sup (f := roundCost S D ins point) (Finset.mem_range.2 hi)
  have hmain := uniformFold_ready (worker S D)
    (scratch S D) (scratch_injective S D) (advance S D) total capT
    (foldCost S D ins point c) (2 * (c * (widthOf S D ins)) + 6) c hcapT Q Q'
    (fun i hi => ClockJoin.enlarge _ _ _ _ _ (hQ' i hi).1 (hcost i hi))
    (fun i hi j => by
      have hi1 : i * (widthOf S D ins) ≤ total := (Nat.mul_le_mul_right (widthOf S D ins) hi.le).trans (by omega)
      have hw1 : (widthOf S D ins) ≤ total := (Nat.le_mul_of_pos_left (widthOf S D ins) (show 0 < c by omega)).trans (by omega)
      have hl := ready_lengths (hQ' i hi).1 total (roundIn_length_le S D ins point i total
        (FixedFold.value bit i) (by omega) (by omega) (by omega) (by omega) hi1 hw1 (by omega))
        (scratch S D j)
      have := hcost i hi
      omega)
    (fun i hi => by
      have hb : (widthOf S D ins) + i * (widthOf S D ins) + 2 ≤ total := by
        have : (widthOf S D ins) + i * (widthOf S D ins) = (i + 1) * (widthOf S D ins) := by ring
        have := (Nat.mul_le_mul_right (widthOf S D ins) (show i + 1 ≤ c by omega))
        omega
      refine ClockJoin.enlarge _ _ _ _ _ (advance_run S D ins point i total capT
        (FixedFold.value bit i) (FixedFold.value bit (i + 1)) (Q' i) hb (hQ' i hi).2.2.1 (hQ' i hi).2.2.2 (hQ' i hi).2.1)
        ?_
      have : (widthOf S D ins) + i * (widthOf S D ins) ≤ c * (widthOf S D ins) := by
        have := Nat.mul_le_mul_right (widthOf S D ins) (show i + 1 ≤ c by omega)
        have : (widthOf S D ins) + i * (widthOf S D ins) = (i + 1) * (widthOf S D ins) := by ring
        omega
      omega)
  have hmeaning : FixedFold.value bit c = padCore (xorPower seed c) hfit point :=
    FixedFold.padded_xor seed point hfit bit (fun _ => rfl)
  rw [← hmeaning]
  exact hmain

end Fold

end

end Stage35.Fold
