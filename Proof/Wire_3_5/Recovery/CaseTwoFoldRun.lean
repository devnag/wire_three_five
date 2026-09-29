import Proof.Wire_3_5.Recovery.CaseTwoFold

/-! # The uniform Case-2 XOR fold at the padded request (P3:3729-3733, 3818-3822; D1.6 A2)

Realizes "`f^{⊕t(q)}`" (P3:3732-3733) of the hybrid Case 2 for a copy count given as DATA (the counter word
`CompareMachine.word c`), as the paper's growing schedule requires ("the least `t` with `e_t ≤ L^{−τ}`",
P3:3818-3822; one fixed `E^NP` program serves every `q`, P3:3758-3759): `c` rounds of `Proof.Wire_3_5.Recovery.CaseTwoFold`'s
worker on ONE reused bank (`uniformFold_ready`), the scratch erased between rounds and the offset advanced by
the block width `w` (base `CaseTwoAdvance`).

Paper quantity of the main type (`fold_run`): the accumulator after `c` rounds is the padded XOR power of the padded
request's unsigned honest proof table, `padCore (xorPower (paddedUnsigned (a.output req) hcb) c) hfit x` (base
`FixedFold.padded_xor`), at every copy count `c` and address `x` with `c·w ≤ |x|`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
open NearCubicWires.RecoveryPipeline (padCore)

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

/-! ## The scratch tapes -/

/-- The number of scratch tapes: the accumulator block's positions `2 … wtapes` and the five extra scratch tapes. -/
def ks (k D : ℕ) : ℕ := (wtapes source a k D - 1) + 5

/-- The scratch tapes, in order. -/
def scratch (k D : ℕ) (j : Fin (ks source a k D)) : Fin (tw source a k D) :=
  if h : j.val < wtapes source a k D - 1 then
    ⟨j.val + 2, by have := wtapes_ge source a k D; show j.val + 2 < wtapes source a k D + 1 + 1 + 9; omega⟩
  else ⟨xt source a k D + 4 + (j.val - (wtapes source a k D - 1)), by
    have hj := j.isLt; unfold ks at hj; show _ < xt source a k D + 9; omega⟩

theorem scratch_val (k D : ℕ) (j : Fin (ks source a k D)) : (scratch source a k D j).val =
    if j.val < wtapes source a k D - 1 then j.val + 2
    else xt source a k D + 4 + (j.val - (wtapes source a k D - 1)) := by
  unfold scratch; split_ifs <;> rfl

theorem scratch_injective (k D : ℕ) : Function.Injective (scratch source a k D) := by
  have hw := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  intro i j h
  have hv := congrArg Fin.val h
  rw [scratch_val, scratch_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- **Which tapes are scratch**: everything but the seven ports. -/
theorem scratch_iff (k D : ℕ) (t : Fin (tw source a k D)) :
    (∃ j, scratch source a k D j = t) ↔
      (2 ≤ t.val ∧ t.val ≤ wtapes source a k D) ∨ xt source a k D + 4 ≤ t.val := by
  have hw := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
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
    · refine ⟨⟨(wtapes source a k D - 1) + (t.val - (xt source a k D + 4)), by
        unfold ks; unfold tw at ht; omega⟩, ?_⟩
      apply Fin.ext
      rw [scratch_val, if_neg (by show ¬ (_ + _ < _); omega)]
      show xt source a k D + 4 + (wtapes source a k D - 1 + (t.val - (xt source a k D + 4)) - (wtapes source a k D - 1)) =
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
def advSlots (k D : ℕ) : Fin 3 → Fin (tw source a k D + 2) :=
  ![(ee source a k D 2).castAdd 2, (ee source a k D 1).castAdd 2, (ee source a k D 4).castAdd 2]

theorem advSlots_val (k D : ℕ) (i : Fin 3) :
    (advSlots source a k D i).val = xt source a k D + (![2, 1, 4] : Fin 3 → ℕ) i := by
  fin_cases i <;> rfl

theorem advSlots_injective (k D : ℕ) : Function.Injective (advSlots source a k D) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [advSlots_val, advSlots_val] at hv
  apply Fin.ext
  revert hv
  fin_cases i <;> fin_cases j <;> simp

/-- **The advance**: the offset `1^{i·w}` becomes `1^{(i+1)·w}` in place (base `CaseTwoAdvance`). -/
def advance (k D : ℕ) := RecoveryFocus.machine (advSlots source a k D) Advance.machine

/-- **The fold**: `c` rounds of the worker on one bank, the copy count read from the counter word. -/
def foldMachine (k D CH Cpad : ℕ) (code : List Bool) :=
  foldLoop (foldBody (worker source a k D CH Cpad code) (scratch source a k D) (advance source a k D))

theorem ee_not_scratch' (k D : ℕ) (j : Fin 9) (hj : j.val < 4) :
    ¬ ∃ i, scratch source a k D i = ee source a k D j := by
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  rw [scratch_iff]
  simp only [ee_val]
  omega

theorem ee4_scratch (k D : ℕ) : ∃ i, scratch source a k D i = ee source a k D 4 := by
  rw [scratch_iff]; right; show _ ≤ xt source a k D + 4; omega

/-! ## The fold -/

section Fold
variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
  (oracle : BooleanCircuit
    (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
  (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
  (D : ℕ)

/-- The round tapes at blocks `i` and `i+1` agree off the offset and the accumulator. -/
theorem roundIn_succ {N : ℕ} (point : BitInput N) (i total : ℕ) (p p' : Bool) (t : Fin (tw source a k D))
    (h1 : t.val ≠ xt source a k D + 1) (h2 : t.val ≠ wtapes source a k D + 1) :
    roundIn source a H Cpad hpad r oracle q hq D point i total p t =
      roundIn source a H Cpad hpad r oracle q hq D point (i + 1) total p' t := by
  rw [roundIn_val, roundIn_val]
  unfold bankN
  split_ifs <;> rfl

/-- Every round tape fits the bank capacity. -/
theorem roundIn_length_le {N : ℕ} (point : BitInput N) (i total : ℕ) (p : Bool)
    (hh : (RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r)).length ≤ total)
    (hd : (RepairOrdinary.frame (PCPPNative.descriptor oracle)).length ≤ total)
    (ha : (RepairOrdinary.frame (List.ofFn point)).length ≤ total) (hqt : q ≤ total)
    (hi : i * widthOf source a H Cpad hpad r oracle q hq D ≤ total)
    (hw : widthOf source a H Cpad hpad r oracle q hq D ≤ total) (h1 : 1 ≤ total) (t : Fin (tw source a k D)) :
    (roundIn source a H Cpad hpad r oracle q hq D point i total p t).length ≤ total := by
  rw [roundIn_val]
  unfold bankN
  split_ifs <;> (try simp only [ZeroPadding.pad_length, List.length_replicate, List.length_cons, List.length_nil]) <;>
    omega

/-- **The advance is ready**: after the erase, the offset moves from block `i` to block `i+1`; everything else is
already the next round's tapes (the accumulator carries the new parity). -/
theorem advance_run {N : ℕ} (point : BitInput N) (i total capT : ℕ) (p p' : Bool) (out : Fin (tw source a k D) → List Bool)
    (hbound : widthOf source a H Cpad hpad r oracle q hq D + i * widthOf source a H Cpad hpad r oracle q hq D + 2 ≤ total)
    (hee : ∀ j : Fin 4, out (ee source a k D (j.castAdd 5)) =
      roundIn source a H Cpad hpad r oracle q hq D point i total p (ee source a k D (j.castAdd 5)))
    (hxe : ∀ j : Fin (xt source a k D), j.val < 2 → out (xe source a k D j) =
      roundIn source a H Cpad hpad r oracle q hq D point i total p (xe source a k D j))
    (hacc : out (xe source a k D (xacc source a k D)) = [p']) :
    ClockJoin.ReadyRun (advance source a k D)
      (2 * (widthOf source a H Cpad hpad r oracle q hq D + i * widthOf source a H Cpad hpad r oracle q hq D) + 6)
      (roundTapes (padScratch (scratch source a k D) total (blankScratch (scratch source a k D) out)) total capT)
      (roundTapes (padScratch (scratch source a k D) total
        (roundIn source a H Cpad hpad r oracle q hq D point (i + 1) total p')) total capT) := by
  have hw9 := wtapes_ge source a k D
  have hxt : xt source a k D = wtapes source a k D + 1 + 1 := rfl
  set w := widthOf source a H Cpad hpad r oracle q hq D with hw
  set sc := scratch source a k D with hsc
  set X := padScratch sc total (blankScratch sc out) with hX
  have hA := ready_of_root (Advance.ready w (i * w) total (by omega))
  have f := hA.focus (advSlots source a k D) (advSlots_injective source a k D) (roundTapes X total capT) (by
    intro j
    fin_cases j
    · show roundTapes X total capT ((ee source a k D 2).castAdd 2) = ZeroPadding.pad total (List.replicate w true)
      simp only [roundTapes, Fin.addCases_left]
      rw [hX, padScratch_port _ _ _ _ (ee_not_scratch' source a k D 2 (by decide)),
        blankScratch_port _ _ _ (ee_not_scratch' source a k D 2 (by decide))]
      exact (hee 2).trans (roundIn_e2 source a H Cpad hpad r oracle q hq D point i total p)
    · show roundTapes X total capT ((ee source a k D 1).castAdd 2) = ZeroPadding.pad total (List.replicate (i * w) true)
      simp only [roundTapes, Fin.addCases_left]
      rw [hX, padScratch_port _ _ _ _ (ee_not_scratch' source a k D 1 (by decide)),
        blankScratch_port _ _ _ (ee_not_scratch' source a k D 1 (by decide))]
      exact (hee 1).trans (roundIn_e1 source a H Cpad hpad r oracle q hq D point i total p)
    · show roundTapes X total capT ((ee source a k D 4).castAdd 2) = _
      simp only [roundTapes, Fin.addCases_left]
      rw [hX, padScratch_scr _ _ _ _ (ee4_scratch source a k D),
        blankScratch_scr _ _ _ (ee4_scratch source a k D)]
      simp [ZeroPadding.pad])
  set Y := padScratch sc total (roundIn source a H Cpad hpad r oracle q hq D point (i + 1) total p') with hY
  have heq : install (advSlots source a k D) (roundTapes X total capT)
      ![ZeroPadding.pad total (List.replicate w true), ZeroPadding.pad total (List.replicate (i * w + w) true),
        List.replicate total false] = roundTapes Y total capT := by
    funext t
    refine Fin.addCases (fun x => ?_) (fun y => ?_) t
    · by_cases hx2 : x = ee source a k D 2
      · rw [hx2, show (ee source a k D 2).castAdd 2 = advSlots source a k D 0 from rfl,
          install_slot _ (advSlots_injective source a k D)]
        show ZeroPadding.pad total (List.replicate w true) = roundTapes Y total capT ((ee source a k D 2).castAdd 2)
        simp only [roundTapes, Fin.addCases_left]
        rw [hY, padScratch_port _ _ _ _ (ee_not_scratch' source a k D 2 (by decide))]
        exact (roundIn_e2 source a H Cpad hpad r oracle q hq D point (i + 1) total p').symm
      by_cases hx1 : x = ee source a k D 1
      · rw [hx1, show (ee source a k D 1).castAdd 2 = advSlots source a k D 1 from rfl,
          install_slot _ (advSlots_injective source a k D)]
        show ZeroPadding.pad total (List.replicate (i * w + w) true) =
          roundTapes Y total capT ((ee source a k D 1).castAdd 2)
        simp only [roundTapes, Fin.addCases_left]
        rw [hY, padScratch_port _ _ _ _ (ee_not_scratch' source a k D 1 (by decide)), roundIn_e1, Nat.succ_mul]
      by_cases hx4 : x = ee source a k D 4
      · rw [hx4, show (ee source a k D 4).castAdd 2 = advSlots source a k D 2 from rfl,
          install_slot _ (advSlots_injective source a k D)]
        show List.replicate total false = roundTapes Y total capT ((ee source a k D 4).castAdd 2)
        simp only [roundTapes, Fin.addCases_left]
        rw [hY, padScratch_scr _ _ _ _ (ee4_scratch source a k D),
          roundIn_other source a H Cpad hpad r oracle q hq D point (i + 1) total p' _
            (by simp [ee]) (by simp [ee]) (by simp [ee]; omega) (by simp [ee]) (by simp [ee]) (by simp [ee])
            (by simp [ee])]
        simp [ZeroPadding.pad]
      have hxv := x.isLt
      have hne : ∀ j, advSlots source a k D j ≠ x.castAdd 2 := by
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
        rw [roundIn_other source a H Cpad hpad r oracle q hq D point (i + 1) total p' x (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)]
      · rw [hX, hY, padScratch_port _ _ _ _ hs, blankScratch_port _ _ _ hs, padScratch_port _ _ _ _ hs]
        rw [hsc, scratch_iff] at hs
        have hs1 : ¬ (2 ≤ x.val ∧ x.val ≤ wtapes source a k D) := fun h => hs (Or.inl h)
        have hs2 : ¬ (xt source a k D + 4 ≤ x.val) := fun h => hs (Or.inr h)
        have hx1v : x.val ≠ xt source a k D + 1 := fun h => hx1 (Fin.ext (by simp [ee]; omega))
        by_cases hacc' : x.val = wtapes source a k D + 1
        · have he : x = xe source a k D (xacc source a k D) := Fin.ext (by simp [xe, xacc]; omega)
          rw [he, hacc, roundIn_val, show (xe source a k D (xacc source a k D)).val = wtapes source a k D + 1 from rfl,
            bankN_acc]
        rw [← roundIn_succ source a H Cpad hpad r oracle q hq D point i total p p' x hx1v hacc']
        by_cases hlow : x.val < xt source a k D
        · have hx2' : x.val < 2 := by omega
          have he : x = xe source a k D ⟨x.val, hlow⟩ := Fin.ext rfl
          rw [he]
          exact hxe ⟨x.val, hlow⟩ hx2'
        · have h4 : x.val - xt source a k D < 4 := by omega
          have he : x = ee source a k D ((⟨x.val - xt source a k D, h4⟩ : Fin 4).castAdd 5) :=
            Fin.ext (by simp [ee]; omega)
          rw [he]
          exact hee _
    · have hne : ∀ j, advSlots source a k D j ≠ Fin.natAdd (tw source a k D) y := by
        intro j h
        have hv := congrArg Fin.val h
        rw [advSlots_val, show (Fin.natAdd (tw source a k D) y : Fin _).val = tw source a k D + y.val from rfl] at hv
        have htw : tw source a k D = xt source a k D + 9 := rfl
        have hj : (![2, 1, 4] : Fin 3 → ℕ) j ≤ 4 := by fin_cases j <;> decide
        omega
      rw [install_other _ _ _ _ hne]
      simp only [roundTapes, Fin.addCases_right]
  rw [← heq]
  exact ClockJoin.enlarge _ _ _ _ _ f (by omega)

/-- The cost bound of the first `c` rounds. -/
def foldCost {N : ℕ} (point : BitInput N) (c : ℕ) : ℕ :=
  (Finset.range c).sup (CaseTwoFold.roundCost source a H Cpad hpad r oracle q hq D point)

/-- The bank capacity the fold needs: every port word, the offsets `≤ c·w + 2`, and every round's cost. -/
def foldNeed {N : ℕ} (point : BitInput N) (c : ℕ) : ℕ :=
  max (max (RepairOrdinary.frame (HierarchySourceInput.hierarchyInput H r)).length
      (RepairOrdinary.frame (PCPPNative.descriptor oracle)).length)
    (max (max (RepairOrdinary.frame (List.ofFn point)).length q)
      (max (c * widthOf source a H Cpad hpad r oracle q hq D + 2) (foldCost source a H Cpad hpad r oracle q hq D point c + 1)))

/-- The fold's step budget. -/
def foldBudget {N : ℕ} (point : BitInput N) (c total : ℕ) : ℕ :=
  1 + 1 + (c * (foldCost source a H Cpad hpad r oracle q hq D point c + 1 +
    (2 * total + 4 + 1 + (2 * (c * widthOf source a H Cpad hpad r oracle q hq D) + 6)) + 2) + c + 3 + 1 + 1)

/-- **The uniform fold is ready**: from the round tapes at block `0` with accumulator `false`, `c` rounds (the copy
count read from the counter word) end at the round tapes at block `c` whose accumulator is the padded XOR power of the
padded request's unsigned honest proof table at the address. -/
theorem fold_run (hcoeff : H.coefficient ≤ Cpad) (hD : 1 ≤ D) {N : ℕ} (point : BitInput N)
    (hcb : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
      capOf source a H Cpad hpad r oracle q hq D)
    (c total capT : ℕ) (hfit : c * widthOf source a H Cpad hpad r oracle q hq D ≤ N)
    (htotal : foldNeed source a H Cpad hpad r oracle q hq D point c ≤ total) (hcapT : total + 1 ≤ capT) :
    ClockJoin.ReadyRun (foldMachine source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
      (foldBudget source a H Cpad hpad r oracle q hq D point c total)
      (Fin.addCases (roundTapes (padScratch (scratch source a k D) total
          (roundIn source a H Cpad hpad r oracle q hq D point 0 total false)) total capT)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c))
      (Fin.addCases (roundTapes (padScratch (scratch source a k D) total
          (roundIn source a H Cpad hpad r oracle q hq D point c total
            (padCore (xorPower (CloseoutLanguage.paddedUnsigned (a.output (wrequest source a H Cpad hpad r oracle q hq)) hcb)
              c) hfit point))) total capT)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word c)) := by
  have hN := htotal
  unfold foldNeed at hN
  set seed := CloseoutLanguage.paddedUnsigned (a.output (wrequest source a H Cpad hpad r oracle q hq)) hcb with hseed
  set bit : ℕ → Bool := fun n => seed (AddressWindow.field point (n * (widthOf source a H Cpad hpad r oracle q hq D)) (widthOf source a H Cpad hpad r oracle q hq D)) with hbit
  set Q : ℕ → Fin (tw source a k D) → List Bool :=
    fun i => roundIn source a H Cpad hpad r oracle q hq D point i total (FixedFold.value bit i) with hQ
  have hround : ∀ i, ∃ out, i < c →
      ClockJoin.ReadyRun (worker source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
        (CaseTwoFold.roundCost source a H Cpad hpad r oracle q hq D point i) (Q i) out ∧
      out (xe source a k D (xacc source a k D)) = [FixedFold.value bit (i + 1)] ∧
      (∀ j : Fin 4, out (ee source a k D (j.castAdd 5)) = Q i (ee source a k D (j.castAdd 5))) ∧
      (∀ j : Fin (xt source a k D), j.val < 2 → out (xe source a k D j) = Q i (xe source a k D j)) := by
    intro i
    by_cases hi : i < c
    · have hfi : (i + 1) * (widthOf source a H Cpad hpad r oracle q hq D) ≤ N := (Nat.mul_le_mul_right (widthOf source a H Cpad hpad r oracle q hq D) (show i + 1 ≤ c by omega)).trans hfit
      obtain ⟨out, h1, h2, h3, h4⟩ := round_run source a H Cpad hpad r oracle q hq D hcoeff hD point hcb i total
        (FixedFold.value bit i) hfi
      exact ⟨out, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨fun _ => [], fun h => absurd h hi⟩
  choose Q' hQ' using hround
  have hcost : ∀ i, i < c → CaseTwoFold.roundCost source a H Cpad hpad r oracle q hq D point i ≤
      foldCost source a H Cpad hpad r oracle q hq D point c :=
    fun i hi => Finset.le_sup (f := CaseTwoFold.roundCost source a H Cpad hpad r oracle q hq D point) (Finset.mem_range.2 hi)
  have hmain := uniformFold_ready (worker source a k D H.coefficient Cpad (VerifierEncoding.code H.verifier))
    (scratch source a k D) (scratch_injective source a k D) (advance source a k D) total capT
    (foldCost source a H Cpad hpad r oracle q hq D point c) (2 * (c * (widthOf source a H Cpad hpad r oracle q hq D)) + 6) c hcapT Q Q'
    (fun i hi => ClockJoin.enlarge _ _ _ _ _ (hQ' i hi).1 (hcost i hi))
    (fun i hi j => by
      have hi1 : i * (widthOf source a H Cpad hpad r oracle q hq D) ≤ total := (Nat.mul_le_mul_right (widthOf source a H Cpad hpad r oracle q hq D) hi.le).trans (by omega)
      have hw1 : (widthOf source a H Cpad hpad r oracle q hq D) ≤ total := (Nat.le_mul_of_pos_left (widthOf source a H Cpad hpad r oracle q hq D) (show 0 < c by omega)).trans (by omega)
      have hl := ready_lengths (hQ' i hi).1 total (roundIn_length_le source a H Cpad hpad r oracle q hq D point i total
        (FixedFold.value bit i) (by omega) (by omega) (by omega) (by omega) hi1 hw1 (by omega))
        (scratch source a k D j)
      have := hcost i hi
      omega)
    (fun i hi => by
      have hb : (widthOf source a H Cpad hpad r oracle q hq D) + i * (widthOf source a H Cpad hpad r oracle q hq D) + 2 ≤ total := by
        have : (widthOf source a H Cpad hpad r oracle q hq D) + i * (widthOf source a H Cpad hpad r oracle q hq D) = (i + 1) * (widthOf source a H Cpad hpad r oracle q hq D) := by ring
        have := (Nat.mul_le_mul_right (widthOf source a H Cpad hpad r oracle q hq D) (show i + 1 ≤ c by omega))
        omega
      refine ClockJoin.enlarge _ _ _ _ _ (advance_run source a H Cpad hpad r oracle q hq D point i total capT
        (FixedFold.value bit i) (FixedFold.value bit (i + 1)) (Q' i) hb (hQ' i hi).2.2.1 (hQ' i hi).2.2.2 (hQ' i hi).2.1)
        ?_
      have : (widthOf source a H Cpad hpad r oracle q hq D) + i * (widthOf source a H Cpad hpad r oracle q hq D) ≤ c * (widthOf source a H Cpad hpad r oracle q hq D) := by
        have := Nat.mul_le_mul_right (widthOf source a H Cpad hpad r oracle q hq D) (show i + 1 ≤ c by omega)
        have : (widthOf source a H Cpad hpad r oracle q hq D) + i * (widthOf source a H Cpad hpad r oracle q hq D) = (i + 1) * (widthOf source a H Cpad hpad r oracle q hq D) := by ring
        omega
      omega)
  have hmeaning : FixedFold.value bit c = padCore (xorPower seed c) hfit point :=
    FixedFold.padded_xor seed point hfit bit (fun _ => rfl)
  rw [← hmeaning]
  exact hmain

end Fold

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun
