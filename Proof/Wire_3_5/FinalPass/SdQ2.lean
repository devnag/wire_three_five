import Proof.Wire_3_5.FinalPass.SdQ1

/-! # S4 (the seeds phase), part 36: the loops' entry state at a star call (P3:3170-3178)

`PreSet`: the body state after the prep and the tables writer at a star call (the prep's registers hold S4's small
numbers and `n`, every other register `0`; S4's words, the numerator's zero, the tables word, blank working streams,
every head at `0`, a blank cell). From it, the state `ωQ` after the setup (`setRS`) and the evaluator's numbers (any
change confined to THR's or SYM's number registers) meets the center loop's static facts **`cstat_of`** and the seed
loop's invariant at `0` **`sdinv_of`**, with the tables word in place and every register off the setup's and the
numbers' `0` (**`entry_regs`**).

Paper quantity of the main type: the seeds phase's loop-entry state at a star call (the star parameters, the
digits, the carriers' formats, the sample, the tables). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL offset centerAt)

theorem flat_ff : ∀ L : ℕ, (List.replicate L [false, false]).flatten ++ [false] = List.replicate (2 * L + 1) false
  | 0 => rfl
  | L + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, flat_ff L,
      show 2 * (L + 1) + 1 = (2 * L + 1) + 2 by ring, List.replicate_add]
    simp [List.replicate_succ]

theorem flat_len {α : Type} (L : ℕ) (bs : List α) : ((List.replicate L bs).flatten).length = L * bs.length := by simp

section Body
variable {nw nn nsc nrs : ℕ}

theorem notin_seedFix (q : Fin (bnr nn nrs))
    (h : q.val < 120 ∨ (121 < q.val ∧ q.val < 156) ∨ (159 < q.val ∧ q.val < 168) ∨ 172 < q.val) :
    q ∉ (seedFix : List (Fin (bnr nn nrs))) := by
  intro hm
  simp only [seedFix, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e | e | e | e <;> (rw [e] at h; simp [ctrR_b, frD_b, rP_b, brg] at h)

theorem notJob (i : Fin (bns nw nsc + 1))
    (h : i.val ≠ 1 ∧ i.val ≠ 2 ∧ i.val ≠ 3 ∧ (i.val < 8 ∨ 17 < i.val) ∧ i.val ≠ 25 ∧ i.val ≠ 26) :
    i ∉ ((sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))).map FlJob.o) := by
  intro hm
  simp only [sJobs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e | e | e | e | e | e | e | e | e | e | e | e <;>
    (rw [e] at h; simp [tU, tV, tC, tRow, tCol, tX, tZ, tPos, tNeg, tT, bst] at h)

theorem notThr (q : Fin (bnr nn nrs)) (h : q.val = 0 ∨ 5 ≤ q.val) : q ∉ (thrRegs : List (Fin (bnr nn nrs))) := by
  intro hm
  simp only [thrRegs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e | e | e | e <;> (rw [e] at h; simp [brg] at h)

theorem notSym (q : Fin (bnr nn nrs)) (h : q.val < 220) : q ∉ (symRegs : List (Fin (bnr nn nrs))) :=
  fun hm => by have := symRegs_mem q hm; omega

/-- **The body state after the prep and the tables writer** at a star call. -/
structure PreSet (P : StarParams) (σT : P.Translation) (smp : CallSample P) (carriers : List (Stars.Carrier P.n))
    (FP : GapParams) (W : ℕ) (σ0 : BS nw nn nsc nrs) : Prop where
  R : ∀ q, ¬ IsPrepReg q → σ0.val q = 0
  Rp : ∀ k : Fin 16, σ0.val (sRp ⟨k.val, by omega⟩) = (Seams.s4Small2 P carriers FP).getD k.val 0
  Rn : σ0.val (sRp 17) = P.n
  W8 : ∀ i : Fin 8, σ0.st (bst (30 + i.val) (by omega)) = Seams.s4Core2 P σT smp carriers FP i
  N : σ0.st tN = frame (binary W 0)
  TW : σ0.st tTW = twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)
  E : ∀ j ∈ (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))), σ0.st j.o = []
  Sp : σ0.st tSp = []
  Sc : ∀ i, IsSc i → σ0.st i = []
  sh : ∀ i, σ0.sh i = 0
  cell : σ0.cell = false

section Entry
variable (P : StarParams) (σT : P.Translation) (smp : CallSample P) (carriers : List (Stars.Carrier P.n))
  (FP : GapParams) (W : ℕ) (σ0 : BS nw nn nsc nrs) (e0 : GapSeed FP)

/-- The setup's exit at a star call. -/
def omS : BS nw nn nsc nrs :=
  setSOut (setROut σ0 (Hof carriers 0) (Hof carriers 1) (tb FP e0 (Seams.carLen carriers 0)).length
    (tb FP e0 (Seams.carLen carriers 1)).length)

variable {P σT smp carriers FP W σ0 e0}

theorem omS_st_other (i : Fin (bns nw nsc + 1))
    (h : i.val ≠ 1 ∧ i.val ≠ 2 ∧ i.val ≠ 3 ∧ (i.val < 8 ∨ 17 < i.val) ∧ i.val ≠ 25 ∧ i.val ≠ 26) (h4 : i.val ≠ 4) :
    (omS P carriers FP σ0 e0).st i = σ0.st i :=
  setRS_st_other σ0 _ _ _ _ i (notJob i h) (fun e => h4 (by rw [e]; rfl))

theorem omS_zero (hR : ∀ q, ¬ IsPrepReg q → σ0.val q = 0) (q : Fin (bnr nn nrs))
    (h : q.val < 120 ∨ (121 < q.val ∧ q.val < 156) ∨ (159 < q.val ∧ q.val < 168) ∨ 172 < q.val) :
    (omS P carriers FP σ0 e0).val q = 0 :=
  setRS_val_zero σ0 _ _ _ _ hR q (notin_seedFix q h)

theorem cstat_of (cap : ℕ) (hc2 : 2 ≤ cap) (H : PreSet P σT smp carriers FP W σ0) (ωQ : BS nw nn nsc nrs)
    (hst : ωQ.st = (omS P carriers FP σ0 e0).st) (hsh : ωQ.sh = (omS P carriers FP σ0 e0).sh)
    (hv : ∀ q, q ∉ (thrRegs : List (Fin (bnr nn nrs))) → q ∉ (symRegs : List (Fin (bnr nn nrs))) →
      ωQ.val q = (omS P carriers FP σ0 e0).val q) :
    CStat cap FP carriers P σT (List.ofFn smp.S) P.s P.b (P.r / 2) (P.n - P.r * P.b) ωQ := by
  have vQ : ∀ q : Fin (bnr nn nrs), (q.val = 0 ∨ 5 ≤ q.val) → q.val < 220 → ωQ.val q = (omS P carriers FP σ0 e0).val q :=
    fun q h1 h2 => hv q (notThr q h1) (notSym q h2)
  have z : ∀ q : Fin (bnr nn nrs), (q.val = 0 ∨ 5 ≤ q.val) → q.val < 220 →
      (q.val < 120 ∨ (121 < q.val ∧ q.val < 156) ∨ (159 < q.val ∧ q.val < 168) ∨ 172 < q.val) → ωQ.val q = 0 :=
    fun q h1 h2 h3 => by rw [vQ q h1 h2]; exact omS_zero H.R q h3
  have cp : ∀ p ∈ (cps : List (Fin (bnr nn nrs) × Fin (bnr nn nrs))), ωQ.val p.2 = σ0.val p.1 := fun p hp => by
    have hv5 : 5 ≤ p.2.val ∧ p.2.val < 220 := by
      simp only [cps, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ctrR_b, frD_b, brg]
    rw [vQ _ (Or.inr hv5.1) hv5.2]
    exact setRS_cp σ0 _ _ _ _ p hp
  have f : ∀ k : Fin 16, σ0.val (sRp ⟨k.val, by omega⟩) = (Seams.s4Small2 P carriers FP).getD k.val 0 := H.Rp
  have stQ : ∀ i : Fin (bns nw nsc + 1),
      (i.val ≠ 1 ∧ i.val ≠ 2 ∧ i.val ≠ 3 ∧ (i.val < 8 ∨ 17 < i.val) ∧ i.val ≠ 25 ∧ i.val ≠ 26) → i.val ≠ 4 →
      ωQ.st i = σ0.st i := fun i h h4 => by rw [hst]; exact omS_st_other i h h4
  have stQ' : ∀ (j : ℕ) (hj : j < 47), (j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3 ∧ (j < 8 ∨ 17 < j) ∧ j ≠ 25 ∧ j ≠ 26) → j ≠ 4 →
      ωQ.st (bst j hj) = σ0.st (bst j hj) := fun j hj h h4 => stQ (bst j hj) h h4
  refine
    { Sp := ?_, Thr := ?_, sh := ?_, ms := ?_, cap2 := hc2, M := ?_, Pf := ?_, acc := ?_, ac := ?_,
      dec := ?_, off := ?_, cB := ?_, cS := ?_, cH := ?_, cL := ?_, cR := ?_, cZ := ?_, I := ?_, cnt := ?_ }
  · rw [hst]; exact setRS_st_Sp σ0 _ _ _ _
  · exact (stQ' 36 (by omega) (by omega) (by omega)).trans (H.W8 6)
  · intro i; rw [hsh, omS, setRS_sh]; exact H.sh i
  · intro j hj
    exact z _ (Or.inr (show 5 ≤ 122 + j by omega)) (show 122 + j < 220 by omega)
      (Or.inr (Or.inl (show 121 < 122 + j ∧ 122 + j < 156 by omega)))
  · intro k
    have := k.isLt
    exact z _ (Or.inr (show 5 ≤ 118 + k.val by omega)) (show 118 + k.val < 220 by omega)
      (Or.inl (show 118 + k.val < 120 by omega))
  · intro k
    have hk := k.isLt
    rw [vQ _ (Or.inr (show 5 ≤ 120 + k.val by omega)) (show 120 + k.val < 220 by omega), omS, setRS_rP]
    have h12 : σ0.val (sRp 12) = carriers.length := f 12
    rw [h12]
    fin_cases k <;> simp <;> split_ifs <;> omega
  · exact z _ (Or.inl rfl) (show (0 : ℕ) < 220 by omega) (Or.inl (show (0 : ℕ) < 120 by omega))
  · exact z _ (Or.inr (show 5 ≤ 154 by omega)) (show 154 < 220 by omega)
      (Or.inr (Or.inl (show 121 < 154 ∧ 154 < 156 by omega)))
  · intro q
    by_cases hq : q.val < 4
    · revert hq
      fin_cases q <;> intro hq <;>
        first
          | exact (cp (sRp 2, frD 0) (by simp [cps])).trans (f 2)
          | exact (cp (sRp 1, frD 1) (by simp [cps])).trans (f 1)
          | exact (cp (sRp 3, frD 2) (by simp [cps])).trans (f 3)
          | exact (cp (sRp 6, frD 3) (by simp [cps])).trans (f 6)
          | (simp at hq)
    · have h4 : 4 ≤ q.val := by omega
      have hq12 := q.isLt
      rw [z (frD q) (Or.inr (show 5 ≤ 156 + q.val by omega)) (show 156 + q.val < 220 by omega)
        (Or.inr (Or.inr (Or.inl (show 159 < 156 + q.val ∧ 156 + q.val < 168 by omega))))]
      revert h4
      fin_cases q <;> simp
  · exact (stQ' 30 (by omega) (by omega) (by omega)).trans (H.W8 0)
  · exact (cp (sRp 1, ctrR 0) (by simp [cps])).trans (f 1)
  · exact (cp (sRp 2, ctrR 1) (by simp [cps])).trans (f 2)
  · exact (cp (sRp 3, ctrR 2) (by simp [cps])).trans (f 3)
  · exact (cp (sRp 4, ctrR 3) (by simp [cps])).trans (f 4)
  · exact (cp (sRp 5, ctrR 4) (by simp [cps])).trans (f 5)
  · intro i hi
    have := i.isLt
    exact z _ (Or.inr (show 5 ≤ 168 + i.val by omega)) (show 168 + i.val < 220 by omega)
      (Or.inr (Or.inr (Or.inr (show 172 < 168 + i.val by omega))))
  · rw [← sampWord_sw]
    exact (stQ' 31 (by omega) (by omega) (by omega)).trans (H.W8 1)
  · intro b
    cases b
    · exact ⟨z _ (Or.inr (show 5 ≤ 194 by omega)) (show 194 < 220 by omega)
          (Or.inr (Or.inr (Or.inr (show 172 < 194 by omega)))),
        z _ (Or.inr (show 5 ≤ 196 by omega)) (show 196 < 220 by omega)
          (Or.inr (Or.inr (Or.inr (show 172 < 196 by omega))))⟩
    · exact ⟨z _ (Or.inr (show 5 ≤ 197 by omega)) (show 197 < 220 by omega)
          (Or.inr (Or.inr (Or.inr (show 172 < 197 by omega)))),
        z _ (Or.inr (show 5 ≤ 199 by omega)) (show 199 < 220 by omega)
          (Or.inr (Or.inr (Or.inr (show 172 < 199 by omega))))⟩

end Entry

end Body

end NearCubicWires.WireExponent3_5.FinalPass.Sd
