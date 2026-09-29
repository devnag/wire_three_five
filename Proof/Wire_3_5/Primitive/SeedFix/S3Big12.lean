import Proof.Wire_3_5.Primitive.SeedFix.S3Big11
import Proof.Wire_3_5.FinalPass.SeamsPt2

/-! # S3: the SYM per-point evaluator (`Seams.SymPtEval2`)

"At one sampled input, compute the nested counts and discrepancies, evaluate the binary residue decoder, follow its
unique reconstructed count or empty state, and then apply repair, majority, and radix lookup. This takes polynomial
time without evaluating a monomial expansion. It is essential that these are reported-list values" (P3:3174-3179).
The per-point sum `Σ_{e'} R̂_{e'}(c,u,v)` (`rsumSym`) is computed by the evaluator `evalS` on its own layout, lifted
into the caller's by the seam's embeddings (`fsS`, `frR`: point, words, scratch; accumulator, numbers, scratch
registers):
* `rsumD_eq`: the evaluator's accumulated sum is `rsumSym` (`rhat4`, `rsum_seeds`);
* **`symPtRun`**: from every `PtIn2` entry at the point `(c, e_L(u), e_R(v))` with capacity `100·(size+1)³`, the lifted
  evaluator ends in `PtOut` with the accumulator `rsumSym k.P k.Cs k.Pl c u v`, within `1100000·(size+1)⁶` steps;
* **`symPtFix : PtEvalFix2 … 16 18 symWords symNums`** and **`symPtEval : SymPtEval2`** (`= symPtFix.toW2`), with
  literal constants `C = 1100000`, `D = 6` (independent of every parameter).

Paper quantity of the main type: `Σ_{e'} R̂_{e'}(c,u,v)`, the SYM per-point sum. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.FinalPass.Seams

/-! ## The value -/

theorem rsumD_eq (k : SymCall) (c : BitInput k.P.n) (u v : k.P.Errors) :
    rsumD k c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) (Fintype.card k.Pl.FlatSeed) =
      rsumSym k.P k.Cs k.Pl c u v := by
  rw [rsum_seeds]
  unfold rsumD
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold rAt
  rw [dif_pos i.isLt, rhat4]

/-! ## The embeddings -/

/-- The evaluator's streams in the caller's: the point, the words, the scratch. -/
def fsS {ns : ℕ} (S : Fin 3 ⊕ Fin 16 ⊕ Fin 9 ↪ Fin (ns + 1)) (i : Fin 28) : Fin (ns + 1) :=
  if h : i.val < 3 then S (.inl ⟨i.val, h⟩)
  else if h2 : i.val < 19 then S (.inr (.inl ⟨i.val - 3, by omega⟩))
  else S (.inr (.inr ⟨i.val - 19, by omega⟩))

/-- The evaluator's registers in the caller's: the accumulator, the numbers, the scratch registers. -/
def frR {nr : ℕ} (R : Fin 1 ⊕ Fin 18 ⊕ Fin 48 ↪ Fin nr) (q : Fin 67) : Fin nr :=
  if h : q.val < 1 then R (.inl ⟨q.val, h⟩)
  else if h2 : q.val < 19 then R (.inr (.inl ⟨q.val - 1, by omega⟩))
  else R (.inr (.inr ⟨q.val - 19, by omega⟩))

theorem fsS_inj {ns : ℕ} (S : Fin 3 ⊕ Fin 16 ⊕ Fin 9 ↪ Fin (ns + 1)) : Function.Injective (fsS S) := by
  intro a b h
  unfold fsS at h
  split_ifs at h <;> have e := S.injective h <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.mk.injEq] at e <;> exact Fin.ext (by omega)

theorem frR_inj {nr : ℕ} (R : Fin 1 ⊕ Fin 18 ⊕ Fin 48 ↪ Fin nr) : Function.Injective (frR R) := by
  intro a b h
  unfold frR at h
  split_ifs at h <;> have e := R.injective h <;>
    simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Fin.mk.injEq] at e <;> exact Fin.ext (by omega)

theorem fsS_pt {ns : ℕ} (S : Fin 3 ⊕ Fin 16 ⊕ Fin 9 ↪ Fin (ns + 1)) (i : Fin 3) :
    fsS S ⟨i.val, by omega⟩ = S (.inl i) := by
  unfold fsS; rw [dif_pos i.isLt]

theorem fsS_w {ns : ℕ} (S : Fin 3 ⊕ Fin 16 ⊕ Fin 9 ↪ Fin (ns + 1)) (w : Fin 16) : fsS S (bW w) = S (.inr (.inl w)) := by
  unfold fsS bW
  rw [dif_neg (by simp), dif_pos (by simp; omega)]
  congr 3
  exact Fin.ext (by simp)

theorem fsS_sc {ns : ℕ} (S : Fin 3 ⊕ Fin 16 ⊕ Fin 9 ↪ Fin (ns + 1)) (s : Fin 9) :
    fsS S ⟨19 + s.val, by omega⟩ = S (.inr (.inr s)) := by
  unfold fsS
  rw [dif_neg (by show ¬ (19 + s.val < 3); omega), dif_neg (by show ¬ (19 + s.val < 19); omega)]
  congr 3
  exact Fin.ext (by simp)

theorem frR_acc {nr : ℕ} (R : Fin 1 ⊕ Fin 18 ⊕ Fin 48 ↪ Fin nr) : frR R qAcc = R (.inl 0) := by
  unfold frR qAcc; rw [dif_pos (by simp)]; rfl

theorem frR_num {nr : ℕ} (R : Fin 1 ⊕ Fin 18 ⊕ Fin 48 ↪ Fin nr) (i : Fin 18) : frR R (qN i) = R (.inr (.inl i)) := by
  unfold frR qN
  rw [dif_neg (by simp), dif_pos (by simp; omega)]
  congr 3
  exact Fin.ext (by simp)

theorem frR_sc {nr : ℕ} (R : Fin 1 ⊕ Fin 18 ⊕ Fin 48 ↪ Fin nr) (q : Fin 67) (hq : 19 ≤ q.val) :
    frR R q = R (.inr (.inr ⟨q.val - 19, by omega⟩)) := by
  unfold frR
  rw [dif_neg (by omega), dif_neg (by omega)]

/-! ## The run -/

/-- **The evaluator in the caller's layout.** -/
def symPtProg {ns nr : ℕ} (S : Fin 3 ⊕ Fin 16 ⊕ Fin 9 ↪ Fin (ns + 1)) (R : Fin 1 ⊕ Fin 18 ⊕ Fin 48 ↪ Fin nr) :
    WM ns nr :=
  evalS.liftW (fsS S) (frR R)

theorem BodyInv.sh0 {k : SymCall} {c eu ev : BitInput k.P.n} {ω : BS} (hI : BodyInv k c eu ev (fun _ => 0) ω)
    (i : Fin 28) : ω.sh i = 0 := by
  by_cases h1 : i.val < 3
  · have : i = bC ∨ i = bU ∨ i = bV := by
      rcases i with ⟨v, hv⟩
      simp only at h1
      interval_cases v <;> simp
    rcases this with rfl | rfl | rfl
    · exact hI.pth.1
    · exact hI.pth.2.1
    · exact hI.pth.2.2
  · by_cases h2 : i.val < 19
    · have e : i = bW ⟨i.val - 3, by omega⟩ := Fin.ext (by simp [bW]; omega)
      rw [e]
      by_cases ht : ∃ j, (⟨i.val - 3, by omega⟩ : Fin 16) = wIdx 2 j
      · obtain ⟨j, hj⟩ := ht
        rw [hj]; exact hI.thead j
      · simp only [not_exists] at ht
        exact hI.whead _ ht
    · exact hI.scs i (by omega)

theorem symPtRun {ns nr : ℕ} (S : Fin 3 ⊕ Fin 16 ⊕ Fin 9 ↪ Fin (ns + 1)) (R : Fin 1 ⊕ Fin 18 ⊕ Fin 48 ↪ Fin nr)
    (k : SymCall) (c : BitInput k.P.n) (u v : k.P.Errors) (cap : ℕ) (σ : WState ns nr)
    (hin : PtIn2 S R c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) (symWords k)
      (symNums k) σ)
    (hneed : 100 * (symSize k + 1) ^ 3 ≤ cap) :
    ∃ τ, WExec cap (symPtProg S R) σ τ (1100000 * (symSize k + 1) ^ 6) ∧
      PtOut S R σ τ (rsumSym k.P k.Cs k.Pl c u v) := by
  obtain ⟨hp, hcell⟩ := hin
  obtain ⟨x, hx⟩ : ∃ y : BS, y = ⟨fun i => σ.sh (fsS S i), fun i => σ.st (fsS S i), fun q => σ.val (frR R q),
      σ.cell⟩ := ⟨_, rfl⟩
  have hL : LiftW (fsS S) (frR R) σ x := by subst hx; exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  have xst : ∀ i, x.st i = σ.st (fsS S i) := fun i => by subst hx; rfl
  have xsh : ∀ i, x.sh i = σ.sh (fsS S i) := fun i => by subst hx; rfl
  have xval : ∀ q, x.val q = σ.val (frR R q) := fun q => by subst hx; rfl
  have xsc : ∀ q : Fin 67, 19 ≤ q.val → x.val q = 0 := fun q hq => by rw [xval, frR_sc R q hq]; exact hp.zero _
  have hsh0 : ∀ i, x.sh i = 0 := fun i => by
    rw [xsh]
    unfold fsS
    split_ifs <;> exact hp.heads _
  have hI : BodyInv k c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) (fun _ => 0) x := by
    refine ⟨fun w => by rw [xst, fsS_w]; exact hp.wd w, ?_, ?_, ?_, fun i => by rw [xval, frR_num]; exact hp.num i,
      fun i hi => ?_, fun i _ => hsh0 i, fun w _ => hsh0 _, fun j => hsh0 _,
      fun j => xsc _ (by show 19 ≤ 58 + j.val; omega), ⟨hsh0 _, hsh0 _, hsh0 _⟩,
      fun q => xsc _ (by show 19 ≤ 19 + q.val; omega),
      xsc _ (by decide), xsc _ (by decide), xsc _ (by decide), xsc _ (by decide)⟩
    · rw [xst, ← frame_eq_frameP]; exact (fsS_pt S 0) ▸ hp.ptC
    · rw [xst, ← frame_eq_frameP]; exact (fsS_pt S 1) ▸ hp.ptU
    · rw [xst, ← frame_eq_frameP]; exact (fsS_pt S 2) ▸ hp.ptV
    · rw [xst]
      have e : fsS S i = S (.inr (.inr ⟨i.val - 19, by omega⟩)) := by
        unfold fsS; rw [dif_neg (by omega), dif_neg (by omega)]
      rw [e]
      exact rdEq_blank _ (hp.sc _)
  obtain ⟨cc, c1, c2, c4, c5⟩ := symCaps k cap hneed
  obtain ⟨τx, ex, Iτ, vτ, cτ⟩ := evalS_spec cap k c _ _ x hI (xsc _ (by decide)) (xsc _ (by decide))
    (xsc _ (by decide)) (by rw [xval, frR_acc]; exact hp.acc) cc c1 c2 c4 c5
  obtain ⟨τ, eτ, hLτ, hOτ⟩ := WExec.liftW cap cap le_rfl (fsS S) (fsS_inj S) (frR R) (frR_inj R) ex σ hL
  refine ⟨τ, WExec.mono eτ (by have := evalCost_le k; omega), ⟨?_, ?_, ?_, fun i hi => ?_, fun j => ?_⟩⟩
  · funext r
    by_cases hr : ∃ q, frR R q = r
    · obtain ⟨q, rfl⟩ := hr
      rw [hLτ.val q, vτ]
      by_cases hq : q = qAcc
      · subst hq; rw [Function.update_self, frR_acc, Function.update_self, rsumD_eq]
      · rw [Function.update_of_ne hq, xval, Function.update_of_ne (fun e => hq (frR_inj R (e.trans (frR_acc R).symm)))]
    · simp only [not_exists] at hr
      rw [hOτ.2 r hr, Function.update_of_ne (fun e => hr qAcc ((frR_acc R).trans e.symm))]
  · funext i
    by_cases hi : ∃ i', fsS S i' = i
    · obtain ⟨i', rfl⟩ := hi
      rw [hLτ.sh i', Iτ.sh0 i', ← xsh, hsh0]
    · simp only [not_exists] at hi
      exact (hOτ.1 i hi).1
  · rw [hLτ.cell, cτ, hcell]
  · by_cases hin' : ∃ i', fsS S i' = i
    · obtain ⟨i', rfl⟩ := hin'
      rw [hLτ.st i', ← xst]
      have hlo : i'.val < 19 := by
        by_contra hc
        exact hi ⟨i'.val - 19, by omega⟩ (by unfold fsS; rw [dif_neg (by omega), dif_neg (by omega)])
      by_cases h3 : i'.val < 3
      · have : i' = bC ∨ i' = bU ∨ i' = bV := by
          rcases i' with ⟨w, hw⟩
          simp only at h3
          interval_cases w <;> simp
        rcases this with rfl | rfl | rfl
        · rw [Iτ.ptC, hI.ptC]
        · rw [Iτ.ptU, hI.ptU]
        · rw [Iτ.ptV, hI.ptV]
      · have e : i' = bW ⟨i'.val - 3, by omega⟩ := Fin.ext (by simp [bW]; omega)
        rw [e, Iτ.words, hI.words]
    · simp only [not_exists] at hin'
      exact (hOτ.1 i hin').2
  · intro b hb
    rw [← fsS_sc S j, hLτ.st] at hb
    exact blank_of_rdEq_nil _ (Iτ.sc _ (by simp)) b hb

/-! ## The evaluator -/

/-- **S3: the SYM per-point evaluator** at its declared words and numbers (`symWords`, `symNums`), capacity
`100·(size+1)³`, steps `1100000·(size+1)⁶`. -/
noncomputable def symPtFix : PtEvalFix2 SymCall (fun k => k.P) (fun k c u v => rsumSym k.P k.Cs k.Pl c u v) 16 18
    symWords symNums where
  nsc := 9
  nrs := 48
  prog := fun S R => symPtProg S R
  need := fun M => 100 * (M + 1) ^ 3
  bound := fun M => 1100000 * (M + 1) ^ 6
  C := 1100000
  D := 6
  need_le := fun M => by
    have h1 : (M + 1) ^ 3 ≤ (M + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  bound_le := fun M => le_rfl
  run := fun S R k c u v cap σ hin hneed => symPtRun S R k c u v cap σ hin hneed

/-- **S3's deliverable** (`Seams.SymPtEval2`). -/
noncomputable def symPtEval : SymPtEval2 := symPtFix.toW2


end NearCubicWires.WireExponent3_5.PrimT.S3
