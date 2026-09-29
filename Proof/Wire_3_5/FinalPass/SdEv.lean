import Proof.Wire_3_5.FinalPass.SdPt1
import Proof.Wire_3_5.FinalPass.Sd1
import Proof.Wire_3_5.FinalPass.ThrPtRS36

/-! # S4 (the seeds phase), part 5: the accumulator and the per-point evaluators on the body's layout (P3:3170-3178)

"Evaluate the reported lookups at the sampled pairs" (P3:3046-3048): at a point the evaluator of the call's mode adds
`Σ R̂` (THR: S2's `ThrPt.thrPtProg`, `Σ_{g,p} R̂_{g,p}`; SYM: the SYM evaluator `E`, `Σ_{e'} R̂_{e'}`), and the value
is added into the numerator `frame (binary W x)`.

* **`addA`**: `Sd1.addLoop` on `tN` with the accumulator `rAcc`; **`addA_spec`**: `tN` becomes
  `frame (binary W (x + v))`, the accumulator `0`, within `v·(incCost T + 4) + 1` for any `T` with `x + v < 2^T`;
* the evaluators' embeddings: `STe`, `RTe` (THR: the point, words `8 … 14`, scratch streams `18 … 24`, registers
  `0`, `1 … 4`, `5 … 117`), `SSe`, `RSe` (SYM: the point, words `16 …`, scratch streams `47 + nw …`, registers `0`,
  `220 …`);
* **`evalD E`**: the mode test on word `13` (the THR primes' list, blank for SYM), then the mode's evaluator;
  `EvOut V` (the accumulator `V`, the heads, cell and every non-scratch stream kept, the scratch blank);
  **`evalT_spec`**, **`evalS_spec`**: from the evaluator's `PtIn2`, `EvOut` at `rsumThr` / `rsumSym`.

Paper quantities: the per-point sums `Σ R̂` (P3:3046-3048) and the numerator in binary. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.ThrPt (USt)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (PtIn2 PtOut SymPtEval2 ThrCall SymCall thrWords thrNums rsumThr
  rsumSym)

section Lay
variable {nw nn nsc nrs : ℕ}

/-! ## The accumulator -/

def rAcc : Fin (bnr nn nrs) := brg 0 (by omega)
def rAc : Fin (bnr nn nrs) := brg 154 (by omega)
def rAr : Fin (bnr nn nrs) := brg 155 (by omega)

/-- The adder's stream: the numerator. -/
def fsA (_ : Fin 1) : Fin (bns nw nsc + 1) := tN

/-- The adder's registers: its position counter, a spare, the accumulator. -/
def frAv : Fin 3 → ℕ := ![154, 155, 0]

def frA (i : Fin 3) : Fin (bnr nn nrs) := brg (frAv i) (by fin_cases i <;> simp [frAv])

theorem fsA_inj : Function.Injective (fsA (nw := nw) (nsc := nsc)) := fun a b _ => Subsingleton.elim a b

theorem frA_inj : Function.Injective (frA (nn := nn) (nrs := nrs)) := fun a b h => by
  have e := congrArg Fin.val h
  simp only [frA, brg] at e
  revert e
  fin_cases a <;> fin_cases b <;> simp [frAv]

/-- **The numerator += the accumulator.** -/
def addA : BP nw nn nsc nrs := Sd.addLoop.liftW fsA frA

theorem addA_spec (cap W T x v : ℕ) (ω : BS nw nn nsc nrs) (hN : ω.st tN = frame (binary W x)) (hh : ω.sh tN = 0)
    (hc : ω.val rAc = 0) (hk : ω.val rAcc = v) (hx : x + v < 2 ^ W) (hT : x + v < 2 ^ T) (hv : v ≤ cap)
    (hcap : 2 * T + 2 < cap) :
    WExec cap addA ω ((ω.sets tN (frame (binary W (x + v)))).setv rAcc 0) (v * (incCost T + 4) + 1) := by
  obtain ⟨u, hu⟩ : ∃ u : USt, u = ⟨ω.st tN, ω.sh tN, ω.val rAc, ω.val rAr, ω.val rAcc, ω.cell⟩ := ⟨_, rfl⟩
  have hvw : viewW fsA frA ω = u.w := by
    rw [hu]
    apply WState.eq
    · funext i; fin_cases i; rfl
    · funext i; fin_cases i; rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  have e := Sd.addLoop_spec cap W T [] hcap v x u (by rw [hu]; show ω.st tN = _; rw [hN, frame_eq_frameP])
    (by rw [hu]; exact hh) (by rw [hu]; exact hc) (by rw [hu]; exact hk) hx hT hv
  rw [← hvw] at e
  have e2 := ThrPt.WExec.liftW_upd cap fsA_inj frA_inj e ω (liftW_view _ _ ω)
  refine WExec.cast cap e2 ?_ le_rfl
  have hA0 : (frA 0 : Fin (bnr nn nrs)) ≠ rAcc := by simp only [frA, rAcc]; apply brg_ne; simp [frAv]
  have hA1 : (frA 1 : Fin (bnr nn nrs)) ≠ rAcc := by simp only [frA, rAcc]; apply brg_ne; simp [frAv]
  have hA2 : (frA 2 : Fin (bnr nn nrs)) = rAcc := rfl
  apply ThrPt.wstate_ext_img (fs := fsA) (fr := frA)
  · intro i
    rw [ThrPt.updW_sh_in fsA_inj, hu]
    fin_cases i
    rfl
  · intro j hj
    rw [ThrPt.updW_sh_out _ _ j hj]
    rfl
  · intro i
    rw [ThrPt.updW_st_in fsA_inj]
    fin_cases i
    show frameP (binary W (x + v)) ++ false :: [] = Function.update ω.st tN (frame (binary W (x + v))) tN
    rw [Function.update_self, frame_eq_frameP]
  · intro j hj
    rw [ThrPt.updW_st_out _ _ j hj]
    have hne : j ≠ tN := fun h => hj 0 h.symm
    show ω.st j = Function.update ω.st tN _ j
    rw [Function.update_of_ne hne]
  · intro r
    rw [ThrPt.updW_val_in frA_inj]
    fin_cases r
    · show u.c = Function.update ω.val rAcc 0 (frA 0)
      rw [Function.update_of_ne hA0, hu]
      rfl
    · show u.r = Function.update ω.val rAcc 0 (frA 1)
      rw [Function.update_of_ne hA1, hu]
      rfl
    · show 0 = Function.update ω.val rAcc 0 (frA 2)
      rw [hA2, Function.update_self]
  · intro q hq
    rw [ThrPt.updW_val_out _ _ q hq]
    have hne : q ≠ rAcc := fun h => hq 2 (hA2.trans h.symm)
    show ω.val q = Function.update ω.val rAcc 0 q
    rw [Function.update_of_ne hne]
  · rw [ThrPt.updW_cell, hu]
    rfl

/-! ## The evaluators' embeddings -/

/-- The THR evaluator's streams: the point `1 … 3`, words `8 … 14` (`38 … 44`), scratch `18 … 24`. -/
def sTv : Fin 3 ⊕ Fin 7 ⊕ Fin 7 → ℕ
  | .inl i => 1 + i.val
  | .inr (.inl k) => 38 + k.val
  | .inr (.inr j) => 18 + j.val

theorem sTv_lt (x : Fin 3 ⊕ Fin 7 ⊕ Fin 7) : sTv x < 47 := by
  rcases x with i | k | j
  · have := i.isLt; simp only [sTv]; omega
  · have := k.isLt; simp only [sTv]; omega
  · have := j.isLt; simp only [sTv]; omega

theorem sTv_inj : Function.Injective sTv := by decide

/-- The THR evaluator's stream embedding. -/
def STe : Fin 3 ⊕ Fin 7 ⊕ Fin 7 ↪ Fin (bns nw nsc + 1) :=
  ⟨fun x => bst (sTv x) (sTv_lt x), fun _ _ h => sTv_inj (congrArg Fin.val h)⟩

/-- The THR evaluator's registers: the accumulator `0`, the numbers `1 … 4`, the scratch `5 … 117`. -/
def rTv : Fin 1 ⊕ Fin 4 ⊕ Fin 113 → ℕ
  | .inl _ => 0
  | .inr (.inl i) => 1 + i.val
  | .inr (.inr j) => 5 + j.val

theorem rTv_lt (x : Fin 1 ⊕ Fin 4 ⊕ Fin 113) : rTv x < 220 := by
  rcases x with _ | i | j
  · simp only [rTv]; omega
  · have := i.isLt; simp only [rTv]; omega
  · have := j.isLt; simp only [rTv]; omega

theorem rTv_inj : Function.Injective rTv := by
  intro x y h
  rcases x with a | i | j <;> rcases y with b | i' | j' <;> simp only [rTv] at h
  · exact congrArg Sum.inl (Subsingleton.elim a b)
  · omega
  · omega
  · omega
  · exact congrArg (fun z => Sum.inr (Sum.inl z)) (Fin.ext (by omega))
  · have := i.isLt; omega
  · omega
  · have := i'.isLt; omega
  · exact congrArg (fun z => Sum.inr (Sum.inr z)) (Fin.ext (by omega))

/-- The THR evaluator's register embedding. -/
def RTe : Fin 1 ⊕ Fin 4 ⊕ Fin 113 ↪ Fin (bnr nn nrs) :=
  ⟨fun x => brg (rTv x) (rTv_lt x), fun _ _ h => rTv_inj (congrArg Fin.val h)⟩

/-- The SYM evaluator's streams: the point, words `16 …` (`46 …`), scratch `47 + nw …`. -/
def sSv (x : Fin 3 ⊕ Fin nw ⊕ Fin nsc) : ℕ :=
  match x with
  | .inl i => 1 + i.val
  | .inr (.inl k) => 46 + k.val
  | .inr (.inr j) => 47 + nw + j.val

theorem sSv_lt (x : Fin 3 ⊕ Fin nw ⊕ Fin nsc) : sSv x < bns nw nsc + 1 := by
  unfold bns
  rcases x with i | k | j
  · have := i.isLt; simp only [sSv]; omega
  · have := k.isLt; simp only [sSv]; omega
  · have := j.isLt; simp only [sSv]; omega

theorem sSv_inj : Function.Injective (sSv (nw := nw) (nsc := nsc)) := by
  intro x y h
  rcases x with i | k | j <;> rcases y with i' | k' | j' <;> simp only [sSv] at h
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · have := i.isLt; omega
  · have := i.isLt; omega
  · have := i'.isLt; omega
  · exact congrArg (fun z => Sum.inr (Sum.inl z)) (Fin.ext (by omega))
  · have := k.isLt; omega
  · have := i'.isLt; omega
  · have := k'.isLt; omega
  · exact congrArg (fun z => Sum.inr (Sum.inr z)) (Fin.ext (by omega))

/-- The SYM evaluator's stream embedding. -/
def SSe : Fin 3 ⊕ Fin nw ⊕ Fin nsc ↪ Fin (bns nw nsc + 1) :=
  ⟨fun x => ⟨sSv x, sSv_lt x⟩, fun _ _ h => sSv_inj (congrArg Fin.val h)⟩

/-- The SYM evaluator's registers: the accumulator `0`, the numbers `220 …`, the scratch `220 + nn …`. -/
def rSv (x : Fin 1 ⊕ Fin nn ⊕ Fin nrs) : ℕ :=
  match x with
  | .inl _ => 0
  | .inr (.inl i) => 220 + i.val
  | .inr (.inr j) => 220 + nn + j.val

theorem rSv_lt (x : Fin 1 ⊕ Fin nn ⊕ Fin nrs) : rSv x < bnr nn nrs := by
  unfold bnr
  rcases x with _ | i | j
  · simp only [rSv]; omega
  · have := i.isLt; simp only [rSv]; omega
  · have := j.isLt; simp only [rSv]; omega

theorem rSv_inj : Function.Injective (rSv (nn := nn) (nrs := nrs)) := by
  intro x y h
  rcases x with a | i | j <;> rcases y with b | i' | j' <;> simp only [rSv] at h
  · exact congrArg Sum.inl (Subsingleton.elim a b)
  · omega
  · omega
  · omega
  · exact congrArg (fun z => Sum.inr (Sum.inl z)) (Fin.ext (by omega))
  · have := i.isLt; omega
  · omega
  · have := i'.isLt; omega
  · exact congrArg (fun z => Sum.inr (Sum.inr z)) (Fin.ext (by omega))

/-- The SYM evaluator's register embedding. -/
def RSe : Fin 1 ⊕ Fin nn ⊕ Fin nrs ↪ Fin (bnr nn nrs) :=
  ⟨fun x => ⟨rSv x, rSv_lt x⟩, fun _ _ h => rSv_inj (congrArg Fin.val h)⟩

/-! ## The evaluators' exit -/

/-- The evaluators' scratch streams. -/
def IsSc (i : Fin (bns nw nsc + 1)) : Prop := (18 ≤ i.val ∧ i.val < 25) ∨ 47 + nw ≤ i.val

/-- **An evaluator's exit at value `V`**: the accumulator `V`, every head, the cell and every non-scratch stream as at
entry, the scratch blank. -/
structure EvOut (V : ℕ) (ω ω' : BS nw nn nsc nrs) : Prop where
  val : ω'.val = Function.update ω.val rAcc V
  sh : ω'.sh = ω.sh
  cell : ω'.cell = ω.cell
  st : ∀ i, ¬ IsSc i → ω'.st i = ω.st i
  sc : ∀ i, IsSc i → ∀ b ∈ ω'.st i, b = false

/-- The mode test's stream: word `13` (the THR primes' list). -/
def tM : Fin (bns nw nsc + 1) := bst 43 (by omega)

end Lay

/-! ## The dispatch -/

variable (E : SymPtEval2)

/-- **The point's evaluator**: THR when word `13` reads `1`, else SYM. -/
noncomputable def evalD : BP E.nw E.nn E.nsc E.nrs := .ifs tM (ThrPt.thrPtProg.prog STe RTe) (E.prog SSe RSe)

theorem evalT_spec (cap : ℕ) (k : ThrCall) (c : BitInput k.P.n) (u v : k.P.Errors) (ω : BS E.nw E.nn E.nsc E.nrs)
    (hbit : wbit ω tM = true)
    (hin : PtIn2 STe RTe c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) (thrWords k)
      (thrNums k) ω)
    (hsc : ∀ i, IsSc i → ∀ b ∈ ω.st i, b = false)
    (hneed : ThrPt.thrPtProg.need (k.P.n + (∑ i, (thrWords k i).length) + ∑ i, thrNums k i) ≤ cap) :
    ∃ ω', WExec cap (evalD E) ω ω' (ThrPt.thrPtProg.bound (k.P.n + (∑ i, (thrWords k i).length) +
        ∑ i, thrNums k i) + 1) ∧
      EvOut (rsumThr k.P k.Cs k.alg k.den (ListFast.listReportFast k.D) c u v) ω ω' := by
  obtain ⟨τ, e, hout⟩ := ThrPt.thrPtProg.run STe RTe k c u v cap ω hin hneed
  have hsc' : ∀ j : Fin 7, IsSc (STe (.inr (.inr j)) : Fin (bns E.nw E.nsc + 1)) := fun j => by
    left
    show 18 ≤ 18 + j.val ∧ 18 + j.val < 25
    have := j.isLt
    omega
  refine ⟨τ, WExec.ifsT hbit e, hout.val, hout.sh, hout.cell, fun i hi => hout.st i (fun j h => hi (h ▸ hsc' j)),
    fun i hi b hb => ?_⟩
  by_cases hj : ∃ j : Fin 7, i = STe (.inr (.inr j))
  · obtain ⟨j, rfl⟩ := hj
    exact hout.sc j b hb
  · rw [hout.st i (fun j h => hj ⟨j, h⟩)] at hb
    exact hsc i hi b hb

theorem evalS_spec (cap : ℕ) (k : SymCall) (c : BitInput k.P.n) (u v : k.P.Errors) (ω : BS E.nw E.nn E.nsc E.nrs)
    (hbit : wbit ω tM = false)
    (hin : PtIn2 SSe RSe c (k.P.errorVector k.P.leftBlock u) (k.P.errorVector k.P.rightBlock v) (E.words k)
      (E.nums k) ω)
    (hsc : ∀ i, IsSc i → ∀ b ∈ ω.st i, b = false)
    (hneed : E.need (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) ≤ cap) :
    ∃ ω', WExec cap (evalD E) ω ω' (E.bound (k.P.n + (∑ i, (E.words k i).length) + ∑ i, E.nums k i) + 1) ∧
      EvOut (rsumSym k.P k.Cs k.Pl c u v) ω ω' := by
  obtain ⟨τ, e, hout⟩ := E.run SSe RSe k c u v cap ω hin hneed
  have hsc' : ∀ j : Fin E.nsc, IsSc (SSe (.inr (.inr j)) : Fin (bns E.nw E.nsc + 1)) := fun j => by
    right
    show 47 + E.nw ≤ 47 + E.nw + j.val
    omega
  refine ⟨τ, WExec.ifsF hbit e, hout.val, hout.sh, hout.cell, fun i hi => hout.st i (fun j h => hi (h ▸ hsc' j)),
    fun i hi b hb => ?_⟩
  by_cases hj : ∃ j : Fin E.nsc, i = SSe (.inr (.inr j))
  · obtain ⟨j, rfl⟩ := hj
    exact hout.sc j b hb
  · rw [hout.st i (fun j h => hj ⟨j, h⟩)] at hb
    exact hsc i hi b hb

end NearCubicWires.WireExponent3_5.FinalPass.Sd
