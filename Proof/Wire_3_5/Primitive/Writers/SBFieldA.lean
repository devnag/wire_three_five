import Proof.Wire_3_5.Primitive.Writers.SBWords
import Proof.Wire_3_5.Primitive.SeedFix.W6N

/-! # SB, part 7: the field phase's word steps

The field phase (S4's words `4`, `5`) prepares, from the degree `ℓ` in a register, the modulus machine's input `1^ℓ`
and six zero words `frame (binary ℓ 0)` (the trace program's mask and work words), and afterwards the erase bound
`4ℓ + 6` (`Modulus.modulus_full`'s tape bound):

* `copyOnesW`, **`copyOnes_spec`**; `copyZeroW`, **`copyZero_spec`**; `zerosW`, **`zeros_spec`** (a list of blank
  streams ↦ `frame (binary ℓ 0)` each); `tripW`, **`trip_spec`** (`R := R + 3v`); **`bound_spec`** (`RT := 4ℓ + 6`).

Paper quantity: none (plumbing for S4's field words, P3:2932-2941). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBFieldA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SBWords

variable {ns nr : ℕ} (cap : ℕ)

theorem zeroFrame (ℓ : ℕ) : FiltRec.reps ℓ [true, false] ++ [false] = frame (binary ℓ 0) := by
  rw [PrimT.W6.binary_zero, PrimT.W6.frame_rep]

/-- Copy `RL` into `RR`, then `1^ℓ` on `O` from `RR`. -/
def copyOnesW (O : Fin (ns + 1)) (RL RR Tt OP : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR RL RR Tt) (onesW O OP RR)

theorem copyOnes_spec (O : Fin (ns + 1)) (RL RR Tt OP : Fin nr) (h1 : RL ≠ RR) (h2 : RL ≠ Tt) (h3 : RR ≠ Tt)
    (h4 : RR ≠ OP) (ℓ : ℕ) (σ : WState ns nr) (hL : σ.val RL = ℓ) (hR : σ.val RR = 0) (hT : σ.val Tt = 0)
    (hop : σ.val OP = 0) (hO : σ.st O = []) (hh : σ.sh O = 0) (hc : ℓ ≤ cap) :
    WExec cap (copyOnesW O RL RR Tt OP) σ (σ.sets O (List.replicate ℓ true))
      (UnaryPow.sq cap + 1 + (16 * ℓ + 3)) := by
  have e1 := SparseNum.copy1 cap RL RR Tt h1 h2 h3 ℓ σ hL hR hT hc
  have e2 := ones_spec cap O OP RR h4 ℓ (σ.setv RR ℓ) (by simp) (by simpa using hO) (by simpa using hh)
    (by simp [Function.update_of_ne (Ne.symm h4), hop]) hc
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j; by_cases hj : j = RR
    · subst hj; simp [hR]
    · simp [Function.update_of_ne hj]
  · rfl

/-- Copy `RL` into `RR`, then the zero word on `O` from `RR`. -/
def copyZeroW (O : Fin (ns + 1)) (RL RR Tt OP : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR RL RR Tt) (zeroW O OP RR)

theorem copyZero_spec (O : Fin (ns + 1)) (RL RR Tt OP : Fin nr) (h1 : RL ≠ RR) (h2 : RL ≠ Tt) (h3 : RR ≠ Tt)
    (h4 : RR ≠ OP) (ℓ : ℕ) (σ : WState ns nr) (hL : σ.val RL = ℓ) (hR : σ.val RR = 0) (hT : σ.val Tt = 0)
    (hop : σ.val OP = 0) (hO : σ.st O = []) (hh : σ.sh O = 0) (hc : 2 * ℓ + 1 ≤ cap) :
    WExec cap (copyZeroW O RL RR Tt OP) σ (σ.sets O (frame (binary ℓ 0)))
      (UnaryPow.sq cap + 1 + (29 * ℓ + 16)) := by
  have e1 := SparseNum.copy1 cap RL RR Tt h1 h2 h3 ℓ σ hL hR hT (by omega)
  have e2 := zero_spec cap O OP RR h4 ℓ (σ.setv RR ℓ) (by simp) (by simpa using hO) (by simpa using hh)
    (by simp [Function.update_of_ne (Ne.symm h4), hop]) hc
  rw [zeroFrame] at e2
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j; by_cases hj : j = RR
    · subst hj; simp [hR]
    · simp [Function.update_of_ne hj]
  · rfl

/-- The zero word on every listed stream. -/
def zerosW (RL RR Tt OP : Fin nr) : List (Fin (ns + 1)) → WM ns nr
  | [] => .skip
  | O :: l => .seq (copyZeroW O RL RR Tt OP) (zerosW RL RR Tt OP l)

def zerosCost (ℓ : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => UnaryPow.sq cap + 1 + (29 * ℓ + 16) + 1 + zerosCost ℓ k

theorem zeros_spec (RL RR Tt OP : Fin nr) (h1 : RL ≠ RR) (h2 : RL ≠ Tt) (h3 : RR ≠ Tt) (h4 : RR ≠ OP) (ℓ : ℕ)
    (hc : 2 * ℓ + 1 ≤ cap) :
    ∀ (l : List (Fin (ns + 1))) (σ : WState ns nr), l.Nodup → σ.val RL = ℓ → σ.val RR = 0 → σ.val Tt = 0 →
      σ.val OP = 0 → (∀ O ∈ l, σ.st O = [] ∧ σ.sh O = 0) →
      ∃ τ : WState ns nr, WExec cap (zerosW RL RR Tt OP l) σ τ (zerosCost cap ℓ l.length) ∧
        (∀ O ∈ l, τ.st O = frame (binary ℓ 0) ∧ τ.sh O = 0) ∧ (∀ i, i ∉ l → τ.st i = σ.st i) ∧
        τ.sh = σ.sh ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  intro l
  induction l with
  | nil =>
    intro σ _ _ _ _ _ _
    exact ⟨σ, WExec.skip σ, fun O hO => by simp at hO, fun _ _ => rfl, rfl, rfl, rfl⟩
  | cons O l ih =>
    intro σ hnd hL hR hT hop hbl
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨hst, hsh⟩ := hbl O (by simp)
    have e1 := copyZero_spec cap O RL RR Tt OP h1 h2 h3 h4 ℓ σ hL hR hT hop hst hsh hc
    set σ1 := σ.sets O (frame (binary ℓ 0)) with hσ1
    have hbl1 : ∀ O' ∈ l, σ1.st O' = [] ∧ σ1.sh O' = 0 := by
      intro O' hO'
      have hne : O' ≠ O := fun e => hnd'.1 (e ▸ hO')
      obtain ⟨a, b⟩ := hbl O' (List.mem_cons_of_mem _ hO')
      exact ⟨by simp [hσ1, Function.update_of_ne hne, a], by simp [hσ1, b]⟩
    obtain ⟨τ, e2, hin, hout, hsh', hv, hcl⟩ := ih σ1 hnd'.2 (by simp [hσ1, hL]) (by simp [hσ1, hR])
      (by simp [hσ1, hT]) (by simp [hσ1, hop]) hbl1
    refine ⟨τ, WExec.seq e1 e2, ?_, ?_, ?_, ?_, ?_⟩
    · intro O' hO'
      rcases List.mem_cons.mp hO' with e | e
      · subst e
        rw [hout O' hnd'.1, hsh']
        simp [hσ1, hsh]
      · exact hin O' e
    · intro i hi
      have hne : i ≠ O := fun e => hi (e ▸ List.mem_cons_self)
      rw [hout i (fun e => hi (List.mem_cons_of_mem _ e))]
      simp [hσ1, Function.update_of_ne hne]
    · rw [hsh']; rfl
    · rw [hv]; rfl
    · rw [hcl]; rfl

/-- `R := R + 3v` from `C` (consumed). -/
def tripW (R C : Fin nr) : WM ns nr := .whr C (.seq (.dec C) (.seq (.inc R) (.seq (.inc R) (.inc R))))

theorem trip_spec (R C : Fin nr) (hRC : R ≠ C) :
    ∀ (v : ℕ) (σ : WState ns nr), σ.val C = v → σ.val R + 3 * v ≤ cap → v ≤ cap →
      WExec cap (tripW R C) σ ((σ.setv C 0).setv R (σ.val R + 3 * v)) (19 * v + 1) := by
  intro v
  induction v with
  | zero =>
    intro σ hv _ _
    have e : (σ.setv C 0).setv R (σ.val R + 3 * 0) = σ := by
      apply WState.eq
      · rfl
      · rfl
      · funext j
        by_cases hj : j = R
        · subst hj; simp
        · by_cases hj2 : j = C
          · subst hj2; simp [Function.update_of_ne hj, hv]
          · simp [Function.update_of_ne hj, Function.update_of_ne hj2]
      · rfl
    rw [e]
    exact WExec.whrF hv
  | succ v ih =>
    intro σ hv hc hv2
    have d1 := WExec.dec (cap := cap) C σ (by omega)
    set σ1 := σ.setv C (σ.val C - 1) with hσ1
    have i1 := WExec.inc (cap := cap) R σ1 (by simp [hσ1, Function.update_of_ne hRC]; omega)
    set σ2 := σ1.setv R (σ1.val R + 1) with hσ2
    have i2 := WExec.inc (cap := cap) R σ2 (by simp [hσ2, hσ1, Function.update_of_ne hRC]; omega)
    set σ3 := σ2.setv R (σ2.val R + 1) with hσ3
    have i3 := WExec.inc (cap := cap) R σ3 (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hRC]; omega)
    set σ4 := σ3.setv R (σ3.val R + 1) with hσ4
    have hv4 : σ4.val C = v := by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hRC)]; omega
    have hR4 : σ4.val R = σ.val R + 3 := by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hRC]
    have h5 := ih σ4 hv4 (by rw [hR4]; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show σ.val C ≠ 0 by omega) (WExec.seq d1 (WExec.seq i1 (WExec.seq i2 i3))) h5) ?_
      (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext j
      by_cases hj : j = R
      · subst hj; simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hRC]; omega
      · by_cases hj2 : j = C
        · subst hj2; simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hj]
        · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hj, Function.update_of_ne hj2]
    · rfl

/-- **The erase bound** `RT := 4ℓ + 6` (from `RL = ℓ`, through `RR`). -/
def boundW (RL RR Tt RT : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR RL RT Tt) (.seq (FinalPass.Hash4.wcopyR RL RR Tt) (.seq (tripW RT RR) (StarNums.incN RT 6)))

theorem bound_spec (RL RR Tt RT : Fin nr) (h1 : RL ≠ RR) (h2 : RL ≠ Tt) (h3 : RR ≠ Tt) (h4 : RL ≠ RT) (h5 : RT ≠ Tt)
    (h6 : RT ≠ RR) (ℓ : ℕ) (σ : WState ns nr) (hL : σ.val RL = ℓ) (hR : σ.val RR = 0) (hT : σ.val Tt = 0)
    (hB : σ.val RT = 0) (hc : 4 * ℓ + 6 ≤ cap) :
    WExec cap (boundW RL RR Tt RT) σ (σ.setv RT (4 * ℓ + 6))
      (UnaryPow.sq cap + 1 + (UnaryPow.sq cap + 1 + (19 * ℓ + 1 + 1 + UnaryPow.sq cap))) := by
  have e1 := SparseNum.copy1 cap RL RT Tt h4 h2 h5 ℓ σ hL hB hT (by omega)
  have e2 := SparseNum.copy1 cap RL RR Tt h1 h2 h3 ℓ (σ.setv RT ℓ) (by simp [Function.update_of_ne h4, hL])
    (by simp [Function.update_of_ne (Ne.symm h6), hR]) (by simp [Function.update_of_ne (Ne.symm h5), hT]) (by omega)
  have e3 := trip_spec cap RT RR h6 ℓ ((σ.setv RT ℓ).setv RR ℓ) (by simp) (by simp [Function.update_of_ne h6]; omega)
    (by omega)
  have e4 := FiltNum.incN1 cap RT (4 * ℓ) 6
    ((((σ.setv RT ℓ).setv RR ℓ).setv RR 0).setv RT (((σ.setv RT ℓ).setv RR ℓ).val RT + 3 * ℓ))
    (by simp [Function.update_of_ne h6]; omega) (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j
    by_cases hj : j = RT
    · subst hj; simp
    · by_cases hj2 : j = RR
      · subst hj2; simp [Function.update_of_ne hj, hR]
      · simp [Function.update_of_ne hj, Function.update_of_ne hj2]
  · rfl

end NearCubicWires.WireExponent3_5.PrimAsm.SBFieldA
