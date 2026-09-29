import Proof.Wire_3_5.UnionMachine.SampKit
import Proof.Wire_3_5.UnionMachine.SampMath

/-! # C6 tail, item 2 (part 3): the zero words and the seed's coefficient records

The sample expansion's word program runs on the streams `0` the framed seed bits `S`, `1` the ruler `1^{kh}`, `2` the
ruler `1^Q`, `3` the ruler `1^ℓ`, `4` the modulus word `frame (binary ℓ p)`, `5` the output, `6` the seed records, `7`
the label `X`, `8`–`10` Horner's words `ACC`, `NEW`, `ST`; register `0` counts the rulers. This module writes:
* **`zw_spec`**: the zero word `frame (binary ℓ 0)` on a blank stream, its head back at `0`;
* **`seed_spec`**: the seed records `seedWord ℓ (allC P s)` (the top coefficient first, C5's Horner format) from the
  seed bits: the head skips to the top chunk, then per chunk `T`, its pairs, `F` and two chunks back (`rec_spec`,
  `recs_spec`), then the records' head back at `0`.

Paper quantity of the main type: the seed's coefficients `a_i` as Horner's records (`seedWord ℓ (allC P s)`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SampSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (Same emitW)
open NearCubicWires.WireExponent3_5.UnionMachine.TailAsm (Cp Cp.tr cp_emit rbW fp_app fp_cons fpl)
open NearCubicWires.WireExponent3_5.UnionMachine.SampKit
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (seedWord coefsRev)

variable (cap : ℕ)

/-! ## The zero words -/

/-- The zero word `frame (binary ℓ 0)` on the blank stream `D`, its head back at `0`. -/
def zwW (D : Fin 11) : WM 10 16 :=
  .seq (rulerW 3 0 (.seq (emitW D true) (emitW D false))) (.seq (emitW D false)
    (.seq (rulerW 3 0 (.seq (.bwd D) (.bwd D))) (.bwd D)))

def zwCost (ℓ : ℕ) : ℕ := ℓ * 20 + 3 + 1 + (3 + 1 + (ℓ * 16 + 3 + 1 + 1))

theorem zw_spec (D : Fin 11) (hD3 : D ≠ 3) (hD4 : D ≠ 4) (ℓ : ℕ) (hl : ℓ ≤ cap) (σ : WState 10 16)
    (hD : σ.st D = []) (hhD : σ.sh D = 0) (hL : σ.st 3 = List.replicate ℓ true) (hhL : σ.sh 3 = 0)
    (hc : σ.val 0 = 0) :
    ∃ τ, WExec cap (zwW D) σ τ (zwCost ℓ) ∧ τ.st D = frame (binary ℓ 0) ∧ τ.sh D = 0 ∧
      WFrame (fun i => i = D) (fun _ => False) σ τ := by
  obtain ⟨τ1, s1, c1⟩ := zeroP_spec cap 3 4 D 0 (by decide) hD3 (Ne.symm hD4) ℓ hl σ (by simp [hD, hhD]) hL hhL hc
  obtain ⟨τ2, s2, c2⟩ := cp_emit cap 4 D (Ne.symm hD4) false τ1 c1.endO
  have c12 := c1.tr c2 rfl rfl
  have hL2 : τ2.st 3 = List.replicate ℓ true := ((c12.same 3 (by decide) (Ne.symm hD3)).1).trans hL
  have hhL2 : τ2.sh 3 = 0 := ((c12.same 3 (by decide) (Ne.symm hD3)).2).trans hhL
  have hc2 : τ2.val 0 = 0 := by rw [c12.val]; exact hc
  have s3 := backP_spec cap 3 D 0 hD3 ℓ hl τ2 hL2 hhL2 hc2
  have s4 := WExec.bwd (cap := cap) D (τ2.seth D (τ2.sh D - 2 * ℓ))
  have hst : τ2.st D = frameP (List.replicate ℓ false) ++ [false] := by rw [c12.out, hD, List.nil_append]
  have hsh : τ2.sh D = 2 * ℓ + 1 := by rw [c12.endO, hst]; simp [fpl]
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), ?_, ?_, ?_⟩
  · simp only [WState.seth_st]; rw [hst, binary_zero, frame_eq_frameP]
  · simp only [WState.seth_sh, Function.update_self]; rw [hsh]; omega
  · refine ⟨fun i hi => ?_, fun r _ => ?_, ?_⟩
    · have hiD : i ≠ D := hi
      simp only [WState.seth_st, WState.seth_sh, Function.update_of_ne hiD]
      by_cases h4 : i = 4
      · subst h4; exact ⟨c12.st, by rw [c12.sh]; rfl⟩
      · exact c12.same i h4 hiD
    · simp only [WState.seth_val]; rw [c12.val]
    · simp only [WState.seth_cell]; exact c12.cell

/-! ## One coefficient record -/

/-- The `i`-th `ℓ`-bit chunk of the seed bits. -/
def chunk (w : List Bool) (ℓ i : ℕ) : List Bool := (w.drop (i * ℓ)).take ℓ

/-- One coefficient record: `T`, the chunk's pairs copied from the seed `S` to the records, `F`; then `S` backed over
two chunks. -/
def crecW : WM 10 16 :=
  .seq (emitW 6 true) (.seq (rulerW 3 0 (.seq (rbW 0 6) (rbW 0 6))) (.seq (emitW 6 false)
    (.seq (rulerW 3 0 (.seq (.bwd 0) (.bwd 0))) (rulerW 3 0 (.seq (.bwd 0) (.bwd 0))))))

def crecCost (ℓ : ℕ) : ℕ := 3 + 1 + (ℓ * 26 + 3 + 1 + (3 + 1 + (ℓ * 16 + 3 + 1 + (ℓ * 16 + 3))))

theorem rec_spec (i : ℕ) (hi : i < 8) (ℓ : ℕ) (w : List Bool) (hw : w.length = 8 * ℓ) (hl : ℓ ≤ cap)
    (σ : WState 10 16) (hS : σ.st 0 = frameP w ++ [false]) (hhS : σ.sh 0 = 2 * (i * ℓ))
    (hE : σ.sh 6 = (σ.st 6).length) (hL : σ.st 3 = List.replicate ℓ true) (hhL : σ.sh 3 = 0) (hc : σ.val 0 = 0) :
    ∃ τ, WExec cap crecW σ τ (crecCost ℓ) ∧ τ.st 0 = σ.st 0 ∧ τ.sh 0 = 2 * (i * ℓ) + 2 * ℓ - 2 * ℓ - 2 * ℓ ∧
      τ.st 6 = σ.st 6 ++ (true :: frame (chunk w ℓ i)) ∧ τ.sh 6 = (τ.st 6).length ∧
      WFrame (fun j => j = 0 ∨ j = 6) (fun _ => False) σ τ := by
  have hle : i * ℓ + ℓ ≤ 8 * ℓ := by nlinarith
  have hlen : (chunk w ℓ i).length = ℓ := by
    simp only [chunk, List.length_take, List.length_drop, hw]; omega
  have hsplit : w = w.take (i * ℓ) ++ (chunk w ℓ i ++ (w.drop (i * ℓ)).drop ℓ) := by
    unfold chunk; rw [List.take_append_drop, List.take_append_drop]
  have hpre : (frameP (w.take (i * ℓ))).length = 2 * (i * ℓ) := by
    rw [fpl, List.length_take, hw]; omega
  have hS' : σ.st 0 = frameP (w.take (i * ℓ)) ++
      (frameP (chunk w ℓ i) ++ (frameP ((w.drop (i * ℓ)).drop ℓ) ++ [false])) := by
    rw [hS]; conv_lhs => rw [hsplit]
    simp only [fp_app, List.append_assoc]
  obtain ⟨τ1, s1, c1⟩ := cp_emit cap 0 6 (by decide) true σ hE
  have hX1 : τ1.st 0 = frameP (w.take (i * ℓ)) ++
      (frameP (chunk w ℓ i) ++ (frameP ((w.drop (i * ℓ)).drop ℓ) ++ [false])) := by rw [c1.st, hS']
  have hhX1 : τ1.sh 0 = (frameP (w.take (i * ℓ))).length := by simp [c1.sh, hhS, hpre]
  have hL1 : τ1.st 3 = List.replicate (chunk w ℓ i).length true := by
    rw [hlen]; exact ((c1.same 3 (by decide) (by decide)).1).trans hL
  have hhL1 : τ1.sh 3 = 0 := ((c1.same 3 (by decide) (by decide)).2).trans hhL
  have hc1 : τ1.val 0 = 0 := by rw [c1.val]; exact hc
  obtain ⟨τ2, s2, c2⟩ := copyP_spec cap 3 0 6 0 (by decide) (by decide) (by decide) (chunk w ℓ i)
    (frameP (w.take (i * ℓ))) (frameP ((w.drop (i * ℓ)).drop ℓ) ++ [false]) (by rw [hlen]; exact hl) τ1 hX1 hhX1
    c1.endO hL1 hhL1 hc1
  obtain ⟨τ3, s3, c3⟩ := cp_emit cap 0 6 (by decide) false τ2 c2.endO
  have c13 := (c1.tr c2 rfl rfl).tr c3 rfl rfl
  have hL3 : τ3.st 3 = List.replicate ℓ true := ((c13.same 3 (by decide) (by decide)).1).trans hL
  have hhL3 : τ3.sh 3 = 0 := ((c13.same 3 (by decide) (by decide)).2).trans hhL
  have hc3 : τ3.val 0 = 0 := by rw [c13.val]; exact hc
  have s4 := backP_spec cap 3 0 0 (by decide) ℓ hl τ3 hL3 hhL3 hc3
  have s5 := backP_spec cap 3 0 0 (by decide) ℓ hl (τ3.seth 0 (τ3.sh 0 - 2 * ℓ)) (by simpa using hL3)
    (by simpa using hhL3) (by simpa using hc3)
  have hh3 : τ3.sh 0 = 2 * (i * ℓ) + 2 * ℓ := by
    rw [c13.sh, hhS]; simp [fpl, hlen]
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))))
    (by rw [hlen]; unfold crecCost; omega), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]; exact c13.st
  · simp only [WState.seth_sh, Function.update_self]; rw [hh3]
  · simp only [WState.seth_st]; rw [c13.out, frame_eq_frameP]; simp
  · simp only [WState.seth_sh, WState.seth_st, Function.update_of_ne (show (6 : Fin 11) ≠ 0 by decide)]
    exact c13.endO
  · refine ⟨fun j hj => ?_, fun r _ => ?_, ?_⟩
    · have h0 : j ≠ 0 := fun h => hj (Or.inl h)
      have h6 : j ≠ 6 := fun h => hj (Or.inr h)
      simp only [WState.seth_st, WState.seth_sh, Function.update_of_ne h0]
      exact c13.same j h0 h6
    · simp only [WState.seth_val]; rw [c13.val]
    · simp only [WState.seth_cell]; exact c13.cell

/-! ## All records -/

/-- The records of the chunks `k−1, …, 0`. -/
def crecsW : ℕ → WM 10 16
  | 0 => .skip
  | k + 1 => .seq crecW (crecsW k)

theorem recs_spec (ℓ : ℕ) (w : List Bool) (hw : w.length = 8 * ℓ) (hl : ℓ ≤ cap) :
    ∀ k, k ≤ 8 → ∀ σ : WState 10 16, σ.st 0 = frameP w ++ [false] → σ.sh 0 = 2 * ((k - 1) * ℓ) →
      σ.sh 6 = (σ.st 6).length → σ.st 3 = List.replicate ℓ true → σ.sh 3 = 0 → σ.val 0 = 0 →
      ∃ τ, WExec cap (crecsW k) σ τ (k * (crecCost ℓ + 1)) ∧ τ.st 0 = σ.st 0 ∧
        τ.st 6 = σ.st 6 ++ ((List.range k).reverse.flatMap fun i => true :: frame (chunk w ℓ i)) ∧
        τ.sh 6 = (τ.st 6).length ∧ WFrame (fun j => j = 0 ∨ j = 6) (fun _ => False) σ τ
  | 0, _, σ, _, _, hE, _, _, _ => ⟨σ, WExec.mono (WExec.skip σ) (by omega), rfl, by simp, hE, WFrame.refl _ _ σ⟩
  | k + 1, hk, σ, hS, hhS, hE, hL, hhL, hc => by
    obtain ⟨τ1, s1, e0, eh0, e6, eh6, f1⟩ := rec_spec cap k (by omega) ℓ w hw hl σ hS (by simpa using hhS) hE hL
      hhL hc
    have hS1 : τ1.st 0 = frameP w ++ [false] := by rw [e0, hS]
    have hhS1 : τ1.sh 0 = 2 * ((k - 1) * ℓ) := by rw [eh0, Nat.sub_one_mul]; omega
    have hL1 : τ1.st 3 = List.replicate ℓ true := (f1.1 3 (by decide)).1.trans hL
    have hhL1 : τ1.sh 3 = 0 := (f1.1 3 (by decide)).2.trans hhL
    have hc1 : τ1.val 0 = 0 := (f1.2.1 0 (fun h => h)).trans hc
    obtain ⟨τ, s2, e0', e6', eh6', f2⟩ := recs_spec ℓ w hw hl k (by omega) τ1 hS1 hhS1 eh6 hL1 hhL1 hc1
    refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by rw [Nat.add_mul, Nat.one_mul]; omega), e0'.trans e0, ?_, eh6',
      f1.trans f2⟩
    rw [e6', e6, List.range_succ, List.reverse_append]; simp

/-! ## Moving the head -/

/-- `k` copies of a program. -/
def repW (B : WM 10 16) : ℕ → WM 10 16
  | 0 => .skip
  | k + 1 => .seq B (repW B k)

theorem repSkip_spec (ℓ : ℕ) (hl : ℓ ≤ cap) : ∀ (k : ℕ) (σ : WState 10 16), σ.st 3 = List.replicate ℓ true →
    σ.sh 3 = 0 → σ.val 0 = 0 →
    WExec cap (repW (rulerW 3 0 (.seq (.fwd 0) (.fwd 0))) k) σ (σ.seth 0 (σ.sh 0 + k * (2 * ℓ)))
      (k * (ℓ * 16 + 4))
  | 0, σ, _, _, _ => by
    have e : σ.seth 0 (σ.sh 0 + 0 * (2 * ℓ)) = σ := by simp [wseth_same]
    rw [e]; exact WExec.mono (WExec.skip σ) (by omega)
  | k + 1, σ, hL, hhL, hc => by
    have s1 := skipP_spec cap 3 0 0 (by decide) ℓ hl σ hL hhL hc
    have s2 := repSkip_spec ℓ hl k (σ.seth 0 (σ.sh 0 + 2 * ℓ)) (by simpa using hL) (by simpa using hhL)
      (by simpa using hc)
    rw [wseth_seth] at s2
    refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [Nat.add_mul, Nat.one_mul]; omega)
    congr 1
    simp only [WState.seth_sh, Function.update_self]
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- Back over one record `T frame(c)` of the records' stream. -/
def backRecW : WM 10 16 := .seq (rulerW 3 0 (.seq (.bwd 6) (.bwd 6))) (.seq (.bwd 6) (.bwd 6))

theorem backRec_spec (ℓ : ℕ) (hl : ℓ ≤ cap) (σ : WState 10 16) (hL : σ.st 3 = List.replicate ℓ true)
    (hhL : σ.sh 3 = 0) (hc : σ.val 0 = 0) :
    WExec cap backRecW σ (σ.seth 6 (σ.sh 6 - (2 * ℓ + 2))) (ℓ * 16 + 8) := by
  have s1 := backP_spec cap 3 6 0 (by decide) ℓ hl σ hL hhL hc
  have s2 := WExec.bwd (cap := cap) 6 (σ.seth 6 (σ.sh 6 - 2 * ℓ))
  have s3 := WExec.bwd (cap := cap) 6 ((σ.seth 6 (σ.sh 6 - 2 * ℓ)).seth 6 ((σ.seth 6 (σ.sh 6 - 2 * ℓ)).sh 6 - 1))
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by omega)
  refine WState.eq ?_ rfl rfl rfl
  funext j
  simp only [WState.seth_sh, Function.update_apply]
  split_ifs <;> omega

theorem repBack_spec (ℓ : ℕ) (hl : ℓ ≤ cap) : ∀ (k : ℕ) (σ : WState 10 16), σ.st 3 = List.replicate ℓ true →
    σ.sh 3 = 0 → σ.val 0 = 0 →
    WExec cap (repW backRecW k) σ (σ.seth 6 (σ.sh 6 - k * (2 * ℓ + 2))) (k * (ℓ * 16 + 9))
  | 0, σ, _, _, _ => by
    have e : σ.seth 6 (σ.sh 6 - 0 * (2 * ℓ + 2)) = σ := by simp [wseth_same]
    rw [e]; exact WExec.mono (WExec.skip σ) (by omega)
  | k + 1, σ, hL, hhL, hc => by
    have s1 := backRec_spec cap ℓ hl σ hL hhL hc
    have s2 := repBack_spec ℓ hl k (σ.seth 6 (σ.sh 6 - (2 * ℓ + 2))) (by simpa using hL) (by simpa using hhL)
      (by simpa using hc)
    rw [wseth_seth] at s2
    refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [Nat.add_mul, Nat.one_mul]; omega)
    congr 1
    simp only [WState.seth_sh, Function.update_self]
    rw [Nat.add_mul, Nat.one_mul]; omega

/-! ## The seed records -/

theorem flatMap_congr_mem {α β : Type} : ∀ (l : List α) (F G : α → List β), (∀ a ∈ l, F a = G a) →
    l.flatMap F = l.flatMap G
  | [], _, _, _ => rfl
  | a :: l, F, G, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
      flatMap_congr_mem l F G (fun b hb => h b (by simp [hb]))]

theorem ofFn_range {α : Type} : ∀ (k : ℕ) (g : ℕ → α), List.ofFn (fun j : Fin k => g j.val) = (List.range k).map g
  | 0, g => rfl
  | k + 1, g => by
    rw [List.ofFn_succ', List.range_succ, List.map_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append]
    rw [ofFn_range k g]; simp

theorem seedRecs_eq (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) :
    ((List.range 8).reverse.flatMap fun i => true :: frame (chunk (List.ofFn s) P.ell i)) =
      (SampMath.allC P s).flatMap fun c => true :: frame (binary P.ell c) := by
  unfold SampMath.allC coefsRev
  rw [show SampMath.coefs P s =
      fun j : Fin 8 => (fun i => Sampler.seedCoeff P.ell (SeedFix.bitsNum _ s) i) j.val from rfl,
    ofFn_range, ← List.map_reverse, List.flatMap_map]
  apply flatMap_congr_mem
  intro i hi
  have hi8 : i < 8 := by simpa using hi
  simp only [chunk]
  rw [← SampMath.chunk_eq P.ell s i hi8]

/-- The seed phase: the top chunk, the eight records, the end mark, the records' head back at `0`. -/
def seedW : WM 10 16 :=
  .seq (repW (rulerW 3 0 (.seq (.fwd 0) (.fwd 0))) 7) (.seq (crecsW 8) (.seq (emitW 6 false)
    (.seq (repW backRecW 8) (.bwd 6))))

def seedCost (ℓ : ℕ) : ℕ :=
  7 * (ℓ * 16 + 4) + 1 + (8 * (crecCost ℓ + 1) + 1 + (3 + 1 + (8 * (ℓ * 16 + 9) + 1 + 1)))

/-- **The seed records**: from the framed seed bits, `seedWord ℓ (allC P s)` on stream `6`, head at `0`. -/
theorem seed_spec (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (hl : P.ell ≤ cap) (σ : WState 10 16)
    (hS : σ.st 0 = frame (List.ofFn s)) (hhS : σ.sh 0 = 0) (hE : σ.st 6 = []) (hhE : σ.sh 6 = 0)
    (hL : σ.st 3 = List.replicate P.ell true) (hhL : σ.sh 3 = 0) (hc : σ.val 0 = 0) :
    ∃ τ, WExec cap seedW σ τ (seedCost P.ell) ∧ τ.st 6 = seedWord P.ell (SampMath.allC P s) ∧ τ.sh 6 = 0 ∧
      WFrame (fun j => j = 0 ∨ j = 6) (fun _ => False) σ τ := by
  have hw : (List.ofFn s).length = 8 * P.ell := List.length_ofFn
  have s1 := repSkip_spec cap P.ell hl 7 σ hL hhL hc
  obtain ⟨σ1, hσ1⟩ : ∃ τ : WState 10 16, τ = σ.seth 0 (σ.sh 0 + 7 * (2 * P.ell)) := ⟨_, rfl⟩
  rw [← hσ1] at s1
  have f1 : WFrame (fun j => j = 0 ∨ j = 6) (fun _ => False) σ σ1 := by
    rw [hσ1]; exact frame_seth _ _ σ 0 _ (Or.inl rfl)
  obtain ⟨τ2, s2, -, e26, eh26, f2⟩ := recs_spec cap P.ell (List.ofFn s) hw hl 8 le_rfl σ1
    (by rw [hσ1]; simp [hS, frame_eq_frameP])
    (by rw [hσ1]; simp only [WState.seth_sh, Function.update_self, hhS]; omega)
    (by rw [hσ1]; simp [hE, hhE]) (by rw [hσ1]; simp [hL]) (by rw [hσ1]; simp [hhL]) (by rw [hσ1]; simp [hc])
  obtain ⟨τ3, s3, c3⟩ := cp_emit cap 0 6 (by decide) false τ2 eh26
  have f3 : WFrame (fun j => j = 0 ∨ j = 6) (fun _ => False) τ2 τ3 :=
    ⟨fun i hi => c3.same i (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h)), fun r _ => by rw [c3.val], c3.cell⟩
  have f13 := f1.trans (f2.trans f3)
  have hL3 : τ3.st 3 = List.replicate P.ell true := (f13.1 3 (by decide)).1.trans hL
  have hhL3 : τ3.sh 3 = 0 := (f13.1 3 (by decide)).2.trans hhL
  have hc3 : τ3.val 0 = 0 := (f13.2.1 0 (fun h => h)).trans hc
  have s4 := repBack_spec cap P.ell hl 8 τ3 hL3 hhL3 hc3
  have s5 := WExec.bwd (cap := cap) 6 (τ3.seth 6 (τ3.sh 6 - 8 * (2 * P.ell + 2)))
  have hst : τ3.st 6 = seedWord P.ell (SampMath.allC P s) := by
    have e1 : σ1.st 6 = [] := by rw [hσ1]; simp [hE]
    rw [c3.out, e26, e1, List.nil_append, seedRecs_eq]; rfl
  have hlen : (SampMath.allC P s).length = 8 := by simp [SampMath.allC, coefsRev]
  have hsh : τ3.sh 6 = 8 * (2 * P.ell + 2) + 1 := by
    rw [c3.endO, hst, FinalPass.Hash4.seedWord_length, hlen]
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))), ?_, ?_, ?_⟩
  · simp only [WState.seth_st]; exact hst
  · simp only [WState.seth_sh, Function.update_self]; rw [hsh]; omega
  · exact f13.trans ((frame_seth _ _ τ3 6 _ (Or.inr rfl)).trans (frame_seth _ _ _ 6 _ (Or.inr rfl)))

end NearCubicWires.WireExponent3_5.UnionMachine.SampSeed
