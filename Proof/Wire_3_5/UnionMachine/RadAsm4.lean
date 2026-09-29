import Proof.Wire_3_5.UnionMachine.RadAsm3

/-! # RADIX assembly (4): stages 3, 4 and 5a's inputs, composed (P3:2585-2623)

From the state after stage 2, the first half of the RADIX setup's stages on the cell, each composed from the phases of
files (1)–(3) with the frame predicate `Keep`:

* `rad_ne` (registers and streams apart by their values), `scK` (the block writer's scratch `139`, `140`),
  `keep_post`;
* `run23` / **`run23_spec`**: the numbers and the setup fields (the record stream `3` holds `fieldsWordB …`);
* `run456` / **`run456_spec`**: the seed word, the zero frames and the window word.

Paper quantity of the main type: the RADIX row's setup fields and the table builder's inputs. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

/-- Registers and streams of the cell apart (by their values). -/
macro "rad_ne" : tactic =>
  `(tactic| (simp [Fin.ext_iff, sk_val, rIn_val, rY_val, rQ_val, rF_val, rT_val, rB_val, rZ_val, rG_val,
    RadSpec.radBlkK] <;> omega))

variable (cap : ℕ) (x : ℕ)

/-- The block writer's scratch streams `139`, `140`. -/
def scK (i : Fin 2) : Fin (LNS x + 1) := sk x ⟨139 + i.val, by omega⟩

theorem scK_val (i : Fin 2) : (scK x i).val = 139 + i.val := rfl

section Post
variable {ns nr : ℕ} (O T GS : Fin (ns + 1)) (OP : Fin nr)

theorem keep_post (σ : WState ns nr) (uO uT : List Bool) (g : ℕ) :
    Keep σ (RadDigL.post O T GS OP σ uO uT g) (fun i => i = O ∨ i = T ∨ i = GS) (fun r => r = OP) := by
  refine ⟨fun i hi => ?_, fun r hr => ?_⟩
  · simp only [not_or] at hi
    simp [RadDigL.post, Function.update_apply, hi.1, hi.2.1, hi.2.2]
  · simp [RadDigL.post, Function.update_apply, hr]

end Post

/-! ## Stages 3 and 4 -/

def run23 : WM (LNS x) LNR := .seq (ph2 x) (ph3 x)

theorem run23_spec (σ : WState (LNS x) LNR) (prs : List (ℕ × ℕ)) (G row M τ J p s : ℕ)
    (h131 : σ.st (sk x 131) = RadScan.recsW prs) (h131h : σ.sh (sk x 131) = 0)
    (h3 : σ.st (sk x 3) = []) (h3h : σ.sh (sk x 3) = 0)
    (hG : σ.val (rIn 4) = G) (hrow : σ.val (rIn 3) = row) (hM : σ.val (rIn 13) = M)
    (hτ : σ.val (rIn 12) = τ) (hJ : σ.val (rIn 16) = J) (hp : σ.val (rIn 1) = p) (hs : σ.val (rIn 2) = s)
    (zQ : ∀ i, σ.val (rQ i) = 0) (zF : ∀ i, σ.val (rF i) = 0) (zY : ∀ i, σ.val (rY i) = 0)
    (hτ1 : 1 ≤ τ) (hp2 : 2 ≤ p) (hsp : s < p) (c0 : 2 * (M + τ + G + J + p + row + 1) ≤ cap)
    (c1 : (RadScan.recsW prs).length + (prs.map Prod.fst).sum + (prs.map Prod.snd).sum + G + row + M + τ + J + p ≤ cap)
    (c2 : (1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45 + 1048576 +
      4 * row + J + 8 ≤ cap)
    (c3 : RadFieldsP.fieldsLen ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40)
      ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1)
      ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) M τ p ≤ cap) :
    ∃ σ3 : WState (LNS x) LNR, WExec cap (run23 x) σ σ3
        (ph2Cost (RadScan.recsW prs).length (prs.map Prod.snd).sum G row M τ J p cap + 1 +
          ph3Cost cap ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40)
            ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1)
            ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) M τ p s) ∧
      Keep σ σ3 (fun i => i = sk x 3) (fun r => r.val < 97 ∨ r.val = 98) ∧
      σ3.st (sk x 3) = RadFieldsP.fieldsWordB
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40)
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M τ p s
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45) ∧
      σ3.sh (sk x 3) = (RadFieldsP.fieldsWordB
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40)
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M τ p s
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45)).length ∧
      σ3.val (rY 0) = (RadFieldsP.fieldsWordB
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40)
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 40 + 1) M τ p s
          ((1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length) ^ 45)).length ∧
      σ3.val (rQ 7) = (RadScan.recsW prs).length ∧ σ3.val (rQ 8) = 4 * (prs.map Prod.snd).sum + 1 := by
  set U := 1048576 * xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length with hU
  have hU1 : 1 ≤ U := by
    have : 1 ≤ xOf G row M τ J p (prs.map Prod.snd).sum (RadScan.recsW prs).length := by
      unfold xOf RadSpec.radX; omega
    omega
  have hU40 : U ^ 40 ≤ U ^ 45 := Nat.pow_le_pow_right hU1 (by norm_num)
  obtain ⟨σ2, e2, K2, q0, q1, q2, q3, q4, q5, q7, q8, q9, q10, q12, q13, q14, q15⟩ :=
    ph2_spec cap x σ prs G row M τ J p h131 h131h hG hrow hM hτ hJ hp zY zQ c1 c2
  obtain ⟨σ3, e3, K3, f3, f3h, f3v⟩ := ph3_spec cap x σ2 (U ^ 40) (U ^ 40 + 1) (U ^ 45) M τ p s q13 q15 q14
    (by rw [K2.val (by rad_ne)]; exact hM) (by rw [K2.val (by rad_ne)]; exact hτ)
    (by rw [K2.val (by rad_ne)]; exact hp) (by rw [K2.val (by rad_ne)]; exact hs)
    (fun i => by rw [K2.val (by rad_ne)]; exact zF i)
    (by rw [K2.val (by rad_ne)]; exact zY 0) (by rw [K2.val (by rad_ne)]; exact zY 4)
    (by rw [K2.st (by rad_ne)]; exact h3) (by rw [K2.sh (by rad_ne)]; exact h3h)
    (by omega) (by omega) (by omega) (by omega) hτ1 (by omega) hp2 hsp (by omega) c3
  refine ⟨σ3, WExec.seq e2 e3, (K2.trans K3).mono (fun i h => by simpa using h) (fun r h => by
      rcases h with h | h
      · rcases h with h | h
        · subst h; simp [rY_val]
        · omega
      · rcases h with h | h
        · subst h; simp [rY_val]
        · omega), f3, f3h, f3v, ?_, ?_⟩
  · rw [K3.val (by rad_ne)]; exact q7
  · rw [K3.val (by rad_ne)]; exact q8

/-! ## The seed word, the zero frames, the window word -/

def run456 : WM (LNS x) LNR := .seq (ph4 x) (.seq (ph5 x) (ph6 x))

theorem run456_spec (σ : WState (LNS x) LNR) (A l : List Bool) (t ℓ M G J : ℕ) (w : List Bool)
    (hl : l.length = 2 * t * ℓ) (h0 : σ.st (sk x 0) = frame (A ++ frame l)) (h0h : σ.sh (sk x 0) = 0)
    (hbl : ∀ k : Fin 161, 141 ≤ k.val → k.val ≤ 148 → σ.st (sk x k) = [] ∧ σ.sh (sk x k) = 0)
    (hS : σ.st (sk x 131) = w) (hSh : σ.sh (sk x 131) = 0)
    (ht : σ.val (rIn 17) = t) (hℓ : σ.val (rIn 18) = ℓ) (hM : σ.val (rIn 13) = M) (hG : σ.val (rIn 4) = G)
    (hJ : σ.val (rIn 16) = J) (hw : σ.val (rQ 7) = w.length) (zT : ∀ i, σ.val (rT i) = 0)
    (zY : ∀ i : Fin 32, 4 ≤ i.val → i.val ≤ 16 → σ.val (rY i) = 0)
    (c4 : 2 * (A ++ frame l).length + 2 * t * (2 * ℓ + 2) + 4 * (t * ℓ) + ℓ + t + 2 ≤ cap)
    (c5 : 2 * ℓ + 1 ≤ cap) (c6 : M + G + J + w.length + 4 ≤ cap) :
    ∃ σ6 : WState (LNS x) LNR, WExec cap (run456 x) σ σ6
        (((18 * t + 3) + 1 + ((18 * ℓ + 3) + 1 + RadSeed.hashSeedCost t ℓ (A ++ frame l).length)) + 1 +
          (((18 * ℓ + 3) + 1 + ((60 * ℓ + 40) + 1 + ((60 * ℓ + 40) + 1 + ((60 * ℓ + 40) + 1 + (60 * ℓ + 40))))) + 1 +
          ((18 * M + 3) + 1 + ((18 * G + 3) + 1 + ((18 * J + 3) + 1 + ((18 * w.length + 3) + 1 +
            RadWin.winCost M G J w.length)))))) ∧
      Keep σ σ6 (fun i => 141 ≤ i.val ∧ i.val ≤ 148)
        (fun r => r.val = 102 ∨ (109 ≤ r.val ∧ r.val ≤ 112) ∨ (128 ≤ r.val ∧ r.val < 138)) ∧
      σ6.st (sk x 142) = [] ∧ σ6.sh (sk x 142) = 0 ∧
      σ6.st (sk x 143) = FinalPass.ListEval.unary M ++ FinalPass.ListEval.unary G ++ FinalPass.ListEval.unary J ++ w ++
        [false] ∧ σ6.sh (sk x 143) = 0 ∧
      σ6.st (sk x 144) = FinalPass.HashSeed.revWord l ℓ (2 * t) ∧ σ6.sh (sk x 144) = 0 ∧
      ∀ k : Fin 161, 145 ≤ k.val → k.val ≤ 148 →
        σ6.st (sk x k) = frame (List.replicate ℓ false) ∧ σ6.sh (sk x k) = 0 := by
  have b141 := hbl 141 (by decide) (by decide)
  have b142 := hbl 142 (by decide) (by decide)
  have b143 := hbl 143 (by decide) (by decide)
  have b144 := hbl 144 (by decide) (by decide)
  obtain ⟨σ4, e4, K4, g141, g141h, g144, g144h⟩ := ph4_spec cap x σ A l t ℓ hl h0 h0h b141.1 b141.2 b144.1 b144.2
    ht hℓ zT (zY 4 (by decide) (by decide)) c4
  obtain ⟨σ5, e5, K5, g145⟩ := ph5_spec cap x σ4 ℓ (by rw [K4.val (by rad_ne)]; exact hℓ)
    (fun k h1 h2 => by
      rw [K4.st (by rad_ne), K4.sh (by rad_ne)]
      exact hbl k (by omega) h2)
    (fun i h1 h2 => by rw [K4.val (by rad_ne)]; exact zY i h1 (by omega)) c5
  obtain ⟨σ6, e6, K6, g143, g143h⟩ := ph6_spec cap x σ5 w M G J
    (by rw [(K4.trans K5).val (by rad_ne)]; exact hM) (by rw [(K4.trans K5).val (by rad_ne)]; exact hG)
    (by rw [(K4.trans K5).val (by rad_ne)]; exact hJ) (by rw [(K4.trans K5).val (by rad_ne)]; exact hw)
    (by rw [(K4.trans K5).st (by rad_ne)]; exact hS) (by rw [(K4.trans K5).sh (by rad_ne)]; exact hSh)
    (by rw [(K4.trans K5).st (by rad_ne)]; exact b143.1) (by rw [(K4.trans K5).sh (by rad_ne)]; exact b143.2)
    (fun i h1 h2 => by rw [(K4.trans K5).val (by rad_ne)]; exact zY i (by omega) h2)
    (by rw [(K4.trans K5).val (by rad_ne)]; exact zY 4 (by decide) (by decide)) c6
  refine ⟨σ6, WExec.seq e4 (WExec.seq e5 e6), ((K4.trans K5).trans K6).mono (fun i h => by
      simp only [Fin.ext_iff, sk_val] at h; omega) (fun r h => by
      simp only [Fin.ext_iff, rY_val] at h; omega), ?_, ?_, g143, g143h, ?_, ?_, fun k h1 h2 => ?_⟩
  · rw [((K4.trans K5).trans K6).st (by rad_ne)]; exact b142.1
  · rw [((K4.trans K5).trans K6).sh (by rad_ne)]; exact b142.2
  · rw [(K5.trans K6).st (by rad_ne)]; exact g144
  · rw [(K5.trans K6).sh (by rad_ne)]; exact g144h
  · rw [K6.st (by rad_ne), K6.sh (by rad_ne)]; exact g145 k h1 h2

end NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
