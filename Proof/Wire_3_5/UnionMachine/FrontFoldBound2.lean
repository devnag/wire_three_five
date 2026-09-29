import Proof.Wire_3_5.UnionMachine.FrontFoldBound

/-! # C6 front, U5, the writers' fold (b): the round fuel, the widths and the stage's polynomials

With `B = s + 2`, `s` bounding `q`, the variable count, the systematic count and the atoms' code widths:
* `eT`: the envelope capacity's exponent (`T = 2^eT·(s+1)^eT ≥ B^eT`, **`envFit`**);
* `eM`: the round's exponent (**`rcost_le`**: every round within `B^(eM+6)`);
* **`width_le`**: every kept tape of every round state within `B^eM`.

Paper quantity: none (the front's time, a fixed polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldLoop
open NearCubicWires.WireExponent3_5.UnionMachine.CWIface (ParityWriterJ CarrierWriterJ)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (bitmap codesWord carrierOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode (envCodeCost atomsOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvRound (foldCwE)
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (cropBCost appendBCost)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldCat (catCost efCost)
open NearCubicWires.BlockPlatform.UnaryCalc (value tapes)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-! ## Generic width facts -/

theorem flat_frame_le (L : ℕ) : ∀ ws : List (List Bool), (∀ w ∈ ws, w.length ≤ L) →
    (ws.flatMap frame).length ≤ ws.length * (2 * L + 1)
  | [], _ => by simp
  | w :: ws, h => by
    rw [List.flatMap_cons, List.length_append, frame_length, List.length_cons]
    have h1 := h w (by simp)
    have h2 := flat_frame_le L ws (fun z hz => h z (by simp [hz]))
    rw [Nat.add_mul, one_mul]; omega

theorem Qf_len {tP tC : ℕ} (ks : List (List Bool)) (N : ℕ) (hk : ∀ k ∈ ks, k.length ≤ N)
    (t : Fin (1220 + tP + tC)) : (FrontFoldRound.Qf ks t).length ≤ N := by
  unfold FrontFoldRound.Qf
  rw [List.getD_eq_getElem?_getD]
  cases h : ks[t.val]? with
  | none => simp
  | some k => simp only [Option.getD_some]; exact hk k (List.mem_of_getElem? h)

/-- The round's fuel from bounds on its stages. -/
theorem roundCost_le {B : ℕ} (hB : 2 ≤ B) (Wb Wa X cP cC cE M : ℕ) (pcs crs : List (List Bool)) (a p y : List Bool)
    (h1 : cropBCost X Wb ≤ B ^ M) (h2 : cP ≤ B ^ M) (h3 : appendBCost pcs p ≤ B ^ M) (h4 : cropBCost X Wa ≤ B ^ M)
    (h5 : catCost a.length p.length X ≤ B ^ M) (h6 : cC ≤ B ^ M) (h7 : appendBCost crs y ≤ B ^ M) (h8 : cE ≤ B ^ M)
    (h9 : efCost X ≤ B ^ M) :
    FrontFoldRound.roundCost Wb Wa X cP cC cE pcs crs a p y ≤ B ^ (M + 6) := by
  have hp := bpos hB M
  have hE : 64 * B ^ M ≤ B ^ (M + 6) := bcm hB 64 6 (by norm_num) le_rfl
  unfold FrontFoldRound.roundCost
  generalize cropBCost X Wb = x1 at *
  generalize appendBCost pcs p = x3 at *
  generalize cropBCost X Wa = x4 at *
  generalize catCost a.length p.length X = x5 at *
  generalize appendBCost crs y = x7 at *
  generalize efCost X = x9 at *
  generalize B ^ M = P at *
  generalize B ^ (M + 6) = Q at *
  omega

/-! ## The exponents -/

section Exps
variable {m : Mode} {q : ℕ}

/-- The envelope capacity's exponent. -/
def eT (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (deg : ℕ) : ℕ := 26 * (lc Pw Cw + 2) + 92 + deg

theorem pow_two_mul (s e : ℕ) : (s + 2) ^ e ≤ value e (2 ^ e) s := by
  unfold value
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) e

variable (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (F : FoldIn m q) (s deg : ℕ)

/-- **The envelope capacity fits every carrier.** -/
theorem envFit (hq : q ≤ s) (X : ℕ) (hA : (codesWord m (F.atoms X)).length ≤ s) :
    EnvFit (F.car X) deg (value (eT Pw Cw deg) (2 ^ eT Pw Cw deg) s) := by
  have hB : 2 ≤ s + 2 := by omega
  have hT := pow_two_mul s (eT Pw Cw deg)
  have hW := Wc_le Pw Cw F s hq X hA
  set W := natBitLength (Stars.Carrier.code (F.car X)) with hWd
  set w := lc Pw Cw + 2 with hw
  have hge : ∀ e, e ≤ eT Pw Cw deg → (s + 2) ^ e ≤ value (eT Pw Cw deg) (2 ^ eT Pw Cw deg) s :=
    fun e he => (Nat.pow_le_pow_right (by omega) he).trans hT
  have hWle : W ≤ (s + 2) ^ w := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (atoms_le _).trans (hWle.trans (hge w (by unfold eT; omega)))
  · have h1 := frames_le (Stars.Carrier.code (F.car X))
    have h2 : 2 * W + 1 ≤ (s + 2) ^ (w + 2) := by
      have := bpos hB w; exact bcm hB 3 2 (by norm_num) (by omega)
    have h3 := Nat.mul_le_mul hWle h2
    rw [← pow_add] at h3
    exact h1.trans (h3.trans (hge _ (by unfold eT; omega)))
  · exact (Nat.pow_le_pow_left (show q + 1 ≤ s + 2 by omega) deg).trans (hge deg (by unfold eT; omega))
  · have h1 := foldCwE_le hB W (atomsOf (Stars.Carrier.code (F.car X))).length w (atoms_le _) hW
    have h2 := badd hB h1 (bpos hB (26 * w + 91))
    exact h2.trans (hge _ (by unfold eT; omega))

end Exps

/-! ## The round -/

section Round
variable {m : Mode} {q : ℕ}

theorem crop_le {B : ℕ} (hB : 2 ≤ B) (X W : ℕ) (hX : X ≤ B) (hW : W ≤ B) : cropBCost X W ≤ B ^ 9 := by
  have h1 : X * (5 * W + 8) ≤ B * (13 * B) := Nat.mul_le_mul hX (by omega)
  have h2 : B * (13 * B) = 13 * B ^ 2 := by ring
  have h3 : B ≤ B ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 := bpos hB 2
  have h5 : cropBCost X W ≤ 77 * B ^ 2 := by unfold cropBCost; omega
  exact bcm hB 77 7 (by norm_num) h5

theorem sumFrame_le {B : ℕ} (hB : 2 ≤ B) (X l : ℕ) (hX : X ≤ B) (f : ℕ → List Bool)
    (hf : ∀ i < X, (f i).length ≤ B ^ l) : (((List.range X).map f).flatMap frame).length ≤ B ^ (l + 3) := by
  have h1 := flat_frame_le (B ^ l) ((List.range X).map f) (by
    intro w hw; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw; exact hf i (List.mem_range.mp hi))
  rw [List.length_map, List.length_range] at h1
  have h2 : X * (2 * B ^ l + 1) ≤ B * (3 * B ^ l) := Nat.mul_le_mul hX (by have := bpos hB l; omega)
  have h3 : B * (3 * B ^ l) = 3 * B ^ (l + 1) := by rw [pow_succ]; ring
  have h4 : 3 * B ^ (l + 1) ≤ B ^ (l + 3) := bcm hB 3 2 (by norm_num) le_rfl
  omega

end Round

/-! ## The widths and the stage -/

section Stage
variable {m : Mode} {q : ℕ}
variable (Pw : ParityWriterJ m) (Cw : CarrierWriterJ m) (F : FoldIn m q) (s deg : ℕ)

theorem as_len (hA : ∀ X < F.nv, (codesWord m (F.atoms X)).length ≤ s) : ∀ a ∈ F.as, a.length ≤ s := by
  intro a ha
  obtain ⟨X, hX, rfl⟩ := List.mem_map.mp ha
  exact hA X (List.mem_range.mp hX)

end Stage

/-! ## The stage's fuel -/

section Cost
variable {m : Mode} {q : ℕ}

theorem budget_le (D C n s : ℕ) (hn : n ≤ s) :
    PCPSerializerCapacity.Power.budget D C n ≤ BlockPlatform.UnaryCalc.polyCoefficient D C * (s + 2) ^ (D + 1) := by
  have h : PCPSerializerCapacity.Power.budget D C n ≤ BlockPlatform.UnaryCalc.polyCoefficient D C * (n + 1) ^ (D + 1) :=
    BlockPlatform.UnaryCalc.poly_cost_polyBounded D C n
  exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

end Cost

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound
