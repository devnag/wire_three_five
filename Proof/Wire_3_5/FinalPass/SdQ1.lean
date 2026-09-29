import Proof.Wire_3_5.FinalPass.SdLoop
import Proof.Wire_3_5.FinalPass.TabFlat
import Proof.Wire_3_5.FinalPass.SeamsProg3

/-! # S4 (the seeds phase), part 35: S4's words at a star call, read (P3:3170-3178)

The facts linking S4's words (`s4Core2`) to the machine's numbers and streams:
* **`ppN_s4`**: the prep's `n` is the call's `n` (`(n − rb) + 2·(r/2)·b = n`, `r` even);
* **`seedWidth_eq`**, **`nE_s4`**: the seed width is `seedBits`, so `2^{width} = |GapSeed|`; **`ppReq_s4`**: the
  prep's request is the tables writer's (`reqT P.n len cap err L₀ L₁ |GapSeed|`);
* **`sampWord_sw`**: the sampled pairs' word is the sample loop's `sw (s·(r/2)) ps`;
* **`carTab_H`**: carrier `k`'s mask table starts with a gate whose first field has `tabH` bits, or reads `0` (no gate:
  `tabH = 0`); `Hof carriers k` that width;
* **`esOf`** (the seeds in the writer's order), **`tabWord_twW`**, **`twW_two`**: the writer's output is the seed
  loop's tables word, its first two frames the first seed's tables.

Paper quantity of the main type: the seeds phase's inputs as the call's parameters (P3:3170-3178). -/

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
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Primitive

theorem ppN_s4 (P : StarParams) {n : ℕ} (carriers : List (Stars.Carrier n)) (FP : GapParams) :
    ppN (Seams.s4Small2 P carriers FP) = P.n := by
  have hre : P.r / 2 * 2 = P.r := Nat.div_mul_cancel (even_iff_two_dvd.mp P.r_even)
  have hhb : P.r / 2 * P.b + P.r / 2 * P.b = P.r * P.b := by rw [← two_mul, ← mul_assoc, mul_comm 2, hre]
  have hrb := P.r_mul_b_le
  show P.n - P.r * P.b + P.r / 2 * P.b + P.r / 2 * P.b = P.n
  omega

theorem seedWidth_eq (FP : GapParams) : Seams.seedWidth FP = FP.seedBits := by
  unfold Seams.seedWidth GapParams.seedBits Filt.wOf
  have hw : FP.walkLen = 2 * (FP.errExp / 4) + 1 := rfl
  rw [hw]
  omega

theorem nE_s4 (P : StarParams) {n : ℕ} (carriers : List (Stars.Carrier n)) (FP : GapParams) :
    2 ^ (Seams.s4Small2 P carriers FP).getD 11 0 = Fintype.card (GapSeed FP) := by
  rw [card_gapSeed, ← seedWidth_eq]
  rfl

theorem ppReq_s4 (P : StarParams) {n : ℕ} (carriers : List (Stars.Carrier n)) (FP : GapParams) :
    ppReq (Seams.s4Small2 P carriers FP) = TabW.reqT P.n FP.len FP.cap FP.errExp (Seams.carLen carriers 0)
      (Seams.carLen carriers 1) (Fintype.card (GapSeed FP)) := by
  unfold ppReq
  rw [ppN_s4, nE_s4]
  rfl

theorem flatMap_ofFn' {α β : Type} : ∀ {n : ℕ} (f : Fin n → α) (g : α → List β),
    (List.ofFn f).flatMap g = (List.ofFn fun i => g (f i)).flatten
  | 0, f, g => by simp
  | n + 1, f, g => by
    rw [List.ofFn_succ, List.ofFn_succ, List.flatMap_cons, List.flatten_cons, flatMap_ofFn' (fun i => f i.succ) g]

theorem sampWord_sw (P : StarParams) (smp : CallSample P) :
    Seams.sampWord P smp = sw (P.s * (P.r / 2)) (List.ofFn smp.S) := by
  unfold Seams.sampWord sw
  rw [flatMap_ofFn']

/-! ## The carriers' weight widths -/

/-- Carrier `k`'s weight width (`0` past the carriers). -/
def Hof {n : ℕ} (carriers : List (Stars.Carrier n)) (k : Fin 2) : ℕ :=
  if h : k.val < carriers.length then PrimT.tabH (carriers.get ⟨k.val, h⟩) else 0

theorem tabH_of_mask_nil {n : ℕ} (X : Stars.Carrier n) (h : Corner.maskGates X = []) : PrimT.tabH X = 0 := by
  cases X with
  | nil => rfl
  | cons g G => simp [Corner.maskGates] at h

theorem gatesW_cons (H : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) (G : List (NormalizedThresholdGate n)) :
    ∃ rest, Corner.gatesW H (g :: G) =
      true :: (frameP (binary H (-g.threshold).toNat) ++ false :: rest) := by
  refine ⟨frame (binary H (-(-g.threshold)).toNat) ++ (List.ofFn g.weight).flatMap (Corner.pairW H) ++
    (G.flatMap (Corner.gateW H) ++ [false]), ?_⟩
  simp only [Corner.gatesW, List.flatMap_cons, Corner.gateW, Corner.pairW, frame_eq_frameP, List.cons_append,
    List.append_assoc, List.singleton_append, List.nil_append]

theorem carTab_H {n : ℕ} (carriers : List (Stars.Carrier n)) (k : Fin 2) :
    (∃ w rest, Seams.carTab carriers k.val = true :: (frameP w ++ false :: rest) ∧ w.length = Hof carriers k) ∨
      (readTapeBit (Seams.carTab carriers k.val) 0 = false ∧ Hof carriers k = 0) := by
  unfold Seams.carTab Hof
  by_cases hk : k.val < carriers.length
  · rw [dif_pos hk, dif_pos hk]
    cases hm : Corner.maskGates (carriers.get ⟨k.val, hk⟩) with
    | nil =>
      right
      refine ⟨rfl, tabH_of_mask_nil _ hm⟩
    | cons g G =>
      left
      obtain ⟨rest, hr⟩ := gatesW_cons (PrimT.tabH (carriers.get ⟨k.val, hk⟩)) g G
      exact ⟨_, rest, hr, Corner.binary_length' _ _⟩
  · rw [dif_neg hk, dif_neg hk]
    right
    exact ⟨rfl, rfl⟩

/-! ## The tables word -/

/-- The seeds in the tables writer's order. -/
def esOf (FP : GapParams) : List (GapSeed FP) :=
  (List.finRange (Fintype.card (GapSeed FP))).map (Enum.gapSeedEquiv FP).symm

theorem tabWord_twW (FP : GapParams) (L0 L1 : ℕ) : TabW.tabWord FP L0 L1 ++ [false] = twW FP (esOf FP) L0 L1 := rfl

theorem esOf_cons (FP : GapParams) : ∃ e es, esOf FP = e :: es := by
  have hpos := Enum.card_gapSeed_pos FP
  have hl : 0 < (esOf FP).length := by simp [esOf, hpos]
  exact List.exists_cons_of_length_pos hl

theorem twW_two (FP : GapParams) (L0 L1 : ℕ) : ∃ (e : GapSeed FP) (rest : List Bool),
    twW FP (esOf FP) L0 L1 = frameP (tb FP e L0) ++ false :: (frameP (tb FP e L1) ++ false :: rest) := by
  obtain ⟨e, es, h⟩ := esOf_cons FP
  rw [h, twW_cons]
  exact ⟨e, _, rfl⟩

end NearCubicWires.WireExponent3_5.FinalPass.Sd
