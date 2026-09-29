import Proof.Wire_3_5.Primitive.SeedFix.C4CapD
import Proof.Wire_3_5.Primitive.SeedFix.C4PadB

/-! # C4 capacity v2: the capacity chain `1^{2^m}`, `m = ⌊n/8⌋ + C`, from `1^n`

The free numbers of a SYM call reach `2^{Θ(R√B_S·L)} = 2^{o(n)}` (the finding 6, ruling), so the numbers machine's
capacity is `2^m` with `m` LINEAR in `n` and a small coefficient: `m = ⌊n/8⌋ + C`. Its square `2^{n/4 + 2C}` stays in the
selection class `2^{q/2 + c_sel k}` (P3:3098-3100). The chain reads `1^n` (the front's `gN1`), writes `1^{⌊n/8⌋ + C}`
(**`divW`**: `C` ones, then one per complete block of eight), `srcWord m` (`tsS`) and `1^{2^m}` (`srcS`), on the 39-tape layout with the output on tape `35`.

* `fwdN`, `divW`, `div_spec`, `divZ`, **`divS`**; `capExp2`, `capM2`, `capCost2`, **`cap_run2`**.

Paper quantity of the main type: the numbers machine's capacity `2^{capExp2 C n}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Cap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5.PrimT.C4Set

section Progs
variable (cap : ℕ)

/-- `k` steps forward on stream `0`. -/
def fwdN : ℕ → CW
  | 0 => .skip
  | k + 1 => .seq (.fwd 0) (fwdN k)

theorem fwdN_spec (a b : List Bool) (h1 : ℕ) : ∀ (k h0 : ℕ),
    WExec cap (fwdN k) (cst a b h0 h1) (cst a b (h0 + k) h1) (2 * k)
  | 0, h0 => WExec.cast cap (WExec.skip _) (by simp) (by simp)
  | k + 1, h0 => by
    have t1 : WExec cap (.fwd 0 : CW) (cst a b h0 h1) (cst a b (h0 + 1) h1) 1 := by
      refine WExec.cast cap (WExec.fwd 0 _) ?_ le_rfl
      apply WState.eq
      · funext j; fin_cases j <;> simp [cst, Function.update_apply]
      · rfl
      · funext r; exact r.elim0
      · rfl
    refine WExec.cast cap (WExec.seq t1 (fwdN_spec a b h1 k (h0 + 1))) ?_ (by omega)
    rw [Nat.add_assoc, Nat.add_comm 1 k]

/-- One block of eight: a one on stream `1`, eight steps on stream `0`. -/
def dbody : CW := .seq (.wr 1 true) (.seq (.fwd 1) (fwdN 8))

/-- **`⌊n/8⌋ + C` ones** from `1^n`: `C` ones, then one per complete block of eight. -/
def divW (C : ℕ) : CW := .seq (C4Pad.wword (List.replicate C true)) (.seq (fwdN 7) (.whs 0 dbody))

theorem dbody_spec (a : List Bool) (i h0 : ℕ) :
    WExec cap dbody (cst a (List.replicate i true) h0 i) (cst a (List.replicate (i + 1) true) (h0 + 8) (i + 1)) 20 := by
  have t1 : WExec cap (.wr 1 true : CW) (cst a (List.replicate i true) h0 i) (cst a (List.replicate (i + 1) true) h0 i) 1 := by
    refine WExec.cast cap (WExec.wr 1 true _) ?_ le_rfl
    apply WState.eq
    · rfl
    · funext j; fin_cases j <;> simp [cst, Function.update_apply, C4Front.write_rep]
    · funext r; exact r.elim0
    · rfl
  have t2 : WExec cap (.fwd 1 : CW) (cst a (List.replicate (i + 1) true) h0 i)
      (cst a (List.replicate (i + 1) true) h0 (i + 1)) 1 := by
    refine WExec.cast cap (WExec.fwd 1 _) ?_ le_rfl
    apply WState.eq
    · funext j; fin_cases j <;> simp [cst, Function.update_apply]
    · rfl
    · funext r; exact r.elim0
    · rfl
  exact WExec.cast cap (WExec.seq t1 (WExec.seq t2 (fwdN_spec cap a _ (i + 1) 8 h0))) rfl (by omega)

theorem dbody_spec' (a : List Bool) (i h0 i' h0' : ℕ) (hi : i' = i + 1) (hh : h0' = h0 + 8) :
    WExec cap dbody (cst a (List.replicate i true) h0 i) (cst a (List.replicate i' true) h0' i') 20 := by
  subst hi hh; exact dbody_spec cap a i h0

theorem dloop_spec (n : ℕ) : ∀ i, i ≤ n / 8 →
    WExec cap (.whs 0 dbody) (cst (List.replicate n true) (List.replicate i true) (8 * i + 7) i)
      (cst (List.replicate n true) (List.replicate (n / 8) true) (8 * (n / 8) + 7) (n / 8)) ((n / 8 - i) * 22 + 1)
  | i, hi => by
    by_cases hin : i = n / 8
    · subst hin
      have hb : wbit (cst (List.replicate n true) (List.replicate (n / 8) true) (8 * (n / 8) + 7) (n / 8)) 0 = false := by
        simp only [wbit, cst]
        have : ¬ 8 * (n / 8) + 7 < n := by omega
        simp [readTapeBit, List.getD_eq_default, this]
      exact WExec.mono (WExec.whsF hb) (by omega)
    · have hlt : i < n / 8 := by omega
      have hb : wbit (cst (List.replicate n true) (List.replicate i true) (8 * i + 7) i) 0 = true := by
        simp only [wbit, cst]
        have : 8 * i + 7 < n := by omega
        simp [readTapeBit, this]
      have ih := dloop_spec n (i + 1) (by omega)
      have hb2 := dbody_spec cap (List.replicate n true) i (8 * i + 7)
      rw [show 8 * i + 7 + 8 = 8 * (i + 1) + 7 by ring] at hb2
      refine WExec.cast cap (WExec.whsT hb hb2 ih) rfl ?_
      have : n / 8 - i = (n / 8 - (i + 1)) + 1 := by omega
      rw [this, Nat.add_mul]; omega
  termination_by i => n / 8 - i

/-- The divide's step bound. -/
def divCost (C n : ℕ) : ℕ := 4 * C + 1 + (14 + 1 + ((n / 8) * 22 + 1))

theorem div_spec (C n : ℕ) :
    WExec cap (divW C) (cst (List.replicate n true) [] 0 0)
      (cst (List.replicate n true) (List.replicate (C + n / 8) true) (8 * (n / 8) + 7) (C + n / 8)) (divCost C n) := by
  have t1 := C4Pad.wword_spec cap (List.replicate n true) 0 (List.replicate C true) []
  simp only [List.nil_append, List.length_replicate, List.length_nil] at t1
  have t2 := fwdN_spec cap (List.replicate n true) (List.replicate C true) C 7 0
  have t3 := dloop_spec cap n 0 (Nat.zero_le _)
  -- stream 1 starts at `1^C`: shift the loop by `C`
  have t3' : WExec cap (.whs 0 dbody) (cst (List.replicate n true) (List.replicate C true) 7 C)
      (cst (List.replicate n true) (List.replicate (C + n / 8) true) (8 * (n / 8) + 7) (C + n / 8))
      ((n / 8 - 0) * 22 + 1) := by
    have key : ∀ i, i ≤ n / 8 →
        WExec cap (.whs 0 dbody) (cst (List.replicate n true) (List.replicate (C + i) true) (8 * i + 7) (C + i))
          (cst (List.replicate n true) (List.replicate (C + n / 8) true) (8 * (n / 8) + 7) (C + n / 8))
          ((n / 8 - i) * 22 + 1) := by
      intro i hi
      induction h : n / 8 - i generalizing i with
      | zero =>
        have hin : i = n / 8 := by omega
        subst hin
        have hb : wbit (cst (List.replicate n true) (List.replicate (C + n / 8) true) (8 * (n / 8) + 7) (C + n / 8)) 0
            = false := by
          simp only [wbit, cst]
          have : ¬ 8 * (n / 8) + 7 < n := by omega
          simp [readTapeBit, List.getD_eq_default, this]
        exact WExec.mono (WExec.whsF hb) (by omega)
      | succ d ih =>
        have hlt : i < n / 8 := by omega
        have hb : wbit (cst (List.replicate n true) (List.replicate (C + i) true) (8 * i + 7) (C + i)) 0 = true := by
          simp only [wbit, cst]
          have : 8 * i + 7 < n := by omega
          simp [readTapeBit, this]
        have hb2 := dbody_spec' cap (List.replicate n true) (C + i) (8 * i + 7) (C + (i + 1)) (8 * (i + 1) + 7)
          (by ring) (by ring)
        have ih' := ih (i + 1) (by omega) (by omega)
        refine WExec.cast cap (WExec.whsT hb hb2 ih') rfl ?_
        rw [Nat.add_mul]; omega
    have := key 0 (Nat.zero_le _)
    have e : cst (List.replicate n true) (List.replicate (C + 0) true) (8 * 0 + 7) (C + 0) =
        cst (List.replicate n true) (List.replicate C true) 7 C := by simp
    rw [e] at this
    exact this
  refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 t3')) rfl ?_
  unfold divCost; omega

end Progs

/-- The divide machine. -/
noncomputable def divZ (C : ℕ) := MaskedReset.machine (divW C).toProg.compile (fun _ => true)

/-- **`1^{⌊n/8⌋ + C}` from `1^n`** on tape `0`: on tape `2`. -/
theorem divS (C n : ℕ) : ∃ tout : Fin (1 + 2 + 0 + 1) → List Bool,
    Step (divZ C) (2 * divCost C n + 2) (fun _ => 0) (fun j => if j.val = 0 then List.replicate n true else [])
      (fun _ => 0) tout ∧ tout ⟨0, by omega⟩ = List.replicate n true ∧
      tout ⟨2, by omega⟩ = List.replicate (n / 8 + C) true := by
  obtain ⟨A', hs, hA⟩ := C4Pipe.wm_blank 0 (divCost C n) (divW C) (cst (List.replicate n true) [] 0 0) _ _
    (div_spec 0 C n) (fun i => by fin_cases i <;> rfl) (fun r => r.elim0) rfl le_rfl
  refine ⟨A', hs.congr_in rfl ?_, hA 0, ?_⟩
  · funext j
    fin_cases j <;> rfl
  · rw [show n / 8 + C = C + n / 8 from Nat.add_comm _ _]; exact hA 1

/-- **The capacity's exponent, v2**: `m = ⌊n/8⌋ + C`. -/
def capExp2 (C n : ℕ) : ℕ := n / 8 + C

/-- **The capacity chain, v2**, on `39` tapes: tape `0` the unary `1^n`; the divide (`1 … 4`), the source word
(`5 … 8`), the CapReader (`27 … 38`, its output on tape `35`). -/
noncomputable def capM2 (C : ℕ) :=
  Composition.machine (RecoveryFocus.machine (slx 1 (by norm_num) (ext0 (⟨0, by norm_num⟩ : Fin 39))) (divZ C))
  (Composition.machine (RecoveryFocus.machine (slx 5 (by norm_num) (ext0 (⟨3, by norm_num⟩ : Fin 39))) tsZ)
    (RecoveryFocus.machine (slx 27 (by norm_num) (ext0 (⟨7, by norm_num⟩ : Fin 39))) crM))

/-- The chain's step bound. -/
def capCost2 (C n : ℕ) : ℕ :=
  2 * divCost C n + 2 + 1 + (2 * tsCost (capExp2 C n) + 2 + 1 + srcCost (capExp2 C n))

/-- **The capacity chain's run, v2**: from `1^n` on tape `0` (every other tape blank), `1^n` kept and `1^{2^m}` on
tape `35`, `m = capExp2 C n`, every head at `0`. -/
theorem cap_run2 (C n : ℕ) :
    ∃ tout : Fin 39 → List Bool, Step (capM2 C) (capCost2 C n) (fun _ => 0)
      (fun j => if j.val = 0 then List.replicate n true else []) (fun _ => 0) tout ∧
      tout ⟨0, by norm_num⟩ = List.replicate n true ∧
      tout ⟨35, by norm_num⟩ = List.replicate (2 ^ capExp2 C n) true := by
  set B0 : Fin 39 → List Bool := fun j => if j.val = 0 then List.replicate n true else [] with hB0
  -- 1: the divide
  obtain ⟨t1, h1, e10, e12⟩ := divS C n
  obtain ⟨B1, s1, bl1, un1, pv1, ex1⟩ := stage0 h1 (by norm_num) 1 (by norm_num) ⟨0, by norm_num⟩ (by norm_num) B0
    (by simp [hB0]) (fun i hi => by simp [hB0]; omega)
  have f1b : B1 ⟨3, by norm_num⟩ = List.replicate (capExp2 C n) true :=
    (pv1 ⟨2, by norm_num⟩ _ (by norm_num) rfl).trans e12
  -- 2: the source word
  obtain ⟨t2, h2, e22⟩ := tsS (capExp2 C n)
  obtain ⟨B2, s2, bl2, un2, pv2, ex2⟩ := stage0 h2 (by norm_num) 5 (by norm_num) ⟨3, by norm_num⟩ (by norm_num) B1
    f1b (fun i hi => bl1 i (by omega))
  have f2b : B2 ⟨7, by norm_num⟩ = PrimAsm.NumsX.srcWord (capExp2 C n) :=
    (pv2 ⟨2, by norm_num⟩ _ (by norm_num) rfl).trans e22
  -- 3: the CapReader
  obtain ⟨t3, h3, e30, e38, e39⟩ := srcS (capExp2 C n)
  obtain ⟨B3, s3, bl3, un3, pv3, ex3⟩ := stage0 h3 (by norm_num) 27 (by norm_num) ⟨7, by norm_num⟩ (by norm_num) B2
    f2b (fun i hi => bl2 i (by omega))
  refine ⟨B3, s1.seq (s2.seq s3), ?_, (pv3 ⟨8, by norm_num⟩ _ (by norm_num) rfl).trans e38⟩
  rw [un3 ⟨0, by norm_num⟩ (by norm_num) (by simp), un2 ⟨0, by norm_num⟩ (by norm_num) (by simp), ex1, e10]

/-- **Every `c·(B+1)²` is below `n/16` up to a constant** (the constant absorbs the small `n`): the free numbers'
`2^{⌊n/16⌋ + d·β²}` fit `2^{⌊n/8⌋ + C}` once `C ≥ K₀`. -/
theorem mul_sq_le_div16 (c : ℕ) : ∃ K0 : ℕ, ∀ n : ℕ, c * (natBitLength n + 1) ^ 2 ≤ n / 16 + K0 := by
  obtain ⟨K, hK⟩ := capExp_le_half (8 * c)
  refine ⟨K + 1, fun n => ?_⟩
  have h := hK n
  have e : 8 * c * (natBitLength n + 1) ^ 2 = 8 * (c * (natBitLength n + 1) ^ 2) := by ring
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4Cap
