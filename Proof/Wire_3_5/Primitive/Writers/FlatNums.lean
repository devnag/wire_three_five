import Proof.Wire_3_5.Primitive.Writers.SymQM

/-! # PA (d): the amplified list's numbers in unary registers (build once: the SYM decode)

P3:1505-1511 (list:flatten: the amplified list at `(M, B, errExp)`: the base list's rank `max(J, ⌈log₂M⌉)` with
`J = ⌈log₂B⌉ + 9`, the walk over Theorem 2.5's Toeplitz seeds on the vertex side `2^{sideBits(rank)}`, the odd walk
length `t = 2⌊errExp/4⌋ + 1`) and `FlatListParams.card_flatSeed` (`|FlatSeed| = side²·(16^{40})^{t−1}`): from `M`,
`B`, `errExp` in a block's first three registers, one program leaves `J`, `⌈log₂M⌉`, the rank, the side bits, the walk
length, `log₂|FlatSeed|` and `|FlatSeed|` in the next seven, the rest of the block zero, everything outside the block
unchanged. It re-composes SymQM's verified parts (`clogW`, `maxW`, `sbW`, `eW`, `sgB`, `pow2W`); the walk length is
computed from `errExp` directly (SymQM's `wlW` takes `L` with `errExp = L + 5`).

* the block `F : Fin 20 ↪ Fin nr`: `0` M, `1` B, `2` errExp (inputs); `3` J, `4` ⌈log₂M⌉, `5` rank, `6` side bits,
  `7` walk length, `8` `log₂|FlatSeed|`, `9` `|FlatSeed|` (outputs); `10 … 19` scratch (zero before and after);
* `flatNumsW`, **`flatNums_spec`** (the state `flatOut = blk F σ (flatVec M B errExp)`, within `110·sq cap`);
* the anchors `rkv_eq`, `sbv_eq`, `wlv_eq`, `card_eq`, and **`flatNums_run`** at `P : FlatListParams`
  (`flatOut_rank`, `flatOut_side`, `flatOut_walk`, `flatOut_card`).

Paper quantity of the main type: `FlatListParams.base.rank`, `toeplitzWalkSideBits` (so `side`), `walkLen` and
`Fintype.card FlatSeed` of the amplified list. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.FlatNums
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.CapNum
open NearCubicWires.WireExponent3_5.PrimAsm.SymQM
open NearCubicWires.WireExponent3_5.Lists

/-! ## The values -/

/-- The rank `max(⌈log₂B⌉ + 9, ⌈log₂M⌉)`. -/
def rkv (M B : ℕ) : ℕ := max (Nat.clog 2 B + 9) (Nat.clog 2 M)

/-- The side bits `⌊3·rank/2⌋`. -/
def sbv (M B : ℕ) : ℕ := (rkv M B + rkv M B + rkv M B) / 2

/-- The walk length `2⌊errExp/4⌋ + 1`. -/
def wlv (e : ℕ) : ℕ := 2 * (e / 2 / 2) + 1

/-- `log₂|FlatSeed| = 2·sideBits + 160·(t − 1)`. -/
def fbv (M B e : ℕ) : ℕ := 0 + sbv M B + sbv M B + (wlv e - 1) * 160

/-- The block's values after the program. -/
def flatVec (M B e : ℕ) : Fin 20 → ℕ :=
  ![M, B, e, Nat.clog 2 B + 9, Nat.clog 2 M, rkv M B, sbv M B, wlv e, fbv M B e, 2 ^ fbv M B e,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem rkv_ge (M B : ℕ) : 9 ≤ rkv M B := by unfold rkv; omega

theorem rkv_eq (P : FlatListParams) : rkv P.M P.B = P.base.rank := rfl

theorem sbv_eq (P : FlatListParams) : sbv P.M P.B = SupplierWalkBridge.toeplitzWalkSideBits P.base.rank := by
  have := rkv_ge P.M P.B
  rw [← rkv_eq]
  unfold sbv SupplierWalkBridge.toeplitzWalkSideBits SupplierWalkBridge.toeplitzSeedBits
  congr 1
  omega

theorem wlv_eq (P : FlatListParams) : wlv P.errExp = P.walkLen := by
  unfold wlv FlatListParams.walkLen
  omega

/-- `log₂|FlatSeed|` at the paper's parameters. -/
def flatBits (P : FlatListParams) : ℕ :=
  2 * SupplierWalkBridge.toeplitzWalkSideBits P.base.rank + 160 * (P.walkLen - 1)

theorem fbv_eq (P : FlatListParams) : fbv P.M P.B P.errExp = flatBits P := by
  unfold fbv flatBits
  rw [sbv_eq, wlv_eq]
  omega

theorem card_eq (P : FlatListParams) : 2 ^ fbv P.M P.B P.errExp = Fintype.card P.FlatSeed := by
  rw [FlatListParams.card_flatSeed, SymQ.side_eq, fbv_eq]
  rfl

/-! ## The program -/

section Prog
variable {ns nr : ℕ} (cap : ℕ)

def c1 : Fin 10 ↪ Fin 20 := ⟨![1, 3, 10, 11, 12, 13, 14, 15, 16, 17], by decide⟩
def c2 : Fin 10 ↪ Fin 20 := ⟨![0, 4, 10, 11, 12, 13, 14, 15, 16, 17], by decide⟩
def mx : Fin 10 ↪ Fin 20 := ⟨![3, 4, 5, 10, 11, 12, 13, 14, 15, 16], by decide⟩
def sbE : Fin 10 ↪ Fin 20 := ⟨![5, 6, 10, 11, 12, 13, 14, 15, 16, 17], by decide⟩
def eE : Fin 10 ↪ Fin 20 := ⟨![19, 6, 7, 8, 10, 11, 12, 13, 14, 15], by decide⟩
def pE : Fin 4 ↪ Fin 20 := ⟨![8, 9, 10, 11], by decide⟩
@[simp] theorem c1_apply (i : Fin 10) : c1 i = ![1, 3, 10, 11, 12, 13, 14, 15, 16, 17] i := rfl
@[simp] theorem c2_apply (i : Fin 10) : c2 i = ![0, 4, 10, 11, 12, 13, 14, 15, 16, 17] i := rfl
@[simp] theorem mx_apply (i : Fin 10) : mx i = ![3, 4, 5, 10, 11, 12, 13, 14, 15, 16] i := rfl
@[simp] theorem sbE_apply (i : Fin 10) : sbE i = ![5, 6, 10, 11, 12, 13, 14, 15, 16, 17] i := rfl
@[simp] theorem eE_apply (i : Fin 10) : eE i = ![19, 6, 7, 8, 10, 11, 12, 13, 14, 15] i := rfl
@[simp] theorem pE_apply (i : Fin 4) : pE i = ![8, 9, 10, 11] i := rfl

/-- **The list's numbers**: `J`, `⌈log₂M⌉`, the rank, the side bits, the walk length, `log₂|FlatSeed|`,
`|FlatSeed|` from `M`, `B`, `errExp`. -/
def flatNumsW (F : Fin 20 ↪ Fin nr) : WM ns nr :=
  .seq (clogW (c1.trans F)) (.seq (StarNums.incN (F 3) 9) (.seq (clogW (c2.trans F)) (.seq (maxW (mx.trans F))
  (.seq (sbW (sbE.trans F)) (.seq (FinalPass.Hash4.wcopyR (F 2) (F 7) (F 10)) (.seq (halveM (F 7) (F 10) (F 11))
  (.seq (WM.clear (F 11)) (.seq (halveM (F 7) (F 10) (F 11)) (.seq (WM.clear (F 11)) (.seq (dbl (F 7) (F 10))
  (.seq (.inc (F 7)) (.seq (eW (eE.trans F)) (.seq (sgB (eE.trans F)) (pow2W (pE.trans F)))))))))))))))

/-- The state after the program. -/
noncomputable def flatOut (F : Fin 20 ↪ Fin nr) (σ : WState ns nr) (M B e : ℕ) : WState ns nr :=
  blk F σ (flatVec M B e)

/-- **The list's numbers, run**: from `M`, `B`, `errExp` in `F 0 … F 2` and the rest of the block `0`, the program
leaves `flatOut`, within `110·sq cap`. -/
theorem flatNums_spec (F : Fin 20 ↪ Fin nr) (σ : WState ns nr) (M B e : ℕ) (h0 : σ.val (F 0) = M)
    (h1 : σ.val (F 1) = B) (h2 : σ.val (F 2) = e) (hz : ∀ i : Fin 20, 3 ≤ i.val → σ.val (F i) = 0)
    (hc : M + B + e + 2 ^ (fbv M B e + 1) + 1000 ≤ cap) :
    WExec cap (flatNumsW F) σ (flatOut F σ M B e) (110 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have hr9 := rkv_ge M B
  have hcB : Nat.clog 2 B + 9 ≤ rkv M B := le_max_left _ _
  have hcM : Nat.clog 2 M ≤ rkv M B := le_max_right _ _
  have hfb : fbv M B e = 0 + (rkv M B + rkv M B + rkv M B) / 2 + (rkv M B + rkv M B + rkv M B) / 2 +
      (2 * (e / 2 / 2) + 1 - 1) * 160 := rfl
  have hlt : fbv M B e < 2 ^ fbv M B e := Nat.lt_two_pow_self
  have hp : 2 ^ (fbv M B e + 1) = 2 * 2 ^ fbv M B e := by rw [pow_succ]; ring
  unfold flatNumsW
  refine seqD cap _ 20 (clogW_spec cap (c1.trans F) σ B (by simp [h1])
    (fun i hi => by fin_cases i <;> simp [hz] at hi ⊢) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (F 3) (Nat.clog 2 B) 9 _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 20 (clogW_spec cap (c2.trans F) _ M (by simp [h0])
    (fun i hi => by fin_cases i <;> simp [hz] at hi ⊢) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 6 (maxW_spec cap (mx.trans F) _ (Nat.clog 2 B + 9) (Nat.clog 2 M) (by simp) (by simp)
    (fun i hi => by fin_cases i <;> simp [hz] at hi ⊢) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 10 (sbW_spec cap (sbE.trans F) _ (rkv M B) (by simp [rkv])
    (fun i hi => by fin_cases i <;> simp [hz] at hi ⊢) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (copy1 cap (F 2) (F 7) (F 10) (by simp) (by simp) (by simp) e _ (by simp [h2]) (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (F 7) (F 10) (F 11) (by simp) (by simp) (by simp) e _ (by simp) (by simp [hz])
    (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (F 11) (e % 2) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (halve1 cap (F 7) (F 10) (F 11) (by simp) (by simp) (by simp) (e / 2) _ (by simp) (by simp [hz])
    (by simp) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (F 11) (e / 2 % 2) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (dbl1 cap (F 7) (F 10) (by simp) (e / 2 / 2) _ (by simp) (by simp [hz]) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (F 7) (2 * (e / 2 / 2)) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 6 (eW_spec cap (eE.trans F) _ 0 ((rkv M B + rkv M B + rkv M B) / 2) (by simp [hz]) (by simp)
    (fun i hi => by fin_cases i <;> simp [hz] at hi ⊢) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 16 (sgB_spec cap (eE.trans F) _ (0 + (rkv M B + rkv M B + rkv M B) / 2 +
      (rkv M B + rkv M B + rkv M B) / 2) (2 * (e / 2 / 2) + 1) (by simp) (by simp)
    (fun i hi => by fin_cases i <;> simp [hz] at hi ⊢) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (pow2v cap (pE.trans F) (fbv M B e) _ (by simp [hfb]) (by simp [hz]) (by simp [hz])
    (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, c1_apply, c2_apply, mx_apply, sbE_apply, eE_apply, pE_apply,
    Matrix.cons_val]
  clear hc hsq hlt hp hcB hcM hr9
  have hb0 := setv_base F σ
  unfold flatOut
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, flatVec, hz, h0, h1, h2, rkv, sbv, wlv, fbv]

/-- The state after the program as the outputs written over `σ` (for composing with other register programs). -/
theorem flatOut_eq (F : Fin 20 ↪ Fin nr) (σ : WState ns nr) (M B e : ℕ) (h0 : σ.val (F 0) = M)
    (h1 : σ.val (F 1) = B) (h2 : σ.val (F 2) = e) (hz : ∀ i : Fin 20, 3 ≤ i.val → σ.val (F i) = 0) :
    flatOut F σ M B e = (((((((σ.setv (F 3) (Nat.clog 2 B + 9)).setv (F 4) (Nat.clog 2 M)).setv (F 5) (rkv M B)).setv
      (F 6) (sbv M B)).setv (F 7) (wlv e)).setv (F 8) (fbv M B e)).setv (F 9) (2 ^ fbv M B e)) := by
  have hb0 := setv_base F σ
  unfold flatOut
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, flatVec, hz, h0, h1, h2]

end Prog

end NearCubicWires.WireExponent3_5.PrimAsm.FlatNums
