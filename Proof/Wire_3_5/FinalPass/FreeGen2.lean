import Proof.Wire_3_5.FinalPass.FreeGen
import Proof.Wire_3_5.Primitive.Writers.PopSetupNums

/-! # The free numbers' program, part 1: the pieces (squares, products, `β`, `m`, `ρ`)

Register programs in C5's word language, each on its own block `S` (sources, one output, scratch left `0`), with
their `WExec` specs in PA's unit budget (`UnaryPow.sq cap` per unit): **`sqW`** (`x·x`), **`mulW`** (`a·b`),
**`cmulW`** (`c·x` for a constant `c`), **`betaW`** (`β = ⌈log₂(n+2)⌉`, `SymQM.clogW`), **`mW`** (the factor count
`mA·nc + mB·(a·W) + mC·W + mD·a + mF·M + mE`), **`rhoW`** (the pad's exponent `max(n − kh − kh + dA·β, dR·b)`).

Paper quantities of the main types: the free numbers' parts (the ledger's `L`, the powers of `β`, the printed terms'
factor count, the pad's exponent). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.SymQM NearCubicWires.WireExponent3_5.PrimAsm.FiltNum
open NearCubicWires.WireExponent3_5.PrimAsm.CapNum NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

variable {ns nr : ℕ} (cap : ℕ)

def sqR : Fin 5 ↪ Fin 5 := ⟨![1, 0, 2, 3, 4], by decide⟩
def mR : Fin 5 ↪ Fin 6 := ⟨![2, 1, 3, 4, 5], by decide⟩
def clR : Fin 10 ↪ Fin 11 := ⟨![2, 1, 3, 4, 5, 6, 7, 8, 9, 10], by decide⟩
def mA0 : Fin 5 ↪ Fin 9 := ⟨![5, 0, 4, 7, 8], by decide⟩
def mAW : Fin 5 ↪ Fin 9 := ⟨![1, 2, 6, 7, 8], by decide⟩
def mB0 : Fin 5 ↪ Fin 9 := ⟨![5, 6, 4, 7, 8], by decide⟩
def mC0 : Fin 5 ↪ Fin 9 := ⟨![5, 2, 4, 7, 8], by decide⟩
def mD0 : Fin 5 ↪ Fin 9 := ⟨![5, 1, 4, 7, 8], by decide⟩
def mF0 : Fin 5 ↪ Fin 9 := ⟨![5, 3, 4, 7, 8], by decide⟩
def rS : Fin 4 ↪ Fin 14 := ⟨![5, 1, 8, 9], by decide⟩
def rA : Fin 5 ↪ Fin 14 := ⟨![7, 2, 5, 8, 9], by decide⟩
def rR : Fin 5 ↪ Fin 14 := ⟨![6, 3, 8, 9, 10], by decide⟩
def rM : Fin 10 ↪ Fin 14 := ⟨![5, 6, 4, 7, 8, 9, 10, 11, 12, 13], by decide⟩
@[simp] theorem sqR_apply (i : Fin 5) : sqR i = ![1, 0, 2, 3, 4] i := rfl
@[simp] theorem mR_apply (i : Fin 5) : mR i = ![2, 1, 3, 4, 5] i := rfl
@[simp] theorem clR_apply (i : Fin 10) : clR i = ![2, 1, 3, 4, 5, 6, 7, 8, 9, 10] i := rfl
@[simp] theorem mA0_apply (i : Fin 5) : mA0 i = ![5, 0, 4, 7, 8] i := rfl
@[simp] theorem mAW_apply (i : Fin 5) : mAW i = ![1, 2, 6, 7, 8] i := rfl
@[simp] theorem mB0_apply (i : Fin 5) : mB0 i = ![5, 6, 4, 7, 8] i := rfl
@[simp] theorem mC0_apply (i : Fin 5) : mC0 i = ![5, 2, 4, 7, 8] i := rfl
@[simp] theorem mD0_apply (i : Fin 5) : mD0 i = ![5, 1, 4, 7, 8] i := rfl
@[simp] theorem mF0_apply (i : Fin 5) : mF0 i = ![5, 3, 4, 7, 8] i := rfl
@[simp] theorem rS_apply (i : Fin 4) : rS i = ![5, 1, 8, 9] i := rfl
@[simp] theorem rA_apply (i : Fin 5) : rA i = ![7, 2, 5, 8, 9] i := rfl
@[simp] theorem rR_apply (i : Fin 5) : rR i = ![6, 3, 8, 9, 10] i := rfl
@[simp] theorem rM_apply (i : Fin 10) : rM i = ![5, 6, 4, 7, 8, 9, 10, 11, 12, 13] i := rfl

/-! ## Squares and products -/

/-- `S1 := S0·S0`; `S = (x, out, scratch)`. -/
def sqW (S : Fin 5 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 1) (S 2)) (mulByW (sqR.trans S))

theorem sqW_spec (S : Fin 5 ↪ Fin nr) (σ : WState ns nr) (x : ℕ) (h0 : σ.val (S 0) = x)
    (hz : ∀ i : Fin 5, 1 ≤ i.val → σ.val (S i) = 0) (hx : x ≤ cap) (hc : x * x ≤ cap) :
    WExec cap (sqW S) σ (σ.setv (S 1) (x * x)) (5 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold sqW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 1) (S 2) (by simp) (by simp) (by simp) x σ h0 (by simp [hz])
    (by simp [hz]) hx) (by omega) (by omega) ?_
  refine endD cap _ 3 (mulBy1 cap (sqR.trans S) x x _ (by simp) (by simp [h0]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc hx hx) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, sqR_apply, Matrix.cons_val]
  clear h0 hx hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- `S2 := S0·S1`; `S = (a, b, out, scratch)`. -/
def mulW (S : Fin 6 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 2) (S 3)) (mulByW (mR.trans S))

theorem mulW_spec (S : Fin 6 ↪ Fin nr) (σ : WState ns nr) (a b : ℕ) (h0 : σ.val (S 0) = a) (h1 : σ.val (S 1) = b)
    (hz : ∀ i : Fin 6, 2 ≤ i.val → σ.val (S i) = 0) (ha : a ≤ cap) (hb : b ≤ cap) (hc : a * b ≤ cap) :
    WExec cap (mulW S) σ (σ.setv (S 2) (a * b)) (5 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold mulW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 2) (S 3) (by simp) (by simp) (by simp) a σ h0 (by simp [hz])
    (by simp [hz]) ha) (by omega) (by omega) ?_
  refine endD cap _ 3 (mulBy1 cap (mR.trans S) a b _ (by simp) (by simp [h1]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc ha hb) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, mR_apply, Matrix.cons_val]
  clear h0 h1 ha hb hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-- `S1 := c·S0`; `S = (x, out, scratch)`. -/
def cmulW (c : ℕ) (S : Fin 5 ↪ Fin nr) : WM ns nr :=
  .seq (StarNums.incN (S 1) c) (mulByW (sqR.trans S))

theorem cmulW_spec (c : ℕ) (S : Fin 5 ↪ Fin nr) (σ : WState ns nr) (x : ℕ) (h0 : σ.val (S 0) = x)
    (hz : ∀ i : Fin 5, 1 ≤ i.val → σ.val (S i) = 0) (hx : x ≤ cap) (hcc : c ≤ cap) (hc : c * x ≤ cap) :
    WExec cap (cmulW c S) σ (σ.setv (S 1) (c * x)) (5 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold cmulW
  refine seqD cap _ 1 (incN0 cap (S 1) c σ (by simp [hz]) hcc) (by omega) (by omega) ?_
  refine endD cap _ 3 (mulBy1 cap (sqR.trans S) c x _ (by simp) (by simp [h0]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) hc hcc hx) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, sqR_apply, Matrix.cons_val]
  clear h0 hx hcc hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ## `β` -/

/-- `S1 := ⌈log₂(S0 + 2)⌉`; `S = (n, out, temp, scratch)`. -/
def betaW (S : Fin 11 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 2) (S 3)) (.seq (.inc (S 2)) (.seq (.inc (S 2)) (.seq (clogW (clR.trans S))
    (WM.clear (S 2)))))

theorem betaW_spec (S : Fin 11 ↪ Fin nr) (σ : WState ns nr) (n : ℕ) (h0 : σ.val (S 0) = n)
    (hz : ∀ i : Fin 11, 1 ≤ i.val → σ.val (S i) = 0) (hc : n + 4 ≤ cap) :
    WExec cap (betaW S) σ (σ.setv (S 1) (Nat.clog 2 (n + 2))) (30 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold betaW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 2) (S 3) (by simp) (by simp) (by simp) n σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (S 2) n _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (inc1 cap (S 2) (n + 1) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 20 (clogW_spec cap (clR.trans S) _ (n + 1 + 1) (by simp) (fun i hi => by
      fin_cases i
      · exact absurd hi (by decide)
      all_goals simp [Function.update_apply, hz]) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 2) (n + 1 + 1) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, clR_apply, Matrix.cons_val]
  clear h0 hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ## The factor count `m` -/

/-- `S4 := mA·S0 + mB·(S1·S2) + mC·S2 + mD·S1 + mF·S3 + mE`; `S = (nc, a, W, M, out, c, aW, scratch)`. -/
def mW (mA mB mC mD mF mE : ℕ) (S : Fin 9 ↪ Fin nr) : WM ns nr :=
  .seq (StarNums.incN (S 5) mA) (.seq (mulAddW (mA0.trans S)) (.seq (WM.clear (S 5))
  (.seq (mulAddW (mAW.trans S)) (.seq (StarNums.incN (S 5) mB) (.seq (mulAddW (mB0.trans S)) (.seq (WM.clear (S 5))
  (.seq (StarNums.incN (S 5) mC) (.seq (mulAddW (mC0.trans S)) (.seq (WM.clear (S 5))
  (.seq (StarNums.incN (S 5) mD) (.seq (mulAddW (mD0.trans S)) (.seq (WM.clear (S 5))
  (.seq (StarNums.incN (S 5) mF) (.seq (mulAddW (mF0.trans S)) (.seq (WM.clear (S 5))
  (.seq (StarNums.incN (S 4) mE) (WM.clear (S 6))))))))))))))))))

theorem mW_spec (mA mB mC mD mF mE : ℕ) (S : Fin 9 ↪ Fin nr) (σ : WState ns nr) (nc a w M : ℕ)
    (h0 : σ.val (S 0) = nc) (h1 : σ.val (S 1) = a) (h2 : σ.val (S 2) = w) (h3 : σ.val (S 3) = M)
    (hz : ∀ i : Fin 9, 4 ≤ i.val → σ.val (S i) = 0)
    (hc : mA + mB + mC + mD + mF + nc + a + w + M + a * w +
      (mA * nc + mB * (a * w) + mC * w + mD * a + mF * M + mE) ≤ cap) :
    WExec cap (mW mA mB mC mD mF mE S) σ (σ.setv (S 4) (mA * nc + mB * (a * w) + mC * w + mD * a + mF * M + mE))
      (40 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have z1 : 0 + a * w = a * w := Nat.zero_add _
  have z2 : mB * (0 + a * w) = mB * (a * w) := by rw [z1]
  unfold mW
  refine seqD cap _ 1 (incN0 cap (S 5) mA σ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mA0.trans S) mA nc 0 _ (by simp) (by simp [h0]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) mA _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mAW.trans S) a w 0 _ (by simp [h1]) (by simp [h2]) (by simp [hz])
    (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 5) mB _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mB0.trans S) mB (0 + a * w) (0 + mA * nc) _ (by simp) (by simp) (by simp)
    (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) mB _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 5) mC _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mC0.trans S) mC w (0 + mA * nc + mB * (0 + a * w)) _ (by simp) (by simp [h2])
    (by simp) (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) mC _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 5) mD _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mD0.trans S) mD a (0 + mA * nc + mB * (0 + a * w) + mC * w) _ (by simp)
    (by simp [h1]) (by simp) (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) mD _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 5) mF _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (mF0.trans S) mF M (0 + mA * nc + mB * (0 + a * w) + mC * w + mD * a) _
    (by simp) (by simp [h3]) (by simp) (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) mF _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN1 cap (S 4) (0 + mA * nc + mB * (0 + a * w) + mC * w + mD * a + mF * M) mE _ (by simp)
    (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 6) (0 + a * w) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, mA0_apply, mAW_apply, mB0_apply, mC0_apply, mD0_apply, mF0_apply,
    Matrix.cons_val, Nat.zero_add]
  clear h0 h1 h2 h3 hc hsq z1 z2
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

/-! ## The pad's exponent `ρ` -/

/-- `S4 := max(S0 − S1 − S1 + dA·S2, dR·S3)`; `S = (n, kh, β, b, out, R₁, R₂, c, scratch)`. -/
def rhoW (dA dR : ℕ) (S : Fin 14 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (S 0) (S 5) (S 8)) (.seq (subW (rS.trans S)) (.seq (subW (rS.trans S))
  (.seq (StarNums.incN (S 7) dA) (.seq (mulAddW (rA.trans S)) (.seq (WM.clear (S 7))
  (.seq (StarNums.incN (S 6) dR) (.seq (mulByW (rR.trans S)) (.seq (maxW (rM.trans S))
  (.seq (WM.clear (S 5)) (WM.clear (S 6)))))))))))

theorem rhoW_spec (dA dR : ℕ) (S : Fin 14 ↪ Fin nr) (σ : WState ns nr) (n kh b g : ℕ) (h0 : σ.val (S 0) = n)
    (h1 : σ.val (S 1) = kh) (h2 : σ.val (S 2) = b) (h3 : σ.val (S 3) = g)
    (hz : ∀ i : Fin 14, 4 ≤ i.val → σ.val (S i) = 0)
    (hc : n + kh + b + g + dA + dR + dA * b + dR * g + 1 ≤ cap) :
    WExec cap (rhoW dA dR S) σ (σ.setv (S 4) (max (n - kh - kh + dA * b) (dR * g))) (30 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  unfold rhoW
  refine seqD cap _ 1 (copy1 cap (S 0) (S 5) (S 8) (by simp) (by simp) (by simp) n σ h0 (by simp [hz])
    (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (PopSetupNums.sub1 cap (rS.trans S) n kh _ (by simp) (by simp [h1]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (PopSetupNums.sub1 cap (rS.trans S) (n - kh) kh _ (by simp) (by simp [h1]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 7) dA _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (mulAdd1 cap (rA.trans S) dA b (n - kh - kh) _ (by simp) (by simp [h2]) (by simp)
    (by simp [hz]) (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 7) dA _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 1 (incN0 cap (S 6) dR _ (by simp [hz]) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 3 (mulBy1 cap (rR.trans S) dR g _ (by simp) (by simp [h3]) (by simp [hz]) (by simp [hz])
    (by simp [hz]) (by omega) (by omega) (by omega)) (by omega) (by omega) ?_
  refine seqD cap _ 6 (maxW_spec cap (rM.trans S) _ (n - kh - kh + dA * b) (dR * g) (by simp) (by simp)
    (fun i hi => by fin_cases i <;> simp_all [Function.update_apply]) (by omega) (by omega) (by omega))
    (by omega) (by omega) ?_
  refine seqD cap _ 1 (clear1 cap (S 5) (n - kh - kh + dA * b) _ (by simp) (by omega)) (by omega) (by omega) ?_
  refine endD cap _ 1 (clear1 cap (S 6) (dR * g) _ (by simp) (by omega)) ?_ (by omega) (by omega)
  simp only [Function.Embedding.trans_apply, rS_apply, rA_apply, rR_apply, rM_apply, Matrix.cons_val]
  clear h0 h1 h2 h3 hc hsq
  have hb0 := setv_base S σ
  simp only [hb0, setv_blk]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply, hz]

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

