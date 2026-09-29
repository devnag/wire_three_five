import Proof.Wire_3_5.UnionMachine.FrontTWBlock
import Proof.Wire_3_5.Primitive.Writers.UnaryArith

/-! # C6 front, U5: one position's and one clause's calls (P3:3685-3691, 3483-3484)

At a position `(i, b)` the variable is `X = ⌊ℓ/2⌋` of the literal index `ℓ = literalIndex` (`2X`, or `2X + 1` when
negated; base `literalIndex`), and its grid entries start at `X·s`. The validity test's monomials at a systematic
variable are `[S S 1 1], [E S 1 1], [E 1 1 1]` with `κ = 1, −2, 1`, otherwise `[S S 1 1], [S S S 1], [S S S S]`; the
second-moment test's is `[S S 1 1]`; the clause test's, at clause `i` with literals `ℓ₀, ℓ₁`, are `[1 1 1 1]`,
`[S_X 1 1 1]`, `[S_Y 1 1 1]`, `[S_X S_Y 1 1]` with `κ` from the literals' signs (`FrontTableRef.patV/patQ/patMu`).
Each block's magnitude `|κ|·∏ m_k` is one of six products of `s` and `Λ̄`, precomputed in registers.

**`varSetT`**: `ℓ ↦ X, N, X·s` (PA's `halveM`, `mulAddW`). Paper quantity: the calls of one position/clause. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef (FK lexProd patV patQ patMu)

variable (cap : ℕ) (src : Fin 11 → List Bool)

/-! ## More registers -/

abbrev rLIT : Fin NR := 40
abbrev rMa : Fin NR := 41
abbrev rMb : Fin NR := 42
abbrev rMc : Fin NR := 43
abbrev rMd : Fin NR := 44
abbrev rMe : Fin NR := 45
abbrev rMf : Fin NR := 46
abbrev rS1 : Fin NR := 47
abbrev rS2 : Fin NR := 48
abbrev rS3 : Fin NR := 49

/-! ## A variable from a literal -/

/-- The multiply-add registers `(X, s, XS, t, w)` for the first literal's variable. -/
def mX : Fin 5 ↪ Fin NR := ⟨![rX, rSS, rXS, rS1, rS2], by decide⟩
/-- The same for the second literal's variable. -/
def mY : Fin 5 ↪ Fin NR := ⟨![rY, rSS, rYS, rS1, rS2], by decide⟩

/-- The zero digits. -/
abbrev Z4 : Fin 4 → ℕ := fun _ => 0

theorem tsR_setv (h : ℕ) (o : List Bool) (cl : Bool) (w : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (r : Fin NR)
    (hr : Plain r) (hro : r ≠ rOP) (x : ℕ) :
    (ts src h o (regsOf w E NB A ok) cl).setv r x = ts src h o (regsOf (Function.update w r x) E NB A ok) cl := by
  rw [ts_setv _ _ _ _ _ _ hro, regsOf_updPlain _ _ _ _ _ _ hr]

theorem tsR_val (h : ℕ) (o : List Bool) (cl : Bool) (w : Fin NR → ℕ) (E NB A : Fin 4 → ℕ) (ok : ℕ) (r : Fin NR)
    (hr : Plain r) (hro : r ≠ rOP) : (ts src h o (regsOf w E NB A ok) cl).val r = w r := by
  rw [ts_val _ _ _ _ _ _ hro, regsOf_plain _ _ _ _ _ _ hr]

/-- `X := ⌊ℓ/2⌋`, `N := ℓ mod 2`, `XS := X·s` from `ℓ` in `LIT` (the multiply-add registers `m`). -/
def varSet (N : Fin NR) (m : Fin 5 ↪ Fin NR) : WM 10 NR :=
  .seq (halveM rLIT rS1 N) (.seq (WM.move rLIT (m 0)) (mulAddW m))

/-- **A variable from a literal**, as a state of plain registers. -/
theorem varSetT (h : ℕ) (o : List Bool) (cl : Bool) (v0 : Fin NR → ℕ) (ok : ℕ) (N : Fin NR) (m : Fin 5 ↪ Fin NR)
    (hN : Plain N) (hNo : N ≠ rOP) (hm : ∀ i, Plain (m i)) (hmo : ∀ i, m i ≠ rOP) (hm3 : m 3 = rS1)
    (hNL : N ≠ rLIT) (hNS : N ≠ rS1) (hmN : ∀ i, m i ≠ N) (hmL : ∀ i, m i ≠ rLIT)
    (h0 : v0 (m 0) = 0) (h2 : v0 (m 2) = 0) (hNz : v0 N = 0) (hs1 : v0 rS1 = 0) (hs2 : v0 (m 4) = 0)
    (hcap : v0 rLIT + v0 rLIT * v0 (m 1) + v0 (m 1) + 1 ≤ cap) :
    WExec cap (varSet N m) (ts src h o (regsOf v0 Z4 Z4 Z4 ok) cl)
      (ts src h o (regsOf (Function.update (Function.update (Function.update (Function.update (Function.update v0
        rLIT (v0 rLIT / 2)) N (v0 rLIT % 2)) rLIT 0) (m 0) (0 + v0 rLIT / 2)) (m 2)
          (0 + (v0 rLIT / 2) * v0 (m 1))) Z4 Z4 Z4 ok) cl)
      (9 * v0 rLIT + 6 + 1 + (7 * (v0 rLIT / 2) + 1) + 1 +
        (v0 (m 1) * (18 * (v0 rLIT / 2) + 8) + 18 * v0 (m 1) + 10)) := by
  have pL : Plain rLIT := ⟨by decide, by decide⟩
  have pS1 : Plain rS1 := ⟨by decide, by decide⟩
  have hLo : rLIT ≠ rOP := by decide
  have hSo : rS1 ≠ rOP := by decide
  have hne : ∀ {i j : Fin 5}, i ≠ j → m i ≠ m j := fun hij => m.injective.ne hij
  set ℓ := v0 rLIT with hℓ
  have s1 := halveM_spec cap rLIT rS1 N (by decide) (Ne.symm hNL) (Ne.symm hNS) (ts src h o (regsOf v0 Z4 Z4 Z4 ok) cl)
    (by rw [tsR_val src h o cl v0 _ _ _ ok rS1 pS1 hSo]; exact hs1)
    (by rw [tsR_val src h o cl v0 _ _ _ ok N hN hNo]; exact hNz)
    (by rw [tsR_val src h o cl v0 _ _ _ ok rLIT pL hLo]; omega) (by omega)
  rw [tsR_val src h o cl v0 _ _ _ ok rLIT pL hLo, tsR_setv src h o cl v0 _ _ _ ok rLIT pL hLo,
    tsR_setv src h o cl _ _ _ _ ok N hN hNo] at s1
  set v1 := Function.update (Function.update v0 rLIT (ℓ / 2)) N (ℓ % 2) with hv1
  have v1L : v1 rLIT = ℓ / 2 := by simp [v1, Function.update_of_ne hNL.symm]
  have v1m : ∀ i, v1 (m i) = v0 (m i) := fun i => by
    simp only [v1]; rw [Function.update_of_ne (hmN i), Function.update_of_ne (hmL i)]
  have s2 := wmove_spec cap rLIT (m 0) (Ne.symm (hmL 0)) (ℓ / 2) (ts src h o (regsOf v1 Z4 Z4 Z4 ok) cl)
    (by rw [tsR_val src h o cl v1 _ _ _ ok rLIT pL hLo]; exact v1L)
    (by rw [tsR_val src h o cl v1 _ _ _ ok rLIT pL hLo, v1L]; omega)
    (by rw [tsR_val src h o cl v1 _ _ _ ok rLIT pL hLo, tsR_val src h o cl v1 _ _ _ ok _ (hm 0) (hmo 0), v1L, v1m, h0]
        omega)
  rw [tsR_val src h o cl v1 _ _ _ ok rLIT pL hLo, tsR_val src h o cl v1 _ _ _ ok _ (hm 0) (hmo 0), v1L, v1m, h0,
    tsR_setv src h o cl v1 _ _ _ ok rLIT pL hLo, tsR_setv src h o cl _ _ _ _ ok _ (hm 0) (hmo 0)] at s2
  set v2 := Function.update (Function.update v1 rLIT 0) (m 0) (0 + ℓ / 2) with hv2
  have v2m : ∀ i, i ≠ 0 → v2 (m i) = v0 (m i) := fun i hi => by
    simp only [v2]; rw [Function.update_of_ne (hne hi), Function.update_of_ne (hmL i), v1m]
  have v20 : v2 (m 0) = ℓ / 2 := by simp [v2]
  have s3 := mulAddW_spec cap m (ts src h o (regsOf v2 Z4 Z4 Z4 ok) cl)
    (by rw [tsR_val src h o cl v2 _ _ _ ok _ (hm 3) (hmo 3), v2m 3 (by decide), hm3]; exact hs1)
    (by rw [tsR_val src h o cl v2 _ _ _ ok _ (hm 4) (hmo 4), v2m 4 (by decide)]; exact hs2)
    (by rw [tsR_val src h o cl v2 _ _ _ ok _ (hm 1) (hmo 1), v2m 1 (by decide)]; omega)
    (by rw [tsR_val src h o cl v2 _ _ _ ok _ (hm 2) (hmo 2), tsR_val src h o cl v2 _ _ _ ok _ (hm 0) (hmo 0),
        tsR_val src h o cl v2 _ _ _ ok _ (hm 1) (hmo 1), v2m 2 (by decide), v2m 1 (by decide), v20, h2]
        have : ℓ / 2 * v0 (m 1) ≤ ℓ * v0 (m 1) := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
        omega)
    (by rw [tsR_val src h o cl v2 _ _ _ ok _ (hm 0) (hmo 0), v20]; omega)
  rw [tsR_val src h o cl v2 _ _ _ ok _ (hm 2) (hmo 2), tsR_val src h o cl v2 _ _ _ ok _ (hm 0) (hmo 0),
    tsR_val src h o cl v2 _ _ _ ok _ (hm 1) (hmo 1), v2m 2 (by decide), v2m 1 (by decide), v20, h2,
    tsR_setv src h o cl v2 _ _ _ ok _ (hm 2) (hmo 2)] at s3
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega)

/-- The registers after `varSet`: `LIT := 0`, `N := ℓ mod 2`, `m 0 := ⌊ℓ/2⌋`, `m 2 := ⌊ℓ/2⌋·(m 1)`. -/
def varSetVec (v0 : Fin NR → ℕ) (N : Fin NR) (m : Fin 5 ↪ Fin NR) : Fin NR → ℕ :=
  Function.update (Function.update (Function.update (Function.update v0 rLIT 0) N (v0 rLIT % 2)) (m 0) (v0 rLIT / 2))
    (m 2) (v0 rLIT / 2 * v0 (m 1))

theorem varSetT' (h : ℕ) (o : List Bool) (cl : Bool) (v0 : Fin NR → ℕ) (ok : ℕ) (N : Fin NR) (m : Fin 5 ↪ Fin NR)
    (hN : Plain N) (hNo : N ≠ rOP) (hm : ∀ i, Plain (m i)) (hmo : ∀ i, m i ≠ rOP) (hm3 : m 3 = rS1)
    (hNL : N ≠ rLIT) (hNS : N ≠ rS1) (hmN : ∀ i, m i ≠ N) (hmL : ∀ i, m i ≠ rLIT)
    (h0 : v0 (m 0) = 0) (h2 : v0 (m 2) = 0) (hNz : v0 N = 0) (hs1 : v0 rS1 = 0) (hs2 : v0 (m 4) = 0)
    (hcap : v0 rLIT + v0 rLIT * v0 (m 1) + v0 (m 1) + 1 ≤ cap) :
    WExec cap (varSet N m) (ts src h o (regsOf v0 Z4 Z4 Z4 ok) cl) (ts src h o (regsOf (varSetVec v0 N m) Z4 Z4 Z4 ok) cl)
      (9 * v0 rLIT + 6 + 1 + (7 * (v0 rLIT / 2) + 1) + 1 +
        (v0 (m 1) * (18 * (v0 rLIT / 2) + 8) + 18 * v0 (m 1) + 10)) := by
  have e := varSetT cap src h o cl v0 ok N m hN hNo hm hmo hm3 hNL hNS hmN hmL h0 h2 hNz hs1 hs2 hcap
  have hne : ∀ {i j : Fin 5}, i ≠ j → m i ≠ m j := fun hij => m.injective.ne hij
  have ev : Function.update (Function.update (Function.update (Function.update (Function.update v0 rLIT (v0 rLIT / 2))
      N (v0 rLIT % 2)) rLIT 0) (m 0) (0 + v0 rLIT / 2)) (m 2) (0 + (v0 rLIT / 2) * v0 (m 1)) = varSetVec v0 N m := by
    funext r
    simp only [varSetVec, Function.update_apply]
    by_cases a1 : r = m 2
    · simp [a1]
    by_cases a2 : r = m 0
    · simp [a2, hne (show (0 : Fin 5) ≠ 2 by decide)]
    by_cases a3 : r = rLIT
    · subst a3; simp [(hmL 2).symm, (hmL 0).symm, hNL.symm]
    by_cases a4 : r = N
    · subst a4; simp [(hmN 2).symm, (hmN 0).symm, hNL]
    simp [a1, a2, a3, a4]
  rw [ev] at e
  exact e

theorem varSetVec_other (v : Fin NR → ℕ) (N : Fin NR) (m : Fin 5 ↪ Fin NR) (r : Fin NR) (h1 : r ≠ rLIT) (h2 : r ≠ N)
    (h3 : r ≠ m 0) (h4 : r ≠ m 2) : varSetVec v N m r = v r := by
  simp only [varSetVec]
  rw [Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]

theorem varSetVec_m2 (v : Fin NR → ℕ) (N : Fin NR) (m : Fin 5 ↪ Fin NR) :
    varSetVec v N m (m 2) = v rLIT / 2 * v (m 1) := by simp [varSetVec]

theorem varSetVec_m0 (v : Fin NR → ℕ) (N : Fin NR) (m : Fin 5 ↪ Fin NR) : varSetVec v N m (m 0) = v rLIT / 2 := by
  simp only [varSetVec]
  rw [Function.update_of_ne (m.injective.ne (by decide)), Function.update_self]

theorem varSetVec_N (v : Fin NR → ℕ) (N : Fin NR) (m : Fin 5 ↪ Fin NR) (h0 : N ≠ m 0) (h2 : N ≠ m 2) :
    varSetVec v N m N = v rLIT % 2 := by
  simp only [varSetVec]
  rw [Function.update_of_ne h2, Function.update_of_ne h0, Function.update_self]

theorem varSetVec_LIT (v : Fin NR → ℕ) (N : Fin NR) (m : Fin 5 ↪ Fin NR) (h1 : rLIT ≠ N) (h0 : rLIT ≠ m 0)
    (h2 : rLIT ≠ m 2) : varSetVec v N m rLIT = 0 := by
  simp only [varSetVec]
  rw [Function.update_of_ne h2, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_self]

/-! ## One block with its magnitude -/

/-- `MAG := Mx`, one block, `MAG := 0`. -/
def magBlock (Mx : Fin NR) (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool) : WM 10 NR :=
  .seq (cloop Mx rT (.inc rMAG)) (.seq (blockP kd κn pat two) (WM.clear rMAG))

theorem plain_MAG : Plain rMAG := ⟨by decide, by decide⟩

/-- The block's registers: `v0` with the magnitude loaded. -/
def withMag (v0 : Fin NR → ℕ) (Mx : Fin NR) : Fin NR → ℕ := Function.update v0 rMAG (v0 Mx)

theorem magBlockT (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ)
    (hs : Scr v0) (hBIG : v0 rBIG = B) (hNZ : v0 rNZ = 0) (hMAG : v0 rMAG = 0) (Mx : Fin NR) (hMx : Plain Mx)
    (hMxo : Mx ≠ rOP) (hMxT : Mx ≠ rT) (hMxM : Mx ≠ rMAG) (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool)
    (hX : v0 rXS + v0 rSS ≤ d.es.length) (hY : v0 rYS + v0 rSS ≤ d.es.length) (hdf : d.es.length ≤ d.df.length)
    (hpar : v0 rX < d.pcs.length ∧ v0 rX < d.pf.length) (hXc : v0 rX < d.crs.length ∧ v0 rX < d.ef.length)
    (hYc : two = true → v0 rY < d.crs.length ∧ v0 rY < d.ef.length) (hcapB : B + 1 ≤ cap)
    (hcX : v0 rXS + v0 rSS + 1 ≤ cap) (hcY : v0 rYS + v0 rSS + 1 ≤ cap) (hM : v0 Mx + 1 ≤ cap)
    (o : List Bool) (ok : ℕ) (hok : ok ≤ 1)
    (hlen : o.length + (blockW d (withMag v0 Mx) kd κn pat two).length + 30 * B + 40 ≤ cap) :
    WExec cap (magBlock Mx kd κn pat two) (ts src h o (regsOf v0 Z4 Z4 Z4 ok) cl)
      (ts src h (o ++ blockW d (withMag v0 Mx) kd κn pat two)
        (regsOf v0 Z4 Z4 Z4 (if blockOk d (withMag v0 Mx) pat two then ok else 0)) cl)
      (18 * v0 Mx + 3 + 1 + (blockCost B (v0 Mx) (v0 rSS) (v0 rXS) (v0 rYS) pat + 1 + (3 * v0 Mx + 1))) := by
  have hMo : rMAG ≠ rOP := by decide
  set v1 := withMag v0 Mx with hv1
  have s1 := cloopIncT cap src h o cl Mx rMAG hMxo hMxT hMo (Ne.symm hMxM) (by decide)
    (fun j => regsOf (Function.update v0 rMAG j) Z4 Z4 Z4 ok)
    (fun j => by beta_reduce; rw [regsOf_updPlain _ _ _ _ _ _ plain_MAG, Function.update_idem])
    (fun j => by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ plain_MAG, Function.update_self])
    (fun j => by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ hMx, regsOf_plain _ _ _ _ _ _ hMx,
      Function.update_of_ne hMxM, Function.update_of_ne hMxM])
    (fun j => by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ ⟨by decide, by decide⟩, Function.update_of_ne (by decide)]
                 exact hs.t)
    (by beta_reduce; rw [regsOf_plain _ _ _ _ _ _ hMx, Function.update_of_ne hMxM]; exact hM)
  beta_reduce at s1
  rw [regsOf_plain _ _ _ _ _ _ hMx, Function.update_of_ne hMxM,
    show Function.update v0 rMAG 0 = v0 from Function.update_eq_self_iff.2 hMAG.symm,
    show Function.update v0 rMAG (v0 Mx) = v1 from rfl] at s1
  have hne : ∀ r, r ≠ rMAG → v1 r = v0 r := fun r hr => Function.update_of_ne hr _ _
  have hs1 : Scr v1 := ⟨by rw [hne _ (by decide)]; exact hs.t, by rw [hne _ (by decide)]; exact hs.f,
    by rw [hne _ (by decide)]; exact hs.c, by rw [hne _ (by decide)]; exact hs.z, by rw [hne _ (by decide)]; exact hs.fl,
    by rw [hne _ (by decide)]; exact hs.neg⟩
  have s2 := blockT cap src d hd B hB h cl v1 hs1 (by rw [hne _ (by decide)]; exact hBIG)
    (by rw [hne _ (by decide)]; exact hNZ) kd κn pat two
    (by rw [hne _ (by decide), hne _ (by decide)]; exact hX) (by rw [hne _ (by decide), hne _ (by decide)]; exact hY) hdf
    (by rw [hne _ (by decide)]; exact hpar) (by rw [hne _ (by decide)]; exact hXc)
    (by rw [hne _ (by decide)]; exact hYc) hcapB (by rw [hne _ (by decide), hne _ (by decide)]; exact hcX)
    (by rw [hne _ (by decide), hne _ (by decide)]; exact hcY) (by simp [v1, withMag]; omega) o ok hok hlen
  have hv1M : v1 rMAG = v0 Mx := by simp [v1, withMag]
  rw [hne rSS (by decide), hne rXS (by decide), hne rYS (by decide), hv1M] at s2
  set ok' := if blockOk d v1 pat two then ok else 0 with hok'
  have s3 := wclear_spec cap rMAG (v0 Mx) (ts src h (o ++ blockW d v1 kd κn pat two) (regsOf v1 Z4 Z4 Z4 ok') cl)
    (by rw [tsR_val src _ _ _ v1 _ _ _ _ rMAG plain_MAG hMo, hv1M]) (by rw [tsR_val src _ _ _ v1 _ _ _ _ rMAG plain_MAG hMo, hv1M]; omega)
  rw [tsR_setv src _ _ _ v1 _ _ _ _ rMAG plain_MAG hMo] at s3
  have e : Function.update v1 rMAG 0 = v0 := by
    simp only [v1, withMag, Function.update_idem]; exact Function.update_eq_self_iff.2 hMAG.symm
  rw [e] at s3
  exact WExec.seq s1 (WExec.seq s2 s3)

/-! ## Programs over fixed plain registers -/

/-- **A block-level contract**: over the plain registers `v0` (digits clear), from any `OK ≤ 1` and any output with
room `L`, the program appends `W` and conjoins `b`. -/
def PSpec (P : WM 10 NR) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ) (L : ℕ) (W : List Bool) (b : Bool) (c : ℕ) : Prop :=
  ∀ (o : List Bool) (ok : ℕ), ok ≤ 1 → o.length + W.length + L ≤ cap →
    WExec cap P (ts src h o (regsOf v0 Z4 Z4 Z4 ok) cl) (ts src h (o ++ W) (regsOf v0 Z4 Z4 Z4 (if b then ok else 0)) cl) c

theorem seqP (P Q : WM 10 NR) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ) (L : ℕ) (W1 W2 : List Bool) (b1 b2 : Bool)
    (c1 c2 : ℕ) (h1 : PSpec cap src P h cl v0 L W1 b1 c1) (h2 : PSpec cap src Q h cl v0 L W2 b2 c2) :
    PSpec cap src (.seq P Q) h cl v0 L (W1 ++ W2) (b1 && b2) (c1 + 1 + c2) := by
  intro o ok hok hlen
  simp only [List.length_append] at hlen
  have s1 := h1 o ok hok (by omega)
  have s2 := h2 (o ++ W1) (if b1 then ok else 0) (by split_ifs <;> omega) (by simp only [List.length_append]; omega)
  have e : (if b2 then (if b1 then ok else 0) else 0) = (if (b1 && b2) then ok else 0) := by
    cases b1 <;> cases b2 <;> simp
  rw [e, List.append_assoc] at s2
  exact WExec.seq s1 s2

theorem skipP (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ) (L : ℕ) : PSpec cap src .skip h cl v0 L [] true 0 := by
  intro o ok _ _
  simp only [List.append_nil, if_true]
  exact WExec.skip _

theorem ifrP (R : Fin NR) (hR : Plain R) (hRo : R ≠ rOP) (P Q : WM 10 NR) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ)
    (L : ℕ) (W1 W2 : List Bool) (b1 b2 : Bool) (c : ℕ) (h1 : PSpec cap src P h cl v0 L W1 b1 c)
    (h2 : PSpec cap src Q h cl v0 L W2 b2 c) :
    PSpec cap src (.ifr R P Q) h cl v0 L (if v0 R ≠ 0 then W1 else W2) (if v0 R ≠ 0 then b1 else b2) (c + 1) := by
  intro o ok hok hlen
  have hv : (ts src h o (regsOf v0 Z4 Z4 Z4 ok) cl).val R = v0 R := tsR_val src h o cl v0 _ _ _ ok R hR hRo
  by_cases h0 : v0 R = 0
  · simp only [h0, ne_eq, not_true_eq_false, if_false] at hlen ⊢
    exact WExec.ifrF (by rw [hv]; exact h0) (h2 o ok hok hlen)
  · simp only [h0, ne_eq, not_false_eq_true, if_true] at hlen ⊢
    exact WExec.ifrT (by rw [hv]; exact h0) (h1 o ok hok hlen)

theorem monoP (P : WM 10 NR) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ) (L : ℕ) (W : List Bool) (b : Bool) (c c' : ℕ)
    (h1 : PSpec cap src P h cl v0 L W b c) (hc : c ≤ c') : PSpec cap src P h cl v0 L W b c' :=
  fun o ok hok hlen => WExec.mono (h1 o ok hok hlen) hc

/-- The block-level invariants of the plain registers. -/
structure GInv (d : TWData) (B : ℕ) (v0 : Fin NR → ℕ) : Prop where
  scr : Scr v0
  big : v0 rBIG = B
  nz : v0 rNZ = 0
  mag : v0 rMAG = 0
  s1 : v0 rS1 = 0
  s2 : v0 rS2 = 0
  s3 : v0 rS3 = 0
  df : d.es.length ≤ d.df.length
  capB : B + 1 ≤ cap
  capM : ∀ M : Fin NR, M = rMa ∨ M = rMb ∨ M = rMc ∨ M = rMd ∨ M = rMe ∨ M = rMf → v0 M + 1 ≤ cap

/-- A block over the plain registers, as a contract. -/
theorem magBlockP (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ)
    (hg : GInv cap d B v0) (Mx : Fin NR) (hMx : Mx = rMa ∨ Mx = rMb ∨ Mx = rMc ∨ Mx = rMd ∨ Mx = rMe ∨ Mx = rMf)
    (kd : Fin 3) (κn : Bool) (pat : Fin 4 → FK) (two : Bool)
    (hX : v0 rXS + v0 rSS ≤ d.es.length) (hY : v0 rYS + v0 rSS ≤ d.es.length)
    (hpar : v0 rX < d.pcs.length ∧ v0 rX < d.pf.length) (hXc : v0 rX < d.crs.length ∧ v0 rX < d.ef.length)
    (hYc : two = true → v0 rY < d.crs.length ∧ v0 rY < d.ef.length)
    (hcX : v0 rXS + v0 rSS + 1 ≤ cap) (hcY : v0 rYS + v0 rSS + 1 ≤ cap) :
    PSpec cap src (magBlock Mx kd κn pat two) h cl v0 (30 * B + 40) (blockW d (withMag v0 Mx) kd κn pat two)
      (blockOk d (withMag v0 Mx) pat two)
      (18 * v0 Mx + 3 + 1 + (blockCost B (v0 Mx) (v0 rSS) (v0 rXS) (v0 rYS) pat + 1 + (3 * v0 Mx + 1))) := by
  have hP : Plain Mx := by rcases hMx with e | e | e | e | e | e <;> subst e <;> exact ⟨by decide, by decide⟩
  have ho : Mx ≠ rOP := by rcases hMx with e | e | e | e | e | e <;> subst e <;> decide
  have hT : Mx ≠ rT := by rcases hMx with e | e | e | e | e | e <;> subst e <;> decide
  have hM : Mx ≠ rMAG := by rcases hMx with e | e | e | e | e | e <;> subst e <;> decide
  intro o ok hok hlen
  exact magBlockT cap src d hd B hB h cl v0 hg.scr hg.big hg.nz hg.mag Mx hP ho hT hM kd κn pat two hX hY hg.df hpar
    hXc hYc hg.capB hcX hcY (hg.capM Mx hMx) o ok hok hlen

/-! ## One position of the validity and second-moment tests -/

/-- The comparison registers `(SYS, X, SYSX, t, u, w)`: `SYSX := [X < SYS]` (systematic). -/
def gX : Fin 6 ↪ Fin NR := ⟨![rSYS, rX, rSYSX, rS1, rS2, rS3], by decide⟩

/-- The validity test's blocks at a position (systematic, or not). -/
def vBlocks : WM 10 NR :=
  .ifr rSYSX
    (.seq (magBlock rMb 0 false (patV true 0) false) (.seq (magBlock rMc 0 true (patV true 1) false)
      (magBlock rMa 0 false (patV true 2) false)))
    (.seq (magBlock rMb 0 false (patV false 0) false) (.seq (magBlock rMd 0 true (patV false 1) false)
      (magBlock rMe 0 false (patV false 2) false)))

/-- The second-moment test's block at a position. -/
def qBlocks : WM 10 NR := magBlock rMb 1 false (patQ 0) false

/-- Clear the position's registers. -/
def posClr : WM 10 NR := .seq (WM.clear rX) (.seq (WM.clear rN0) (.seq (WM.clear rXS) (WM.clear rSYSX)))

/-- One position: the variable from the literal, the blocks, the cleanup. -/
def posP (blocks : WM 10 NR) : WM 10 NR := .seq (varSet rN0 mX) (.seq (gtFlagW gX) (.seq blocks posClr))

/-- The registers at a position of literal `ℓ` (in `LIT`): `X = ⌊ℓ/2⌋`, `N₀ = ℓ mod 2`, `XS = X·s`,
`SYSX = [X < SYS]`, `LIT = 0`. -/
def posRegs (v0 : Fin NR → ℕ) : Fin NR → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update v0
    rLIT (v0 rLIT / 2)) rN0 (v0 rLIT % 2)) rLIT 0) rX (0 + v0 rLIT / 2)) rXS (0 + (v0 rLIT / 2) * v0 rSS)) rSYSX
      (if v0 rLIT / 2 < v0 rSYS then 1 else 0)

theorem posRegs_other (v0 : Fin NR → ℕ) (r : Fin NR) (h1 : r ≠ rLIT) (h2 : r ≠ rN0) (h3 : r ≠ rX) (h4 : r ≠ rXS)
    (h5 : r ≠ rSYSX) : posRegs v0 r = v0 r := by
  simp only [posRegs, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5]

theorem posRegs_X (v0 : Fin NR → ℕ) : posRegs v0 rX = v0 rLIT / 2 := by simp +decide [posRegs, Function.update_apply]
theorem posRegs_XS (v0 : Fin NR → ℕ) : posRegs v0 rXS = v0 rLIT / 2 * v0 rSS := by
  simp +decide [posRegs, Function.update_apply]
theorem posRegs_SYSX (v0 : Fin NR → ℕ) : posRegs v0 rSYSX = if v0 rLIT / 2 < v0 rSYS then 1 else 0 := by
  simp +decide [posRegs, Function.update_apply]

theorem ginv_pos (d : TWData) (B : ℕ) (v0 : Fin NR → ℕ) (hg : GInv cap d B v0) : GInv cap d B (posRegs v0) := by
  have e : ∀ r : Fin NR, r ≠ rLIT → r ≠ rN0 → r ≠ rX → r ≠ rXS → r ≠ rSYSX → posRegs v0 r = v0 r :=
    fun r h1 h2 h3 h4 h5 => posRegs_other v0 r h1 h2 h3 h4 h5
  have e' : ∀ r : Fin NR, (r = rT ∨ r = rF ∨ r = rC ∨ r = rZ ∨ r = rFL ∨ r = rNEG ∨ r = rBIG ∨ r = rNZ ∨ r = rMAG ∨
      r = rS1 ∨ r = rS2 ∨ r = rS3 ∨ r = rMa ∨ r = rMb ∨ r = rMc ∨ r = rMd ∨ r = rMe ∨ r = rMf) → posRegs v0 r = v0 r := by
    intro r hr
    apply e <;> rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hg.df, hg.capB, ?_⟩
  · rw [e' _ (by simp)]; exact hg.scr.t
  · rw [e' _ (by simp)]; exact hg.scr.f
  · rw [e' _ (by simp)]; exact hg.scr.c
  · rw [e' _ (by simp)]; exact hg.scr.z
  · rw [e' _ (by simp)]; exact hg.scr.fl
  · rw [e' _ (by simp)]; exact hg.scr.neg
  · rw [e' _ (by simp)]; exact hg.big
  · rw [e' _ (by simp)]; exact hg.nz
  · rw [e' _ (by simp)]; exact hg.mag
  · rw [e' _ (by simp)]; exact hg.s1
  · rw [e' _ (by simp)]; exact hg.s2
  · rw [e' _ (by simp)]; exact hg.s3
  · intro M hM
    rw [e' _ (by rcases hM with h | h | h | h | h | h <;> simp [h])]
    exact hg.capM M hM

theorem posClr_eq (v0 : Fin NR → ℕ) (h1 : v0 rX = 0) (h2 : v0 rN0 = 0) (h3 : v0 rXS = 0) (h4 : v0 rSYSX = 0) :
    Function.update (Function.update (Function.update (Function.update (posRegs v0) rX 0) rN0 0) rXS 0) rSYSX 0 =
      Function.update v0 rLIT 0 := by
  funext r
  by_cases a1 : r = rSYSX
  · subst a1; simp +decide [h4, Function.update_apply]
  by_cases a2 : r = rXS
  · subst a2; simp +decide [h3, Function.update_apply]
  by_cases a3 : r = rN0
  · subst a3; simp +decide [h2, Function.update_apply]
  by_cases a4 : r = rX
  · subst a4; simp +decide [h1, Function.update_apply]
  by_cases a5 : r = rLIT
  · subst a5; simp +decide [posRegs, Function.update_apply]
  rw [Function.update_of_ne a1, Function.update_of_ne a2, Function.update_of_ne a3, Function.update_of_ne a4,
    Function.update_of_ne a5, posRegs_other v0 r a5 a3 a4 a2 a1]

/-- **One position**: the variable, the blocks at its registers, the cleanup (`LIT` consumed). -/
theorem posT (h : ℕ) (cl : Bool) (v0 : Fin NR → ℕ) (blocks : WM 10 NR) (L : ℕ) (W : List Bool) (b : Bool) (c : ℕ)
    (hb : PSpec cap src blocks h cl (posRegs v0) L W b c) (hX0 : v0 rX = 0) (hN0 : v0 rN0 = 0) (hXS0 : v0 rXS = 0)
    (hSY0 : v0 rSYSX = 0) (hs1 : v0 rS1 = 0) (hs2 : v0 rS2 = 0) (hs3 : v0 rS3 = 0)
    (hcap : v0 rLIT + v0 rLIT * v0 rSS + v0 rSS + v0 rSYS + 1 ≤ cap)
    (o : List Bool) (ok : ℕ) (hok : ok ≤ 1) (hlen : o.length + W.length + L ≤ cap) :
    WExec cap (posP blocks) (ts src h o (regsOf v0 Z4 Z4 Z4 ok) cl)
      (ts src h (o ++ W) (regsOf (Function.update v0 rLIT 0) Z4 Z4 Z4 (if b then ok else 0)) cl)
      (110 * (v0 rLIT * v0 rSS) + 110 * v0 rLIT + 110 * v0 rSS + 30 * v0 rSYS + c + 120) := by
  have hmX : ∀ i, Plain (mX i) := by intro i; fin_cases i <;> exact ⟨by decide, by decide⟩
  have hmXo : ∀ i, mX i ≠ rOP := by intro i; fin_cases i <;> decide
  have s1 := varSetT cap src h o cl v0 ok rN0 mX ⟨by decide, by decide⟩ (by decide) hmX hmXo rfl (by decide) (by decide)
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide) hX0 hXS0 hN0 hs1 hs2 (by
      show v0 rLIT + v0 rLIT * v0 rSS + v0 rSS + 1 ≤ cap; omega)
  set v1 := Function.update (Function.update (Function.update (Function.update (Function.update v0 rLIT (v0 rLIT / 2))
    rN0 (v0 rLIT % 2)) rLIT 0) (mX 0) (0 + v0 rLIT / 2)) (mX 2) (0 + v0 rLIT / 2 * v0 (mX 1)) with hv1
  have v1r : ∀ r, r ≠ rLIT → r ≠ rN0 → r ≠ rX → r ≠ rXS → v1 r = v0 r := by
    intro r a1 a2 a3 a4
    simp only [v1, mX]
    rw [Function.update_of_ne (by simpa using a4), Function.update_of_ne (by simpa using a3), Function.update_of_ne a1,
      Function.update_of_ne a2, Function.update_of_ne a1]
  have v1X : v1 rX = v0 rLIT / 2 := by simp +decide [v1, mX, Function.update_apply]
  have s2 := gtFlagW_spec cap gX (ts src h o (regsOf v1 Z4 Z4 Z4 ok) cl)
    (by rw [show gX 2 = rSYSX from rfl, tsR_val src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide),
      v1r _ (by decide) (by decide) (by decide) (by decide)]; exact hSY0)
    (by rw [show gX 3 = rS1 from rfl, tsR_val src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide),
      v1r _ (by decide) (by decide) (by decide) (by decide)]; exact hs1)
    (by rw [show gX 4 = rS2 from rfl, tsR_val src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide),
      v1r _ (by decide) (by decide) (by decide) (by decide)]; exact hs2)
    (by rw [show gX 5 = rS3 from rfl, tsR_val src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide),
      v1r _ (by decide) (by decide) (by decide) (by decide)]; exact hs3)
    (by rw [show gX 0 = rSYS from rfl, tsR_val src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide),
      v1r _ (by decide) (by decide) (by decide) (by decide)]; omega)
    (by rw [show gX 1 = rX from rfl, tsR_val src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide), v1X]
        have := Nat.div_le_self (v0 rLIT) 2; omega)
    (by omega)
  rw [show gX 2 = rSYSX from rfl, show gX 1 = rX from rfl, show gX 0 = rSYS from rfl,
    tsR_val src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide),
    tsR_val src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide), v1X,
    v1r _ (by decide) (by decide) (by decide) (by decide),
    tsR_setv src h o cl v1 _ _ _ ok _ ⟨by decide, by decide⟩ (by decide)] at s2
  have e12 : Function.update v1 rSYSX (if v0 rLIT / 2 < v0 rSYS then 1 else 0) = posRegs v0 := rfl
  rw [e12] at s2
  have s3 := hb o ok hok hlen
  set ok' := if b then ok else 0 with hok'
  -- the cleanup
  have c1 := wclear_spec cap rX (v0 rLIT / 2) (ts src h (o ++ W) (regsOf (posRegs v0) Z4 Z4 Z4 ok') cl)
    (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide), posRegs_X])
    (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide), posRegs_X]
        have := Nat.div_le_self (v0 rLIT) 2; omega)
  rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at c1
  have c2 := wclear_spec cap rN0 (v0 rLIT % 2) (ts src h (o ++ W) (regsOf (Function.update (posRegs v0) rX 0) Z4 Z4 Z4 ok') cl)
    (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [posRegs, Function.update_apply])
    (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [posRegs, Function.update_apply]
        have := Nat.mod_lt (v0 rLIT) (show 2 > 0 by omega); omega)
  rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at c2
  have c3 := wclear_spec cap rXS (v0 rLIT / 2 * v0 rSS)
    (ts src h (o ++ W) (regsOf (Function.update (Function.update (posRegs v0) rX 0) rN0 0) Z4 Z4 Z4 ok') cl)
    (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [posRegs, Function.update_apply])
    (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [posRegs, Function.update_apply]
        have : v0 rLIT / 2 * v0 rSS ≤ v0 rLIT * v0 rSS := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
        omega)
  rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at c3
  have c4 := wclear_spec cap rSYSX (if v0 rLIT / 2 < v0 rSYS then 1 else 0)
    (ts src h (o ++ W) (regsOf (Function.update (Function.update (Function.update (posRegs v0) rX 0) rN0 0) rXS 0)
      Z4 Z4 Z4 ok') cl)
    (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [posRegs, Function.update_apply])
    (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [posRegs, Function.update_apply]
        split_ifs <;> omega)
  rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide), posClr_eq v0 hX0 hN0 hXS0 hSY0] at c4
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq c1 (WExec.seq c2 (WExec.seq c3 c4)))))) ?_
  have hd2 := Nat.div_le_self (v0 rLIT) 2
  have hm2 := Nat.mod_lt (v0 rLIT) (show 2 > 0 by omega)
  have hmm : v0 rLIT / 2 * v0 rSS ≤ v0 rLIT * v0 rSS := Nat.mul_le_mul_right _ hd2
  have hmm' : v0 rSS * (18 * (v0 rLIT / 2) + 8) ≤ 18 * (v0 rLIT * v0 rSS) + 8 * v0 rSS := by
    have : v0 rSS * (v0 rLIT / 2) ≤ v0 rSS * v0 rLIT := Nat.mul_le_mul_left _ hd2
    rw [Nat.mul_comm (v0 rLIT) (v0 rSS)]; nlinarith
  have hif : (if v0 rLIT / 2 < v0 rSYS then 1 else 0) ≤ 1 := by split_ifs <;> omega
  generalize (if v0 rLIT / 2 < v0 rSYS then 1 else 0) = t at hif ⊢
  show _ ≤ _
  simp only [show mX 1 = rSS from rfl]
  omega

/-- A magnitude block's cost at registers `v`. -/
def mbCost (B : ℕ) (v : Fin NR → ℕ) (Mx : Fin NR) (pat : Fin 4 → FK) : ℕ :=
  18 * v Mx + 3 + 1 + (blockCost B (v Mx) (v rSS) (v rXS) (v rYS) pat + 1 + (3 * v Mx + 1))

/-- The validity test's output at a position. -/
def outV (d : TWData) (v : Fin NR → ℕ) : List Bool :=
  if v rSYSX ≠ 0 then
    blockW d (withMag v rMb) 0 false (patV true 0) false ++ (blockW d (withMag v rMc) 0 true (patV true 1) false ++
      blockW d (withMag v rMa) 0 false (patV true 2) false)
  else
    blockW d (withMag v rMb) 0 false (patV false 0) false ++ (blockW d (withMag v rMd) 0 true (patV false 1) false ++
      blockW d (withMag v rMe) 0 false (patV false 2) false)

/-- The validity test's admissibility at a position. -/
def okV (d : TWData) (v : Fin NR → ℕ) : Bool :=
  if v rSYSX ≠ 0 then
    blockOk d (withMag v rMb) (patV true 0) false && (blockOk d (withMag v rMc) (patV true 1) false &&
      blockOk d (withMag v rMa) (patV true 2) false)
  else
    blockOk d (withMag v rMb) (patV false 0) false && (blockOk d (withMag v rMd) (patV false 1) false &&
      blockOk d (withMag v rMe) (patV false 2) false)

/-- The validity test's cost bound at a position. -/
def costV (B : ℕ) (v : Fin NR → ℕ) : ℕ :=
  mbCost B v rMb (patV true 0) + mbCost B v rMc (patV true 1) + mbCost B v rMa (patV true 2) +
    mbCost B v rMb (patV false 0) + mbCost B v rMd (patV false 1) + mbCost B v rMe (patV false 2) + 10

/-- The per-variable facts a position's blocks need. -/
structure VarOK (d : TWData) (v : Fin NR → ℕ) : Prop where
  xs : v rXS + v rSS ≤ d.es.length
  ys : v rYS + v rSS ≤ d.es.length
  par : v rX < d.pcs.length ∧ v rX < d.pf.length
  xc : v rX < d.crs.length ∧ v rX < d.ef.length
  yc : v rY < d.crs.length ∧ v rY < d.ef.length
  cx : v rXS + v rSS + 1 ≤ cap
  cy : v rYS + v rSS + 1 ≤ cap

theorem vBlocksP (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v : Fin NR → ℕ)
    (hg : GInv cap d B v) (hv : VarOK cap d v) :
    PSpec cap src vBlocks h cl v (30 * B + 40) (outV d v) (okV d v) (costV B v) := by
  have mb := fun (Mx : Fin NR) (hMx : Mx = rMa ∨ Mx = rMb ∨ Mx = rMc ∨ Mx = rMd ∨ Mx = rMe ∨ Mx = rMf) (kd : Fin 3)
    (κn : Bool) (pat : Fin 4 → FK) =>
    magBlockP cap src d hd B hB h cl v hg Mx hMx kd κn pat false hv.xs hv.ys hv.par hv.xc (fun h2 => absurd h2 (by simp))
      hv.cx hv.cy
  have bS := seqP cap src _ _ h cl v _ _ _ _ _ _ _ (mb rMb (by simp) 0 false (patV true 0))
    (seqP cap src _ _ h cl v _ _ _ _ _ _ _ (mb rMc (by simp) 0 true (patV true 1)) (mb rMa (by simp) 0 false (patV true 2)))
  have bN := seqP cap src _ _ h cl v _ _ _ _ _ _ _ (mb rMb (by simp) 0 false (patV false 0))
    (seqP cap src _ _ h cl v _ _ _ _ _ _ _ (mb rMd (by simp) 0 true (patV false 1)) (mb rMe (by simp) 0 false (patV false 2)))
  have bS' := monoP cap src _ h cl v _ _ _ _ (costV B v - 1) bS (by unfold costV mbCost; omega)
  have bN' := monoP cap src _ h cl v _ _ _ _ (costV B v - 1) bN (by unfold costV mbCost; omega)
  have := ifrP cap src rSYSX ⟨by decide, by decide⟩ (by decide) _ _ h cl v _ _ _ _ _ _ bS' bN'
  have e : costV B v - 1 + 1 = costV B v := by unfold costV; omega
  rw [e] at this
  exact this

/-- The second-moment test's output at a position. -/
def outQ (d : TWData) (v : Fin NR → ℕ) : List Bool := blockW d (withMag v rMb) 1 false (patQ 0) false

/-- The second-moment test's admissibility at a position. -/
def okQ (d : TWData) (v : Fin NR → ℕ) : Bool := blockOk d (withMag v rMb) (patQ 0) false

theorem qBlocksP (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v : Fin NR → ℕ)
    (hg : GInv cap d B v) (hv : VarOK cap d v) :
    PSpec cap src qBlocks h cl v (30 * B + 40) (outQ d v) (okQ d v) (mbCost B v rMb (patQ 0)) :=
  magBlockP cap src d hd B hB h cl v hg rMb (by simp) 1 false (patQ 0) false hv.xs hv.ys hv.par hv.xc
    (fun h2 => absurd h2 (by simp)) hv.cx hv.cy

/-! ## One clause of the clause test -/

/-- The clause test's blocks at a clause (literal signs `N₀`, `N₁`). -/
def muBlocks : WM 10 NR :=
  .seq (.ifr rN0 (magBlock rMa 2 false (patMu 0) true) (.ifr rN1 (magBlock rMa 2 false (patMu 0) true) .skip))
  (.seq (.ifr rN1 .skip (.ifr rN0 (magBlock rMf 2 true (patMu 1) true) (magBlock rMf 2 false (patMu 1) true)))
  (.seq (.ifr rN0 .skip (.ifr rN1 (magBlock rMf 2 true (patMu 2) true) (magBlock rMf 2 false (patMu 2) true)))
    (.ifr rN0 (.ifr rN1 (magBlock rMb 2 true (patMu 3) true) (magBlock rMb 2 false (patMu 3) true))
      (.ifr rN1 (magBlock rMb 2 false (patMu 3) true) (magBlock rMb 2 true (patMu 3) true)))))

/-- The clause test's output at a clause. -/
def outMu (d : TWData) (v : Fin NR → ℕ) : List Bool :=
  (if v rN0 ≠ 0 then blockW d (withMag v rMa) 2 false (patMu 0) true
    else if v rN1 ≠ 0 then blockW d (withMag v rMa) 2 false (patMu 0) true else []) ++
  ((if v rN1 ≠ 0 then [] else if v rN0 ≠ 0 then blockW d (withMag v rMf) 2 true (patMu 1) true
    else blockW d (withMag v rMf) 2 false (patMu 1) true) ++
  ((if v rN0 ≠ 0 then [] else if v rN1 ≠ 0 then blockW d (withMag v rMf) 2 true (patMu 2) true
    else blockW d (withMag v rMf) 2 false (patMu 2) true) ++
  (if v rN0 ≠ 0 then (if v rN1 ≠ 0 then blockW d (withMag v rMb) 2 true (patMu 3) true
      else blockW d (withMag v rMb) 2 false (patMu 3) true)
    else (if v rN1 ≠ 0 then blockW d (withMag v rMb) 2 false (patMu 3) true
      else blockW d (withMag v rMb) 2 true (patMu 3) true))))

/-- The clause test's admissibility at a clause. -/
def okMu (d : TWData) (v : Fin NR → ℕ) : Bool :=
  (if v rN0 ≠ 0 then blockOk d (withMag v rMa) (patMu 0) true
    else if v rN1 ≠ 0 then blockOk d (withMag v rMa) (patMu 0) true else true) &&
  ((if v rN1 ≠ 0 then true else if v rN0 ≠ 0 then blockOk d (withMag v rMf) (patMu 1) true
    else blockOk d (withMag v rMf) (patMu 1) true) &&
  ((if v rN0 ≠ 0 then true else if v rN1 ≠ 0 then blockOk d (withMag v rMf) (patMu 2) true
    else blockOk d (withMag v rMf) (patMu 2) true) &&
  (if v rN0 ≠ 0 then (if v rN1 ≠ 0 then blockOk d (withMag v rMb) (patMu 3) true
      else blockOk d (withMag v rMb) (patMu 3) true)
    else (if v rN1 ≠ 0 then blockOk d (withMag v rMb) (patMu 3) true
      else blockOk d (withMag v rMb) (patMu 3) true))))

/-- The clause test's cost bound at a clause. -/
def costMu (B : ℕ) (v : Fin NR → ℕ) : ℕ :=
  mbCost B v rMa (patMu 0) + 2 * mbCost B v rMf (patMu 1) + 2 * mbCost B v rMf (patMu 2) +
    2 * mbCost B v rMb (patMu 3) + 20

theorem muBlocksP (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (h : ℕ) (cl : Bool) (v : Fin NR → ℕ)
    (hg : GInv cap d B v) (hv : VarOK cap d v) :
    PSpec cap src muBlocks h cl v (30 * B + 40) (outMu d v) (okMu d v) (costMu B v) := by
  have mb := fun (Mx : Fin NR) (hMx : Mx = rMa ∨ Mx = rMb ∨ Mx = rMc ∨ Mx = rMd ∨ Mx = rMe ∨ Mx = rMf) (κn : Bool)
    (pat : Fin 4 → FK) =>
    magBlockP cap src d hd B hB h cl v hg Mx hMx 2 κn pat true hv.xs hv.ys hv.par hv.xc (fun _ => hv.yc) hv.cx hv.cy
  have pN0 : Plain rN0 := ⟨by decide, by decide⟩
  have pN1 : Plain rN1 := ⟨by decide, by decide⟩
  have sk := skipP cap src h cl v (30 * B + 40)
  have b0' := monoP cap src _ h cl v _ _ _ _ (mbCost B v rMa (patMu 0) + 2)
    (ifrP cap src rN0 pN0 (by decide) _ _ h cl v _ _ _ _ _ _
      (monoP cap src _ h cl v _ _ _ _ (mbCost B v rMa (patMu 0) + 1) (mb rMa (by simp) false (patMu 0)) (by simp only [mbCost]; omega))
      (ifrP cap src rN1 pN1 (by decide) _ _ h cl v _ _ _ _ _ _ (mb rMa (by simp) false (patMu 0))
        (monoP cap src _ h cl v _ _ _ _ _ sk (Nat.zero_le _)))) le_rfl
  have b1 := monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMf (patMu 1) + 2)
    (ifrP cap src rN1 pN1 (by decide) _ _ h cl v _ _ _ _ _ _
      (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMf (patMu 1) + 1) sk (Nat.zero_le _))
      (ifrP cap src rN0 pN0 (by decide) _ _ h cl v _ _ _ _ _ _
        (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMf (patMu 1)) (mb rMf (by simp) true (patMu 1)) (by simp only [mbCost]; omega))
        (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMf (patMu 1)) (mb rMf (by simp) false (patMu 1)) (by simp only [mbCost]; omega))))
    le_rfl
  have b2 := monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMf (patMu 2) + 2)
    (ifrP cap src rN0 pN0 (by decide) _ _ h cl v _ _ _ _ _ _
      (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMf (patMu 2) + 1) sk (Nat.zero_le _))
      (ifrP cap src rN1 pN1 (by decide) _ _ h cl v _ _ _ _ _ _
        (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMf (patMu 2)) (mb rMf (by simp) true (patMu 2)) (by simp only [mbCost]; omega))
        (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMf (patMu 2)) (mb rMf (by simp) false (patMu 2)) (by simp only [mbCost]; omega))))
    le_rfl
  have b3 := monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMb (patMu 3) + 2)
    (ifrP cap src rN0 pN0 (by decide) _ _ h cl v _ _ _ _ _ _
      (ifrP cap src rN1 pN1 (by decide) _ _ h cl v _ _ _ _ _ _
        (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMb (patMu 3)) (mb rMb (by simp) true (patMu 3)) (by simp only [mbCost]; omega))
        (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMb (patMu 3)) (mb rMb (by simp) false (patMu 3)) (by simp only [mbCost]; omega)))
      (ifrP cap src rN1 pN1 (by decide) _ _ h cl v _ _ _ _ _ _
        (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMb (patMu 3)) (mb rMb (by simp) false (patMu 3)) (by simp only [mbCost]; omega))
        (monoP cap src _ h cl v _ _ _ _ (2 * mbCost B v rMb (patMu 3)) (mb rMb (by simp) true (patMu 3)) (by simp only [mbCost]; omega))))
    (by simp only [mbCost]; omega)
  have all := seqP cap src _ _ h cl v _ _ _ _ _ _ _ b0' (seqP cap src _ _ h cl v _ _ _ _ _ _ _ b1
    (seqP cap src _ _ h cl v _ _ _ _ _ _ _ b2 b3))
  exact monoP cap src _ h cl v _ (outMu d v) (okMu d v) _ (costMu B v) all (by unfold costMu; omega)

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
