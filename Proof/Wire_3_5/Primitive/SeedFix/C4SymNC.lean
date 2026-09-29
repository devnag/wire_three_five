import Proof.Wire_3_5.Primitive.SeedFix.C4SymNB
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLk
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB2

/-! # C4.K SYM item (b), part 3: the SYM numbers machine at the unary capacity `2·2^{capExp C n} + 2`

P3:2929-2941, 2994-3000, 3011-3016 (the numbers `ℓ`, `Q`, `n_T`, `dRow` and the words the SYM stage reads), P3:3105-3115
(every size is `2^{O(k)}·poly(n)`, `k = O((B+1)²)`): at every SYM call of the gate, the SYM numbers machine
`C4Set.bigW Fp …` runs at the capacity `2·2^{capExp C n} + 2` from the cell's entry once `C ≥ C₀`, for a constant `C₀`
of the gate, the base constants and the free program's bounds, and leaves the thirty-nine words at the call's own
`Q = symCount`, `kh`, `ℓ`, `n_T·2^{w}`, `dRow` and the free numbers `Fp.val symX`.

* `symBigCost`, `SymBig`; `symX_small`, `caps_of`, `sym_fits`; **`sym_bigS`** (generic in the free program `Fp`: it
  reads only `ok_le`, `val_le`, `rho_le`).

Paper quantities of the main type: the SYM stage's words at the call's `Q`, `ℓ`, `n_T`, `dRow`, and the capacity
`2^{capExp C n}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymN
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- The SYM numbers machine's step bound (`bigS_spec`'s). -/
def symBigCost (cap n cr fe t sp L a nc Kb Cmax M fc : ℕ) : ℕ :=
  numsSCost cap n cr fe t sp L a nc Kb Cmax M + 1 +
    (400 * UnaryPow.sq cap + 1 + (fc + 1 + (200 * UnaryPow.sq cap + 1 + 400 * UnaryPow.sq cap)))

/-- **The SYM numbers machine's run at one call**: from the cell's entry, within `cost` at capacity `cap`, the
request stays on stream `0` and the thirty-nine words hold the call's own numbers. -/
def SymBig (Fp : FreeProg) (cr fe : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) (cap cost : ℕ) {kclk : ℕ}
    {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : I.StarAt n) : Prop :=
  ∃ (τ : WState (LNS 0) LNR) (c : ℕ),
    WExec cap (bigW Fp cr fe ζ Cδ C)
      (CellLoopD.blankCellD 0 (symReq n a ha Cs carriers translation).word [] 0
        (Data.unaryList (Data.symCounts a Cs carriers))) τ c ∧ c ≤ cost ∧
    τ.st (sk 0 0) = frame (symReq n a ha Cs carriers translation).word ∧
    ∀ j : Fin 39, τ.st (sk 0 (symO j)) = symClean (SeedFix.symCount I hs Cs carriers)
      (SeedFix.callKh (I.starParams n hs))
      (max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
        (Nat.clog 2 (SeedFix.symCount I hs Cs carriers)))
      (Enum.symNT I hs Cs carriers * 2 ^ wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.symCount I hs Cs carriers))
      (0 + C4Geo.dRow (I.starParams n hs) + C4Geo.dRow (I.starParams n hs))
      (Fp.val (C4SymW.symX I Cs carriers hs))
      (derVals (SeedFix.symCount I hs Cs carriers) (SeedFix.callKh (I.starParams n hs))
        (Fp.val (C4SymW.symX I Cs carriers hs) 0) (Fp.val (C4SymW.symX I Cs carriers hs) 1)) j

/-! ## Small facts -/

theorem stV_pos (m0 m1 m2 m3 : ℕ) : 1 ≤ SymDec.stV m0 m1 m2 m3 := by
  unfold SymDec.stV; exact Nat.succ_le_of_lt (by positivity)

theorem sk0_ne_symO (j : Fin 39) : sk 0 0 ≠ sk 0 (symO j) := by
  fin_cases j <;> decide

theorem blankD_st0 (w u : List Bool) : (CellLoopD.blankCellD 0 w [] 0 u).st (sk 0 0) = frame w := by
  have n3 : sk 0 0 ≠ sk 0 113 := by decide
  simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, n3]

theorem le2 {X M : ℕ} (h : X + 1 ≤ M) : X ≤ 2 * M + 2 := by omega

theorem le2' {X M : ℕ} (h : X + 1 ≤ M) : X + X + 3 ≤ 2 * M + 2 := by omega

theorem w_le {L K s ek eq : ℕ} (hL : L ≤ (ek + eq) * s) (hK : K + K ≤ ek * s) (hs : 1 ≤ s) :
    (1 + L + K) * 8 + 1 ≤ (9 + 8 * (ek + eq) + 8 * ek) * s := by
  have e : (9 + 8 * (ek + eq) + 8 * ek) * s = 9 * s + 8 * ((ek + eq) * s) + 8 * (ek * s) := by ring
  omega

theorem l3_le {L s e : ℕ} (hL : L ≤ e * s) (hs : 1 ≤ s) : L + L + 1 ≤ (2 * e + 1) * s := by
  have h : (2 * e + 1) * s = e * s + e * s + s := by ring
  omega

theorem dRow_le (P : StarParams) : C4Geo.dRow P ≤ 4 * (P.n + 2) := by
  rw [← C4SymL.dRow_link]
  have := (star_small P).2.2.2.2.2.2.2
  omega

section Small
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) {n a : ℕ}
  (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (hs : I.StarAt n)

/-- The call's `FreeIn` is small once each of its twelve fields is. -/
theorem symX_small (Ds : ℕ)
    (h1 : n ≤ 2 ^ (Ds * C4Cap.bsq n)) (h2 : SeedFix.callKh (I.starParams n hs) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h3 : Ledger.Lq n ≤ 2 ^ (Ds * C4Cap.bsq n)) (h4 : B.capOf .sym n ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h5 : a ≤ 2 ^ (Ds * C4Cap.bsq n)) (h6 : carriers.length ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h7 : (SymDec.cyOf Cs).sum ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h8 : SeedFix.symCount I hs Cs carriers ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h9 : max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.symCount I hs Cs carriers)) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h10 : Enum.symNT I hs Cs carriers ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h11 : wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.symCount I hs Cs carriers) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h12 : C4Geo.dRow (I.starParams n hs) ≤ 2 ^ (Ds * C4Cap.bsq n)) :
    C4SymW.FreeSmall Ds (C4SymW.symX I Cs carriers hs) :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

end Small

/-- **The capacity conditions of the SYM numbers machine** from the fits `X + 1 ≤ M` (pure arithmetic). -/
theorem caps_of (M Q kh gs fs pi b s r n tw cp : ℕ) (fQ : Q + 1 ≤ M) (fkk : kh + kh + 1 ≤ M)
    (fG : gs * fs * pi + 1 ≤ M) (fW : 2 ^ (wOf kh Q + 1) + 1 ≤ M) (fcnt : gs * fs * pi * 2 ^ wOf kh Q + 1 ≤ M)
    (fSm : 4 * (n + 2) + 1 ≤ M) (sb1 : b ≤ n) (sb2 : s ≤ n) (sb3 : r ≤ n) (_sb5 : (b - s) * (r / 2) ≤ n)
    (sb6 : r * b ≤ n) (sb8 : (n - r * b + 1) / 2 + (b - s) * (r / 2) ≤ 2 * n)
    (hgs : 1 ≤ gs) (hfs : 1 ≤ fs) (hpi : 1 ≤ pi) (ftw : tw + 1 ≤ M) (fcp : cp + 1 ≤ M)
    (fd0 : kh + kh + tw + 1 ≤ M)
    (fd1 : max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp +
      1 ≤ M)
    (fd3 : wOf kh Q + 1 + tw + 1 ≤ M) (fd4 : max (kh + kh) (Nat.clog 2 Q) * 8 + 1 ≤ M)
    (fl : 3 * max (kh + kh) (Nat.clog 2 Q) + Q + 1 ≤ M) :
    SeedCap (2 * M + 2) Q kh gs fs pi b s (r / 2) r n ∧ DerCap (2 * M + 2) Q kh tw cp ∧
      (∀ i, derVals Q kh tw cp i + derVals Q kh tw cp i + 3 ≤ 2 * M + 2) ∧
      Q - 1 < 2 ^ max (kh + kh) (Nat.clog 2 Q) ∧ Q + 1 ≤ 2 * M + 2 ∧
      3 * max (kh + kh) (Nat.clog 2 Q) + Q + 3 ≤ 2 * M + 2 ∧ kh + kh + 1 ≤ 2 * M + 2 ∧
      gs * fs * pi * 2 ^ wOf kh Q + 1 ≤ 2 * M + 2 ∧
      (0 + ((n - r * b + 1) / 2 + (b - s) * (r / 2)) + ((n - r * b + 1) / 2 + (b - s) * (r / 2))) +
        (0 + ((n - r * b + 1) / 2 + (b - s) * (r / 2)) + ((n - r * b + 1) / 2 + (b - s) * (r / 2))) + 3 ≤ 2 * M + 2 ∧
      17 ≤ 2 * M + 2 := by
  have hgf : gs * fs ≤ gs * fs * pi := Nat.le_mul_of_pos_right _ hpi
  have hg1 : gs ≤ gs * fs := Nat.le_mul_of_pos_right _ hfs
  have hf1 : fs ≤ gs * fs := Nat.le_mul_of_pos_left _ hgs
  have hp1 : pi ≤ gs * fs * pi := Nat.le_mul_of_pos_left _ (Nat.mul_pos hgs hfs)
  have hw2 : wOf kh Q + 1 < 2 ^ (wOf kh Q + 1) := Nat.lt_two_pow_self
  have hr2 : r / 2 ≤ r := Nat.div_le_self _ _
  have cQl : Q - 1 < 2 ^ max (kh + kh) (Nat.clog 2 Q) := by
    have h1 : Q ≤ 2 ^ Nat.clog 2 Q := Nat.le_pow_clog (by norm_num) Q
    have h2 : 2 ^ Nat.clog 2 Q ≤ 2 ^ max (kh + kh) (Nat.clog 2 Q) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    have h3 : 1 ≤ 2 ^ max (kh + kh) (Nat.clog 2 Q) := Nat.one_le_two_pow
    omega
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩, fun i => ?_, cQl, by omega, by omega,
    by omega, by omega, by omega, by omega⟩
  fin_cases i
  · show kh + kh + tw + (kh + kh + tw) + 3 ≤ 2 * M + 2; omega
  · show max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp +
      (max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + cp) + 3 ≤
      2 * M + 2
    omega
  · show wOf kh Q + 1 + (wOf kh Q + 1) + 3 ≤ 2 * M + 2; omega
  · show wOf kh Q + 1 + tw + (wOf kh Q + 1 + tw) + 3 ≤ 2 * M + 2; omega
  · show max (kh + kh) (Nat.clog 2 Q) * 8 + max (kh + kh) (Nat.clog 2 Q) * 8 + 3 ≤ 2 * M + 2; omega
  · show Q - 1 + (Q - 1) + 3 ≤ 2 * M + 2; omega
  · show max (kh + kh) (Nat.clog 2 Q) - 1 + (max (kh + kh) (Nat.clog 2 Q) - 1) + 3 ≤ 2 * M + 2; omega

end NearCubicWires.WireExponent3_5.PrimT.C4SymN
