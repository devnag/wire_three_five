import Proof.Wire_3_5.Primitive.SeedFix.C4SB

/-! # C4 per-call setup (item 3), part 3: the seed's numbers `ℓ`, `n_T`, `w`, `n_T·2^w`, `dRow`

P3:2929-2941 (samp:printable: "Take `ℓ ≥ max{k, ⌈log₂(Q+1)⌉}` and a field `F_{2^ℓ}`"; `SamplerPrintable.ellFor`:
`ℓ = max(1, 2kh, ⌈log₂ Q⌉)`), P3:3011-3016 (the printed objective's states `t < n_T` and completions, C4's loop
counter `n_T·2^w`, `w = 8 + 8ℓ + 8kh`), P3:1195-1196 (the printer's rows `dRow = leftCenterBits`): from the SYM
numbers of part 2, a register program on registers `64 … 126` (six segments, each within its own block) leaves

* `ℓ' = max(2kh, ⌈log₂ Q⌉)` in `X 2`, `n_T = |GapSeed|·|FlatSeed|·Π_j(m_j+1)²` in `N 0`, `w` in `WB 0`, `2^w` in
  `P 1`, `n_T·2^w` in `CC 0`, `dRow` in `ST 0`, `2·dRow` in `rD2`.

* the blocks, `segA … segF`, their specs, `seedW`, **`seed_spec`**.

Paper quantities of the main type: the seed field's size `ℓ` (`ellFor`), the state count `n_T`, the completions'
exponent `w`, the loop counter `n_T·2^w`, the printer's rows `dRow`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.ParseNat

/-- A block of `k` registers from `b` (below PA's decode blocks). -/
def blk (b k : ℕ) (h : b + k ≤ 250) : Fin k ↪ Fin LNR :=
  ⟨fun i => ⟨b + i.val, by have := i.isLt; unfold LNR; omega⟩, fun x y e => Fin.ext (by
    have := congrArg Fin.val e; simp at this; exact this)⟩

theorem blk_val (b k : ℕ) (h : b + k ≤ 250) (i : Fin k) : (blk b k h i).val = b + i.val := rfl

def E : Fin 10 ↪ Fin LNR := blk 64 10 (by norm_num)
def X : Fin 10 ↪ Fin LNR := blk 74 10 (by norm_num)
def N : Fin 5 ↪ Fin LNR := blk 84 5 (by norm_num)
def WB : Fin 5 ↪ Fin LNR := blk 89 5 (by norm_num)
def P : Fin 4 ↪ Fin LNR := blk 94 4 (by norm_num)
def CC : Fin 5 ↪ Fin LNR := blk 101 5 (by norm_num)
def SB : Fin 4 ↪ Fin LNR := blk 106 4 (by norm_num)
def MD : Fin 5 ↪ Fin LNR := blk 110 5 (by norm_num)
def MR : Fin 5 ↪ Fin LNR := blk 115 5 (by norm_num)
def ST : Fin 4 ↪ Fin LNR := blk 120 4 (by norm_num)
def rDr : Fin LNR := ⟨124, by decide⟩
def rRb : Fin LNR := ⟨125, by decide⟩
def rD2 : Fin LNR := ⟨126, by decide⟩

abbrev cp (a b : Fin LNR) : WM (LNS 0) LNR := FinalPass.Hash4.wcopyR a b rT0

theorem vsv {ns nr : ℕ} (σ : WState ns nr) (r q : Fin nr) (x : ℕ) :
    (σ.setv r x).val q = if q = r then x else σ.val q := by simp [WState.setv, Function.update_apply, eq_comm]

/-- The completions' exponent `w = 8·(1 + ℓ + kh)` at `ℓ = max(2kh, ⌈log₂ Q⌉)`. -/
def wOf (kh Q : ℕ) : ℕ := (1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8

/-- The segments' capacity bounds. -/
structure SeedCap (cap Q kh gs fs pi b s r2 r n : ℕ) : Prop where
  cQ : Q + 2 ≤ cap
  ckh : kh + kh ≤ cap
  cg : gs * fs ≤ cap
  cgp : gs * fs * pi ≤ cap
  cgs : gs ≤ cap
  cfs : fs ≤ cap
  cpi : pi ≤ cap
  cw : 2 ^ (wOf kh Q + 1) ≤ cap
  cc : gs * fs * pi * 2 ^ wOf kh Q ≤ cap
  cb : b ≤ cap
  cs : s ≤ cap
  cr2 : r2 ≤ cap
  cr : r ≤ cap
  cn : n ≤ cap
  cbs : (b - s) * r2 ≤ cap
  crb : r * b ≤ cap
  cn1 : n - r * b + 1 ≤ cap
  cd : ((n - r * b + 1) / 2 + (b - s) * r2) + ((n - r * b + 1) / 2 + (b - s) * r2) ≤ cap

/-- Segment A of the seed's numbers. -/
def segA : WM (LNS 0) LNR := (.seq (cp (KB 52) (E 0)) (.seq (SymQM.clogW E) (.seq (cp (SGb 8) (X 0)) (.seq (addTo (SGb 8) (X 0) rT0) (.seq (cp (E 1) (X 1)) (SymQM.maxW X))))))

theorem segA_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh gs fs pi b s r2 r n : ℕ) (eQ : s0.val (KB 52) = Q) (ekh : s0.val (SGb 8) = kh)
    (hzs : ∀ q : Fin LNR, 64 ≤ q.val → q.val < 84 → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : SeedCap cap Q kh gs fs pi b s r2 r n) :
    ∃ τ c, WExec cap segA s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)) ∧ τ.val (X 0) = (kh + kh) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, (q.val < 64 ∨ 84 ≤ q.val) → q ≠ rT0 → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨cQ, ckh, cg, cgp, cgs, cfs, cpi, cw, cc, cb, cs, cr2, cr, cn, cbs, crb, cn1, cd⟩ := hc
  simp only [wOf] at *
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hW : (1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 < 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := Nat.lt_two_pow_self
  have hp2 : 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 + 1) = 2 * 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := by rw [pow_succ]; ring
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv (E 0) Q := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (E 1) (Nat.clog 2 Q) := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (X 0) kh := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (X 0) (kh + kh) := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = (s4).setv (X 1) (Nat.clog 2 Q) := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ z : WState (LNS 0) LNR, z = (s5).setv (X 2) (max (kh + kh) (Nat.clog 2 Q)) := ⟨_, rfl⟩
  have h1 : WExec cap (cp (KB 52) (E 0)) s0 s1 (18 * Q + 3) := by
    have ex : s0.val (KB 52) = Q := eQ
    have w := wc cap (KB 52) (E 0) s0 (by decide) (by decide) (by decide) (hzs _ (by decide) (by decide)) (hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (SymQM.clogW E) s1 s2 (20 * UnaryPow.sq cap) := by
    have w := SymQM.clogW_spec cap E s1 Q (by rw [hs1, vsv, if_pos rfl]) (fun i hi => by
      rw [hs1, vsv, if_neg (fun e => by have := congrArg Fin.val e; simp [E, blk_val] at this; omega)]
      exact hzs _ (by simp [E, blk_val]) (by simp [E, blk_val]; omega)) (by omega)
    rw [hs2]; exact w
  have h3 : WExec cap (cp (SGb 8) (X 0)) s2 s3 (18 * kh + 3) := by
    have ex : s2.val (SGb 8) = kh := by rw [hs2, vsv, if_neg (show ¬ ((SGb 8) = (E 1)) by decide), hs1, vsv, if_neg (show ¬ ((SGb 8) = (E 0)) by decide), ekh]
    have w := wc cap (SGb 8) (X 0) s2 (by decide) (by decide) (by decide) (by rw [hs2, vsv, if_neg (show ¬ ((X 0) = (E 1)) by decide), hs1, vsv, if_neg (show ¬ ((X 0) = (E 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs2, vsv, if_neg (show ¬ (rT0 = (E 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (E 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs3]; exact w
  have h4 : WExec cap (addTo (SGb 8) (X 0) rT0) s3 s4 (18 * kh + 3) := by
    have ep : s3.val (SGb 8) = kh := by rw [hs3, vsv, if_neg (show ¬ ((SGb 8) = (X 0)) by decide), hs2, vsv, if_neg (show ¬ ((SGb 8) = (E 1)) by decide), hs1, vsv, if_neg (show ¬ ((SGb 8) = (E 0)) by decide), ekh]
    have ev : s3.val (X 0) = kh := by rw [hs3, vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (SGb 8) (X 0) rT0 (by decide) (by decide) (by decide) s3 (by rw [hs3, vsv, if_neg (show ¬ (rT0 = (X 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (E 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (E 0)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs4]; exact w
  have h5 : WExec cap (cp (E 1) (X 1)) s4 s5 (18 * (Nat.clog 2 Q) + 3) := by
    have ex : s4.val (E 1) = (Nat.clog 2 Q) := by rw [hs4, vsv, if_neg (show ¬ ((E 1) = (X 0)) by decide), hs3, vsv, if_neg (show ¬ ((E 1) = (X 0)) by decide), hs2, vsv, if_pos rfl]
    have w := wc cap (E 1) (X 1) s4 (by decide) (by decide) (by decide) (by rw [hs4, vsv, if_neg (show ¬ ((X 1) = (X 0)) by decide), hs3, vsv, if_neg (show ¬ ((X 1) = (X 0)) by decide), hs2, vsv, if_neg (show ¬ ((X 1) = (E 1)) by decide), hs1, vsv, if_neg (show ¬ ((X 1) = (E 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs4, vsv, if_neg (show ¬ (rT0 = (X 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (X 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (E 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (E 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs5]; exact w
  have h6 : WExec cap (SymQM.maxW X) s5 s6 (6 * UnaryPow.sq cap) := by
    have w := SymQM.maxW_spec cap X s5 (kh + kh) (Nat.clog 2 Q) (by rw [hs5, vsv, if_neg (show ¬ ((X 0) = (X 1)) by decide), hs4, vsv, if_pos rfl]) (by rw [hs5, vsv, if_pos rfl]) (fun i hi => by
      have n0 : ∀ j : Fin 10, j.val < 2 → X i ≠ X j := fun j hj e => by have := congrArg Fin.val e; simp [X, blk_val] at this; omega
      have nE : ∀ j : Fin 10, X i ≠ E j := fun j e => by have := congrArg Fin.val e; simp [X, E, blk_val] at this; omega
      rw [hs5, vsv, if_neg (n0 1 (by decide)), hs4, vsv, if_neg (n0 0 (by decide)), hs3, vsv, if_neg (n0 0 (by decide)), hs2, vsv, if_neg (nE 1), hs1, vsv, if_neg (nE 0)]
      exact hzs _ (by simp [X, blk_val]; omega) (by simp [X, blk_val]; omega)) (by omega) (by omega) (by omega)
    rw [hs6]; exact w
  have f0 : s6.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs6, vsv, if_pos rfl]
  have f1 : s6.val (X 0) = (kh + kh) := by rw [hs6, vsv, if_neg (show ¬ ((X 0) = (X 2)) by decide), hs5, vsv, if_neg (show ¬ ((X 0) = (X 1)) by decide), hs4, vsv, if_pos rfl]
  have fT : s6.val rT0 = 0 := by rw [hs6, vsv, if_neg (show ¬ (rT0 = (X 2)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (X 1)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (X 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (X 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (E 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (E 0)) by decide)]; exact hT
  refine ⟨s6, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 (h6))))), ?_, f0, f1, fT, fun q hq hqT => ?_, ?_, ?_, ?_⟩
  · have e2 : ∀ x y z : ℕ, 18 * (x * y * z) = 18 * x * y * z := fun x y z => by ring
    have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, (64 ≤ r'.val ∧ r'.val < 84) → q ≠ r' := fun r' h e => by subst e; omega
    rw [hs6, vsv, if_neg (nq (X 2) (by decide)), hs5, vsv, if_neg (nq (X 1) (by decide)), hs4, vsv, if_neg (nq (X 0) (by decide)), hs3, vsv, if_neg (nq (X 0) (by decide)), hs2, vsv, if_neg (nq (E 1) (by decide)), hs1, vsv, if_neg (nq (E 0) (by decide))]
  · simp only [hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- Segment B of the seed's numbers. -/
def segB : WM (LNS 0) LNR := (.seq (cp (G 21) (N 0)) (.seq (cp (G 41) (N 1)) (.seq (SparseNum.mulByW N) (.seq (WM.clear (N 1)) (.seq (cp (G 52) (N 1)) (SparseNum.mulByW N))))))

theorem segB_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh gs fs pi b s r2 r n : ℕ) (e21 : s0.val (G 21) = gs) (e41 : s0.val (G 41) = fs) (e52 : s0.val (G 52) = pi)
    (hzs : ∀ q : Fin LNR, 84 ≤ q.val → q.val < 89 → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : SeedCap cap Q kh gs fs pi b s r2 r n) :
    ∃ τ c, WExec cap segB s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (N 0) = (gs * fs * pi) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, (q.val < 84 ∨ 89 ≤ q.val) → q ≠ rT0 → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨cQ, ckh, cg, cgp, cgs, cfs, cpi, cw, cc, cb, cs, cr2, cr, cn, cbs, crb, cn1, cd⟩ := hc
  simp only [wOf] at *
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hW : (1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 < 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := Nat.lt_two_pow_self
  have hp2 : 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 + 1) = 2 * 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := by rw [pow_succ]; ring
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv (N 0) gs := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (N 1) fs := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (N 0) (gs * fs) := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (N 1) 0 := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = (s4).setv (N 1) pi := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ z : WState (LNS 0) LNR, z = (s5).setv (N 0) (gs * fs * pi) := ⟨_, rfl⟩
  have h1 : WExec cap (cp (G 21) (N 0)) s0 s1 (18 * gs + 3) := by
    have ex : s0.val (G 21) = gs := e21
    have w := wc cap (G 21) (N 0) s0 (by decide) (by decide) (by decide) (hzs _ (by decide) (by decide)) (hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (cp (G 41) (N 1)) s1 s2 (18 * fs + 3) := by
    have ex : s1.val (G 41) = fs := by rw [hs1, vsv, if_neg (show ¬ ((G 41) = (N 0)) by decide), e41]
    have w := wc cap (G 41) (N 1) s1 (by decide) (by decide) (by decide) (by rw [hs1, vsv, if_neg (show ¬ ((N 1) = (N 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs1, vsv, if_neg (show ¬ (rT0 = (N 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs2]; exact w
  have h3 : WExec cap (SparseNum.mulByW N) s2 s3 (3 * UnaryPow.sq cap) := by
    have e0 : s2.val (N 0) = gs := by rw [hs2, vsv, if_neg (show ¬ ((N 0) = (N 1)) by decide), hs1, vsv, if_pos rfl]
    have e1 : s2.val (N 1) = fs := by rw [hs2, vsv, if_pos rfl]
    have w := SparseNum.mulByW_spec cap N s2 (by rw [hs2, vsv, if_neg (show ¬ ((N 2) = (N 1)) by decide), hs1, vsv, if_neg (show ¬ ((N 2) = (N 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs2, vsv, if_neg (show ¬ ((N 3) = (N 1)) by decide), hs1, vsv, if_neg (show ¬ ((N 3) = (N 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs2, vsv, if_neg (show ¬ ((N 4) = (N 1)) by decide), hs1, vsv, if_neg (show ¬ ((N 4) = (N 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [e0, e1]; omega) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs3]; exact w
  have h4 : WExec cap (WM.clear (N 1)) s3 s4 (3 * fs + 1) := by
    have ex : s3.val (N 1) = fs := by rw [hs3, vsv, if_neg (show ¬ ((N 1) = (N 0)) by decide), hs2, vsv, if_pos rfl]
    have w := FinalPass.Tm.wclear_spec cap (N 1) fs s3 ex (by rw [ex]; omega)
    rw [hs4]; exact w
  have h5 : WExec cap (cp (G 52) (N 1)) s4 s5 (18 * pi + 3) := by
    have ex : s4.val (G 52) = pi := by rw [hs4, vsv, if_neg (show ¬ ((G 52) = (N 1)) by decide), hs3, vsv, if_neg (show ¬ ((G 52) = (N 0)) by decide), hs2, vsv, if_neg (show ¬ ((G 52) = (N 1)) by decide), hs1, vsv, if_neg (show ¬ ((G 52) = (N 0)) by decide), e52]
    have w := wc cap (G 52) (N 1) s4 (by decide) (by decide) (by decide) (by rw [hs4, vsv, if_pos rfl]) (by rw [hs4, vsv, if_neg (show ¬ (rT0 = (N 1)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (N 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (N 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (N 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs5]; exact w
  have h6 : WExec cap (SparseNum.mulByW N) s5 s6 (3 * UnaryPow.sq cap) := by
    have e0 : s5.val (N 0) = (gs * fs) := by rw [hs5, vsv, if_neg (show ¬ ((N 0) = (N 1)) by decide), hs4, vsv, if_neg (show ¬ ((N 0) = (N 1)) by decide), hs3, vsv, if_pos rfl]
    have e1 : s5.val (N 1) = pi := by rw [hs5, vsv, if_pos rfl]
    have w := SparseNum.mulByW_spec cap N s5 (by rw [hs5, vsv, if_neg (show ¬ ((N 2) = (N 1)) by decide), hs4, vsv, if_neg (show ¬ ((N 2) = (N 1)) by decide), hs3, vsv, if_neg (show ¬ ((N 2) = (N 0)) by decide), hs2, vsv, if_neg (show ¬ ((N 2) = (N 1)) by decide), hs1, vsv, if_neg (show ¬ ((N 2) = (N 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs5, vsv, if_neg (show ¬ ((N 3) = (N 1)) by decide), hs4, vsv, if_neg (show ¬ ((N 3) = (N 1)) by decide), hs3, vsv, if_neg (show ¬ ((N 3) = (N 0)) by decide), hs2, vsv, if_neg (show ¬ ((N 3) = (N 1)) by decide), hs1, vsv, if_neg (show ¬ ((N 3) = (N 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs5, vsv, if_neg (show ¬ ((N 4) = (N 1)) by decide), hs4, vsv, if_neg (show ¬ ((N 4) = (N 1)) by decide), hs3, vsv, if_neg (show ¬ ((N 4) = (N 0)) by decide), hs2, vsv, if_neg (show ¬ ((N 4) = (N 1)) by decide), hs1, vsv, if_neg (show ¬ ((N 4) = (N 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [e0, e1]; omega) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs6]; exact w
  have f0 : s6.val (N 0) = (gs * fs * pi) := by rw [hs6, vsv, if_pos rfl]
  have fT : s6.val rT0 = 0 := by rw [hs6, vsv, if_neg (show ¬ (rT0 = (N 0)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (N 1)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (N 1)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (N 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (N 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (N 0)) by decide)]; exact hT
  refine ⟨s6, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 (h6))))), ?_, f0, fT, fun q hq hqT => ?_, ?_, ?_, ?_⟩
  · have e2 : ∀ x y z : ℕ, 18 * (x * y * z) = 18 * x * y * z := fun x y z => by ring
    have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, (84 ≤ r'.val ∧ r'.val < 89) → q ≠ r' := fun r' h e => by subst e; omega
    rw [hs6, vsv, if_neg (nq (N 0) (by decide)), hs5, vsv, if_neg (nq (N 1) (by decide)), hs4, vsv, if_neg (nq (N 1) (by decide)), hs3, vsv, if_neg (nq (N 0) (by decide)), hs2, vsv, if_neg (nq (N 1) (by decide)), hs1, vsv, if_neg (nq (N 0) (by decide))]
  · simp only [hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- Segment C of the seed's numbers. -/
def segC : WM (LNS 0) LNR := (.seq (.inc (WB 0)) (.seq (addTo (X 2) (WB 0) rT0) (.seq (addTo (SGb 8) (WB 0) rT0) (.seq (StarNums.incN (WB 1) 8) (SparseNum.mulByW WB)))))

theorem segC_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh gs fs pi b s r2 r n : ℕ) (eX2 : s0.val (X 2) = (max (kh + kh) (Nat.clog 2 Q))) (ekh : s0.val (SGb 8) = kh)
    (hzs : ∀ q : Fin LNR, 89 ≤ q.val → q.val < 94 → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : SeedCap cap Q kh gs fs pi b s r2 r n) :
    ∃ τ c, WExec cap segC s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (WB 0) = (wOf kh Q) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, (q.val < 89 ∨ 94 ≤ q.val) → q ≠ rT0 → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨cQ, ckh, cg, cgp, cgs, cfs, cpi, cw, cc, cb, cs, cr2, cr, cn, cbs, crb, cn1, cd⟩ := hc
  simp only [wOf] at *
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hW : (1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 < 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := Nat.lt_two_pow_self
  have hp2 : 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 + 1) = 2 * 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := by rw [pow_succ]; ring
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv (WB 0) (1) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (WB 0) (1 + max (kh + kh) (Nat.clog 2 Q)) := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (WB 0) ((1 + max (kh + kh) (Nat.clog 2 Q) + kh)) := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (WB 1) 8 := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = (s4).setv (WB 0) (((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) := ⟨_, rfl⟩
  have h1 : WExec cap (.inc (WB 0)) s0 s1 3 := by
    have ex : s0.val (WB 0) = 0 := hzs _ (by decide) (by decide)
    have w := WExec.inc (cap := cap) (WB 0) s0 (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (addTo (X 2) (WB 0) rT0) s1 s2 (18 * (max (kh + kh) (Nat.clog 2 Q)) + 3) := by
    have ep : s1.val (X 2) = (max (kh + kh) (Nat.clog 2 Q)) := by rw [hs1, vsv, if_neg (show ¬ ((X 2) = (WB 0)) by decide), eX2]
    have ev : s1.val (WB 0) = 1 := by rw [hs1, vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (X 2) (WB 0) rT0 (by decide) (by decide) (by decide) s1 (by rw [hs1, vsv, if_neg (show ¬ (rT0 = (WB 0)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs2]; exact w
  have h3 : WExec cap (addTo (SGb 8) (WB 0) rT0) s2 s3 (18 * kh + 3) := by
    have ep : s2.val (SGb 8) = kh := by rw [hs2, vsv, if_neg (show ¬ ((SGb 8) = (WB 0)) by decide), hs1, vsv, if_neg (show ¬ ((SGb 8) = (WB 0)) by decide), ekh]
    have ev : s2.val (WB 0) = (1 + max (kh + kh) (Nat.clog 2 Q)) := by rw [hs2, vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (SGb 8) (WB 0) rT0 (by decide) (by decide) (by decide) s2 (by rw [hs2, vsv, if_neg (show ¬ (rT0 = (WB 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (WB 0)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs3]; exact w
  have h4 : WExec cap (StarNums.incN (WB 1) 8) s3 s4 (4 * 8) := by
    have ex : s3.val (WB 1) = 0 := by rw [hs3, vsv, if_neg (show ¬ ((WB 1) = (WB 0)) by decide), hs2, vsv, if_neg (show ¬ ((WB 1) = (WB 0)) by decide), hs1, vsv, if_neg (show ¬ ((WB 1) = (WB 0)) by decide)]; exact hzs _ (by decide) (by decide)
    have w := StarNums.incN_spec cap (WB 1) 8 s3 (by rw [ex]; omega)
    rw [ex, Nat.zero_add] at w; rw [hs4]; exact w
  have h5 : WExec cap (SparseNum.mulByW WB) s4 s5 (3 * UnaryPow.sq cap) := by
    have e0 : s4.val (WB 0) = (1 + max (kh + kh) (Nat.clog 2 Q) + kh) := by rw [hs4, vsv, if_neg (show ¬ ((WB 0) = (WB 1)) by decide), hs3, vsv, if_pos rfl]
    have e1 : s4.val (WB 1) = 8 := by rw [hs4, vsv, if_pos rfl]
    have w := SparseNum.mulByW_spec cap WB s4 (by rw [hs4, vsv, if_neg (show ¬ ((WB 2) = (WB 1)) by decide), hs3, vsv, if_neg (show ¬ ((WB 2) = (WB 0)) by decide), hs2, vsv, if_neg (show ¬ ((WB 2) = (WB 0)) by decide), hs1, vsv, if_neg (show ¬ ((WB 2) = (WB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs4, vsv, if_neg (show ¬ ((WB 3) = (WB 1)) by decide), hs3, vsv, if_neg (show ¬ ((WB 3) = (WB 0)) by decide), hs2, vsv, if_neg (show ¬ ((WB 3) = (WB 0)) by decide), hs1, vsv, if_neg (show ¬ ((WB 3) = (WB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs4, vsv, if_neg (show ¬ ((WB 4) = (WB 1)) by decide), hs3, vsv, if_neg (show ¬ ((WB 4) = (WB 0)) by decide), hs2, vsv, if_neg (show ¬ ((WB 4) = (WB 0)) by decide), hs1, vsv, if_neg (show ¬ ((WB 4) = (WB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [e0, e1]; omega) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs5]; exact w
  have f0 : s5.val (WB 0) = ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := by rw [hs5, vsv, if_pos rfl]
  have fT : s5.val rT0 = 0 := by rw [hs5, vsv, if_neg (show ¬ (rT0 = (WB 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (WB 1)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (WB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (WB 0)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (WB 0)) by decide)]; exact hT
  refine ⟨s5, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (h5)))), ?_, f0, fT, fun q hq hqT => ?_, ?_, ?_, ?_⟩
  · have e2 : ∀ x y z : ℕ, 18 * (x * y * z) = 18 * x * y * z := fun x y z => by ring
    have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, (89 ≤ r'.val ∧ r'.val < 94) → q ≠ r' := fun r' h e => by subst e; omega
    rw [hs5, vsv, if_neg (nq (WB 0) (by decide)), hs4, vsv, if_neg (nq (WB 1) (by decide)), hs3, vsv, if_neg (nq (WB 0) (by decide)), hs2, vsv, if_neg (nq (WB 0) (by decide)), hs1, vsv, if_neg (nq (WB 0) (by decide))]
  · simp only [hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- Segment D of the seed's numbers. -/
def segD : WM (LNS 0) LNR := (.seq (cp (WB 0) (P 0)) (.seq (UnaryArith.pow2W P) (.seq (cp (N 0) (CC 0)) (.seq (cp (P 1) (CC 1)) (SparseNum.mulByW CC)))))

theorem segD_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh gs fs pi b s r2 r n : ℕ) (eW0 : s0.val (WB 0) = (wOf kh Q)) (eN0 : s0.val (N 0) = (gs * fs * pi))
    (hzs : ∀ q : Fin LNR, 94 ≤ q.val → q.val < 106 → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : SeedCap cap Q kh gs fs pi b s r2 r n) :
    ∃ τ c, WExec cap segD s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (P 1) = (2 ^ (wOf kh Q)) ∧ τ.val (CC 0) = (gs * fs * pi * 2 ^ (wOf kh Q)) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, (q.val < 94 ∨ 106 ≤ q.val) → q ≠ rT0 → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨cQ, ckh, cg, cgp, cgs, cfs, cpi, cw, cc, cb, cs, cr2, cr, cn, cbs, crb, cn1, cd⟩ := hc
  simp only [wOf] at *
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hW : (1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 < 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := Nat.lt_two_pow_self
  have hp2 : 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 + 1) = 2 * 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := by rw [pow_succ]; ring
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv (P 0) ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (P 1) (2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (CC 0) (gs * fs * pi) := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (CC 1) (2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = (s4).setv (CC 0) (gs * fs * pi * 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) := ⟨_, rfl⟩
  have h1 : WExec cap (cp (WB 0) (P 0)) s0 s1 (18 * ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) + 3) := by
    have ex : s0.val (WB 0) = ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := eW0
    have w := wc cap (WB 0) (P 0) s0 (by decide) (by decide) (by decide) (hzs _ (by decide) (by decide)) (hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (UnaryArith.pow2W P) s1 s2 (UnaryPow.sq cap) := by
    have w := SymQM.pow2v cap P ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) s1 (by rw [hs1, vsv, if_pos rfl]) (by rw [hs1, vsv, if_neg (show ¬ ((P 1) = (P 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs1, vsv, if_neg (show ¬ ((P 2) = (P 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs1, vsv, if_neg (show ¬ ((P 3) = (P 0)) by decide)]; exact hzs _ (by decide) (by decide)) cw
    rw [hs2]; exact w
  have h3 : WExec cap (cp (N 0) (CC 0)) s2 s3 (18 * (gs * fs * pi) + 3) := by
    have ex : s2.val (N 0) = (gs * fs * pi) := by rw [hs2, vsv, if_neg (show ¬ ((N 0) = (P 1)) by decide), hs1, vsv, if_neg (show ¬ ((N 0) = (P 0)) by decide), eN0]
    have w := wc cap (N 0) (CC 0) s2 (by decide) (by decide) (by decide) (by rw [hs2, vsv, if_neg (show ¬ ((CC 0) = (P 1)) by decide), hs1, vsv, if_neg (show ¬ ((CC 0) = (P 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs2, vsv, if_neg (show ¬ (rT0 = (P 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (P 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs3]; exact w
  have h4 : WExec cap (cp (P 1) (CC 1)) s3 s4 (18 * (2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) + 3) := by
    have ex : s3.val (P 1) = (2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) := by rw [hs3, vsv, if_neg (show ¬ ((P 1) = (CC 0)) by decide), hs2, vsv, if_pos rfl]
    have w := wc cap (P 1) (CC 1) s3 (by decide) (by decide) (by decide) (by rw [hs3, vsv, if_neg (show ¬ ((CC 1) = (CC 0)) by decide), hs2, vsv, if_neg (show ¬ ((CC 1) = (P 1)) by decide), hs1, vsv, if_neg (show ¬ ((CC 1) = (P 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs3, vsv, if_neg (show ¬ (rT0 = (CC 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (P 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (P 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs4]; exact w
  have h5 : WExec cap (SparseNum.mulByW CC) s4 s5 (3 * UnaryPow.sq cap) := by
    have e0 : s4.val (CC 0) = (gs * fs * pi) := by rw [hs4, vsv, if_neg (show ¬ ((CC 0) = (CC 1)) by decide), hs3, vsv, if_pos rfl]
    have e1 : s4.val (CC 1) = (2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) := by rw [hs4, vsv, if_pos rfl]
    have w := SparseNum.mulByW_spec cap CC s4 (by rw [hs4, vsv, if_neg (show ¬ ((CC 2) = (CC 1)) by decide), hs3, vsv, if_neg (show ¬ ((CC 2) = (CC 0)) by decide), hs2, vsv, if_neg (show ¬ ((CC 2) = (P 1)) by decide), hs1, vsv, if_neg (show ¬ ((CC 2) = (P 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs4, vsv, if_neg (show ¬ ((CC 3) = (CC 1)) by decide), hs3, vsv, if_neg (show ¬ ((CC 3) = (CC 0)) by decide), hs2, vsv, if_neg (show ¬ ((CC 3) = (P 1)) by decide), hs1, vsv, if_neg (show ¬ ((CC 3) = (P 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs4, vsv, if_neg (show ¬ ((CC 4) = (CC 1)) by decide), hs3, vsv, if_neg (show ¬ ((CC 4) = (CC 0)) by decide), hs2, vsv, if_neg (show ¬ ((CC 4) = (P 1)) by decide), hs1, vsv, if_neg (show ¬ ((CC 4) = (P 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [e0, e1]; omega) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs5]; exact w
  have f0 : s5.val (P 1) = (2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) := by rw [hs5, vsv, if_neg (show ¬ ((P 1) = (CC 0)) by decide), hs4, vsv, if_neg (show ¬ ((P 1) = (CC 1)) by decide), hs3, vsv, if_neg (show ¬ ((P 1) = (CC 0)) by decide), hs2, vsv, if_pos rfl]
  have f1 : s5.val (CC 0) = (gs * fs * pi * 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8)) := by rw [hs5, vsv, if_pos rfl]
  have fT : s5.val rT0 = 0 := by rw [hs5, vsv, if_neg (show ¬ (rT0 = (CC 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (CC 1)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (CC 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (P 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (P 0)) by decide)]; exact hT
  refine ⟨s5, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (h5)))), ?_, f0, f1, fT, fun q hq hqT => ?_, ?_, ?_, ?_⟩
  · have e2 : ∀ x y z : ℕ, 18 * (x * y * z) = 18 * x * y * z := fun x y z => by ring
    have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, (94 ≤ r'.val ∧ r'.val < 106) → q ≠ r' := fun r' h e => by subst e; omega
    rw [hs5, vsv, if_neg (nq (CC 0) (by decide)), hs4, vsv, if_neg (nq (CC 1) (by decide)), hs3, vsv, if_neg (nq (CC 0) (by decide)), hs2, vsv, if_neg (nq (P 1) (by decide)), hs1, vsv, if_neg (nq (P 0) (by decide))]
  · simp only [hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- Segment E of the seed's numbers. -/
def segE : WM (LNS 0) LNR := (.seq (cp (SGb 5) (SB 0)) (.seq (cp (SGb 4) (SB 1)) (.seq (UnaryArith.subW SB) (.seq (cp (SB 0) (MD 0)) (.seq (cp (SGb 6) (MD 1)) (.seq (SparseNum.mulByW MD) (.seq (cp (SGb 3) (MR 0)) (.seq (cp (SGb 5) (MR 1)) (SparseNum.mulByW MR)))))))))

theorem segE_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh gs fs pi b s r2 r n : ℕ) (eb : s0.val (SGb 5) = b) (es : s0.val (SGb 4) = s) (er2 : s0.val (SGb 6) = r2) (er : s0.val (SGb 3) = r)
    (hzs : ∀ q : Fin LNR, 106 ≤ q.val → q.val < 120 → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : SeedCap cap Q kh gs fs pi b s r2 r n) :
    ∃ τ c, WExec cap segE s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (MD 0) = ((b - s) * r2) ∧ τ.val (MR 0) = (r * b) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, (q.val < 106 ∨ 120 ≤ q.val) → q ≠ rT0 → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨cQ, ckh, cg, cgp, cgs, cfs, cpi, cw, cc, cb, cs, cr2, cr, cn, cbs, crb, cn1, cd⟩ := hc
  simp only [wOf] at *
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hW : (1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 < 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := Nat.lt_two_pow_self
  have hp2 : 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 + 1) = 2 * 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := by rw [pow_succ]; ring
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv (SB 0) b := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (SB 1) s := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (SB 0) (b - s) := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (MD 0) (b - s) := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = (s4).setv (MD 1) r2 := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ z : WState (LNS 0) LNR, z = (s5).setv (MD 0) ((b - s) * r2) := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ z : WState (LNS 0) LNR, z = (s6).setv (MR 0) r := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ z : WState (LNS 0) LNR, z = (s7).setv (MR 1) b := ⟨_, rfl⟩
  obtain ⟨s9, hs9⟩ : ∃ z : WState (LNS 0) LNR, z = (s8).setv (MR 0) (r * b) := ⟨_, rfl⟩
  have h1 : WExec cap (cp (SGb 5) (SB 0)) s0 s1 (18 * b + 3) := by
    have ex : s0.val (SGb 5) = b := eb
    have w := wc cap (SGb 5) (SB 0) s0 (by decide) (by decide) (by decide) (hzs _ (by decide) (by decide)) (hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (cp (SGb 4) (SB 1)) s1 s2 (18 * s + 3) := by
    have ex : s1.val (SGb 4) = s := by rw [hs1, vsv, if_neg (show ¬ ((SGb 4) = (SB 0)) by decide), es]
    have w := wc cap (SGb 4) (SB 1) s1 (by decide) (by decide) (by decide) (by rw [hs1, vsv, if_neg (show ¬ ((SB 1) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs1, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs2]; exact w
  have h3 : WExec cap (UnaryArith.subW SB) s2 s3 (30 * s + 10) := by
    have e0 : s2.val (SB 0) = b := by rw [hs2, vsv, if_neg (show ¬ ((SB 0) = (SB 1)) by decide), hs1, vsv, if_pos rfl]
    have e1 : s2.val (SB 1) = s := by rw [hs2, vsv, if_pos rfl]
    have w := UnaryArith.subW_spec cap SB s2 (by rw [hs2, vsv, if_neg (show ¬ ((SB 2) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((SB 2) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs2, vsv, if_neg (show ¬ ((SB 3) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((SB 3) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs3]; exact w
  have h4 : WExec cap (cp (SB 0) (MD 0)) s3 s4 (18 * (b - s) + 3) := by
    have ex : s3.val (SB 0) = (b - s) := by rw [hs3, vsv, if_pos rfl]
    have w := wc cap (SB 0) (MD 0) s3 (by decide) (by decide) (by decide) (by rw [hs3, vsv, if_neg (show ¬ ((MD 0) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MD 0) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MD 0) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs3, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs4]; exact w
  have h5 : WExec cap (cp (SGb 6) (MD 1)) s4 s5 (18 * r2 + 3) := by
    have ex : s4.val (SGb 6) = r2 := by rw [hs4, vsv, if_neg (show ¬ ((SGb 6) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((SGb 6) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((SGb 6) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((SGb 6) = (SB 0)) by decide), er2]
    have w := wc cap (SGb 6) (MD 1) s4 (by decide) (by decide) (by decide) (by rw [hs4, vsv, if_neg (show ¬ ((MD 1) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MD 1) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MD 1) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MD 1) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs4, vsv, if_neg (show ¬ (rT0 = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs5]; exact w
  have h6 : WExec cap (SparseNum.mulByW MD) s5 s6 (3 * UnaryPow.sq cap) := by
    have e0 : s5.val (MD 0) = (b - s) := by rw [hs5, vsv, if_neg (show ¬ ((MD 0) = (MD 1)) by decide), hs4, vsv, if_pos rfl]
    have e1 : s5.val (MD 1) = r2 := by rw [hs5, vsv, if_pos rfl]
    have w := SparseNum.mulByW_spec cap MD s5 (by rw [hs5, vsv, if_neg (show ¬ ((MD 2) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((MD 2) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MD 2) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MD 2) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MD 2) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs5, vsv, if_neg (show ¬ ((MD 3) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((MD 3) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MD 3) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MD 3) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MD 3) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs5, vsv, if_neg (show ¬ ((MD 4) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((MD 4) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MD 4) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MD 4) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MD 4) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [e0, e1]; omega) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs6]; exact w
  have h7 : WExec cap (cp (SGb 3) (MR 0)) s6 s7 (18 * r + 3) := by
    have ex : s6.val (SGb 3) = r := by rw [hs6, vsv, if_neg (show ¬ ((SGb 3) = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ ((SGb 3) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((SGb 3) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((SGb 3) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((SGb 3) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((SGb 3) = (SB 0)) by decide), er]
    have w := wc cap (SGb 3) (MR 0) s6 (by decide) (by decide) (by decide) (by rw [hs6, vsv, if_neg (show ¬ ((MR 0) = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ ((MR 0) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((MR 0) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MR 0) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MR 0) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MR 0) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs6, vsv, if_neg (show ¬ (rT0 = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs7]; exact w
  have h8 : WExec cap (cp (SGb 5) (MR 1)) s7 s8 (18 * b + 3) := by
    have ex : s7.val (SGb 5) = b := by rw [hs7, vsv, if_neg (show ¬ ((SGb 5) = (MR 0)) by decide), hs6, vsv, if_neg (show ¬ ((SGb 5) = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ ((SGb 5) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((SGb 5) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((SGb 5) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((SGb 5) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((SGb 5) = (SB 0)) by decide), eb]
    have w := wc cap (SGb 5) (MR 1) s7 (by decide) (by decide) (by decide) (by rw [hs7, vsv, if_neg (show ¬ ((MR 1) = (MR 0)) by decide), hs6, vsv, if_neg (show ¬ ((MR 1) = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ ((MR 1) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((MR 1) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MR 1) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MR 1) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MR 1) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs7, vsv, if_neg (show ¬ (rT0 = (MR 0)) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs8]; exact w
  have h9 : WExec cap (SparseNum.mulByW MR) s8 s9 (3 * UnaryPow.sq cap) := by
    have e0 : s8.val (MR 0) = r := by rw [hs8, vsv, if_neg (show ¬ ((MR 0) = (MR 1)) by decide), hs7, vsv, if_pos rfl]
    have e1 : s8.val (MR 1) = b := by rw [hs8, vsv, if_pos rfl]
    have w := SparseNum.mulByW_spec cap MR s8 (by rw [hs8, vsv, if_neg (show ¬ ((MR 2) = (MR 1)) by decide), hs7, vsv, if_neg (show ¬ ((MR 2) = (MR 0)) by decide), hs6, vsv, if_neg (show ¬ ((MR 2) = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ ((MR 2) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((MR 2) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MR 2) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MR 2) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MR 2) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs8, vsv, if_neg (show ¬ ((MR 3) = (MR 1)) by decide), hs7, vsv, if_neg (show ¬ ((MR 3) = (MR 0)) by decide), hs6, vsv, if_neg (show ¬ ((MR 3) = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ ((MR 3) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((MR 3) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MR 3) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MR 3) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MR 3) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs8, vsv, if_neg (show ¬ ((MR 4) = (MR 1)) by decide), hs7, vsv, if_neg (show ¬ ((MR 4) = (MR 0)) by decide), hs6, vsv, if_neg (show ¬ ((MR 4) = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ ((MR 4) = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ ((MR 4) = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ ((MR 4) = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ ((MR 4) = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ ((MR 4) = (SB 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [e0, e1]; omega) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs9]; exact w
  have f0 : s9.val (MD 0) = ((b - s) * r2) := by rw [hs9, vsv, if_neg (show ¬ ((MD 0) = (MR 0)) by decide), hs8, vsv, if_neg (show ¬ ((MD 0) = (MR 1)) by decide), hs7, vsv, if_neg (show ¬ ((MD 0) = (MR 0)) by decide), hs6, vsv, if_pos rfl]
  have f1 : s9.val (MR 0) = (r * b) := by rw [hs9, vsv, if_pos rfl]
  have fT : s9.val rT0 = 0 := by rw [hs9, vsv, if_neg (show ¬ (rT0 = (MR 0)) by decide), hs8, vsv, if_neg (show ¬ (rT0 = (MR 1)) by decide), hs7, vsv, if_neg (show ¬ (rT0 = (MR 0)) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (MD 0)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = (MD 1)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (MD 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (SB 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (SB 0)) by decide)]; exact hT
  refine ⟨s9, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 (WExec.seq h6 (WExec.seq h7 (WExec.seq h8 (h9)))))))), ?_, f0, f1, fT, fun q hq hqT => ?_, ?_, ?_, ?_⟩
  · have e2 : ∀ x y z : ℕ, 18 * (x * y * z) = 18 * x * y * z := fun x y z => by ring
    have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, (106 ≤ r'.val ∧ r'.val < 120) → q ≠ r' := fun r' h e => by subst e; omega
    rw [hs9, vsv, if_neg (nq (MR 0) (by decide)), hs8, vsv, if_neg (nq (MR 1) (by decide)), hs7, vsv, if_neg (nq (MR 0) (by decide)), hs6, vsv, if_neg (nq (MD 0) (by decide)), hs5, vsv, if_neg (nq (MD 1) (by decide)), hs4, vsv, if_neg (nq (MD 0) (by decide)), hs3, vsv, if_neg (nq (SB 0) (by decide)), hs2, vsv, if_neg (nq (SB 1) (by decide)), hs1, vsv, if_neg (nq (SB 0) (by decide))]
  · simp only [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- Segment F of the seed's numbers. -/
def segF : WM (LNS 0) LNR := (.seq (cp dN (ST 0)) (.seq (cp (MR 0) (ST 1)) (.seq (UnaryArith.subW ST) (.seq (.inc (ST 0)) (.seq (WriteNat.halveM (ST 0) rDr rRb) (.seq (addTo (MD 0) (ST 0) rT0) (.seq (addTo (ST 0) rD2 rT0) (addTo (ST 0) rD2 rT0))))))))

theorem segF_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh gs fs pi b s r2 r n : ℕ) (en : s0.val dN = n) (eMR : s0.val (MR 0) = (r * b)) (eMD : s0.val (MD 0) = ((b - s) * r2))
    (hzs : ∀ q : Fin LNR, 120 ≤ q.val → q.val < 127 → s0.val q = 0) (hT : s0.val rT0 = 0)
    (hc : SeedCap cap Q kh gs fs pi b s r2 r n) :
    ∃ τ c, WExec cap segF s0 τ c ∧ c ≤ 60 * UnaryPow.sq cap ∧ τ.val (ST 0) = ((n - r * b + 1) / 2 + (b - s) * r2) ∧ τ.val rD2 = (0 + ((n - r * b + 1) / 2 + (b - s) * r2) + ((n - r * b + 1) / 2 + (b - s) * r2)) ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, (q.val < 120 ∨ 127 ≤ q.val) → q ≠ rT0 → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  obtain ⟨cQ, ckh, cg, cgp, cgs, cfs, cpi, cw, cc, cb, cs, cr2, cr, cn, cbs, crb, cn1, cd⟩ := hc
  simp only [wOf] at *
  have hsq := UnaryPow.sq_ge cap
  have hlin := UnaryPow.lin_le_sq cap
  have hlQ : Nat.clog 2 Q ≤ Q := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hW : (1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 < 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := Nat.lt_two_pow_self
  have hp2 : 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8 + 1) = 2 * 2 ^ ((1 + max (kh + kh) (Nat.clog 2 Q) + kh) * 8) := by rw [pow_succ]; ring
  have cmx : max (kh + kh) (Nat.clog 2 Q) ≤ cap := max_le (by omega) (by omega)
  obtain ⟨s1, hs1⟩ : ∃ z : WState (LNS 0) LNR, z = (s0).setv (ST 0) n := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ z : WState (LNS 0) LNR, z = (s1).setv (ST 1) (r * b) := ⟨_, rfl⟩
  obtain ⟨s3, hs3⟩ : ∃ z : WState (LNS 0) LNR, z = (s2).setv (ST 0) (n - r * b) := ⟨_, rfl⟩
  obtain ⟨s4, hs4⟩ : ∃ z : WState (LNS 0) LNR, z = (s3).setv (ST 0) (n - r * b + 1) := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ z : WState (LNS 0) LNR, z = ((s4).setv (ST 0) ((n - r * b + 1) / 2)).setv rRb ((n - r * b + 1) % 2) := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ z : WState (LNS 0) LNR, z = (s5).setv (ST 0) (((n - r * b + 1) / 2 + (b - s) * r2)) := ⟨_, rfl⟩
  obtain ⟨s7, hs7⟩ : ∃ z : WState (LNS 0) LNR, z = (s6).setv rD2 (0 + ((n - r * b + 1) / 2 + (b - s) * r2)) := ⟨_, rfl⟩
  obtain ⟨s8, hs8⟩ : ∃ z : WState (LNS 0) LNR, z = (s7).setv rD2 (0 + ((n - r * b + 1) / 2 + (b - s) * r2) + ((n - r * b + 1) / 2 + (b - s) * r2)) := ⟨_, rfl⟩
  have h1 : WExec cap (cp dN (ST 0)) s0 s1 (18 * n + 3) := by
    have ex : s0.val dN = n := en
    have w := wc cap dN (ST 0) s0 (by decide) (by decide) (by decide) (hzs _ (by decide) (by decide)) (hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs1]; exact w
  have h2 : WExec cap (cp (MR 0) (ST 1)) s1 s2 (18 * (r * b) + 3) := by
    have ex : s1.val (MR 0) = (r * b) := by rw [hs1, vsv, if_neg (show ¬ ((MR 0) = (ST 0)) by decide), eMR]
    have w := wc cap (MR 0) (ST 1) s1 (by decide) (by decide) (by decide) (by rw [hs1, vsv, if_neg (show ¬ ((ST 1) = (ST 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs1, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide)]; exact hT) (by rw [ex]; omega)
    rw [ex] at w; rw [hs2]; exact w
  have h3 : WExec cap (UnaryArith.subW ST) s2 s3 (30 * (r * b) + 10) := by
    have e0 : s2.val (ST 0) = n := by rw [hs2, vsv, if_neg (show ¬ ((ST 0) = (ST 1)) by decide), hs1, vsv, if_pos rfl]
    have e1 : s2.val (ST 1) = (r * b) := by rw [hs2, vsv, if_pos rfl]
    have w := UnaryArith.subW_spec cap ST s2 (by rw [hs2, vsv, if_neg (show ¬ ((ST 2) = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ ((ST 2) = (ST 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs2, vsv, if_neg (show ¬ ((ST 3) = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ ((ST 3) = (ST 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [e0]; omega) (by rw [e1]; omega)
    rw [e0, e1] at w; rw [hs3]; exact w
  have h4 : WExec cap (.inc (ST 0)) s3 s4 3 := by
    have ex : s3.val (ST 0) = (n - r * b) := by rw [hs3, vsv, if_pos rfl]
    have w := WExec.inc (cap := cap) (ST 0) s3 (by rw [ex]; omega)
    rw [ex] at w; rw [hs4]; exact w
  have h5 : WExec cap (WriteNat.halveM (ST 0) rDr rRb) s4 s5 (9 * (n - r * b + 1) + 6) := by
    have ex : s4.val (ST 0) = n - r * b + 1 := by rw [hs4, vsv, if_pos rfl]
    have w := WriteNat.halveM_spec cap (ST 0) rDr rRb (by decide) (by decide) (by decide) s4 (by rw [hs4, vsv, if_neg (show ¬ (rDr = (ST 0)) by decide), hs3, vsv, if_neg (show ¬ (rDr = (ST 0)) by decide), hs2, vsv, if_neg (show ¬ (rDr = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ (rDr = (ST 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [hs4, vsv, if_neg (show ¬ (rRb = (ST 0)) by decide), hs3, vsv, if_neg (show ¬ (rRb = (ST 0)) by decide), hs2, vsv, if_neg (show ¬ (rRb = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ (rRb = (ST 0)) by decide)]; exact hzs _ (by decide) (by decide)) (by rw [ex]; omega) (by omega)
    rw [ex] at w; rw [hs5]; exact w
  have h6 : WExec cap (addTo (MD 0) (ST 0) rT0) s5 s6 (18 * ((b - s) * r2) + 3) := by
    have ep : s5.val (MD 0) = ((b - s) * r2) := by rw [hs5, vsv, if_neg (show ¬ ((MD 0) = rRb) by decide), vsv, if_neg (show ¬ ((MD 0) = (ST 0)) by decide), hs4, vsv, if_neg (show ¬ ((MD 0) = (ST 0)) by decide), hs3, vsv, if_neg (show ¬ ((MD 0) = (ST 0)) by decide), hs2, vsv, if_neg (show ¬ ((MD 0) = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ ((MD 0) = (ST 0)) by decide), eMD]
    have ev : s5.val (ST 0) = ((n - r * b + 1) / 2) := by rw [hs5, vsv, if_neg (show ¬ ((ST 0) = rRb) by decide), vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (MD 0) (ST 0) rT0 (by decide) (by decide) (by decide) s5 (by rw [hs5, vsv, if_neg (show ¬ (rT0 = rRb) by decide), vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs6]; exact w
  have h7 : WExec cap (addTo (ST 0) rD2 rT0) s6 s7 (18 * ((n - r * b + 1) / 2 + (b - s) * r2) + 3) := by
    have ep : s6.val (ST 0) = ((n - r * b + 1) / 2 + (b - s) * r2) := by rw [hs6, vsv, if_pos rfl]
    have ev : s6.val rD2 = 0 := by rw [hs6, vsv, if_neg (show ¬ (rD2 = (ST 0)) by decide), hs5, vsv, if_neg (show ¬ (rD2 = rRb) by decide), vsv, if_neg (show ¬ (rD2 = (ST 0)) by decide), hs4, vsv, if_neg (show ¬ (rD2 = (ST 0)) by decide), hs3, vsv, if_neg (show ¬ (rD2 = (ST 0)) by decide), hs2, vsv, if_neg (show ¬ (rD2 = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ (rD2 = (ST 0)) by decide)]; exact hzs _ (by decide) (by decide)
    have w := ParseNat.addTo_spec cap (ST 0) rD2 rT0 (by decide) (by decide) (by decide) s6 (by rw [hs6, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = rRb) by decide), vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs7]; exact w
  have h8 : WExec cap (addTo (ST 0) rD2 rT0) s7 s8 (18 * ((n - r * b + 1) / 2 + (b - s) * r2) + 3) := by
    have ep : s7.val (ST 0) = ((n - r * b + 1) / 2 + (b - s) * r2) := by rw [hs7, vsv, if_neg (show ¬ ((ST 0) = rD2) by decide), hs6, vsv, if_pos rfl]
    have ev : s7.val rD2 = (0 + ((n - r * b + 1) / 2 + (b - s) * r2)) := by rw [hs7, vsv, if_pos rfl]
    have w := ParseNat.addTo_spec cap (ST 0) rD2 rT0 (by decide) (by decide) (by decide) s7 (by rw [hs7, vsv, if_neg (show ¬ (rT0 = rD2) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = rRb) by decide), vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide)]; exact hT) (by rw [ep]; omega) (by rw [ep, ev]; omega)
    rw [ep, ev] at w; rw [hs8]; exact w
  have f0 : s8.val (ST 0) = ((n - r * b + 1) / 2 + (b - s) * r2) := by rw [hs8, vsv, if_neg (show ¬ ((ST 0) = rD2) by decide), hs7, vsv, if_neg (show ¬ ((ST 0) = rD2) by decide), hs6, vsv, if_pos rfl]
  have f1 : s8.val rD2 = (0 + ((n - r * b + 1) / 2 + (b - s) * r2) + ((n - r * b + 1) / 2 + (b - s) * r2)) := by rw [hs8, vsv, if_pos rfl]
  have fT : s8.val rT0 = 0 := by rw [hs8, vsv, if_neg (show ¬ (rT0 = rD2) by decide), hs7, vsv, if_neg (show ¬ (rT0 = rD2) by decide), hs6, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs5, vsv, if_neg (show ¬ (rT0 = rRb) by decide), vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs4, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs3, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide), hs2, vsv, if_neg (show ¬ (rT0 = (ST 1)) by decide), hs1, vsv, if_neg (show ¬ (rT0 = (ST 0)) by decide)]; exact hT
  refine ⟨s8, _, WExec.seq h1 (WExec.seq h2 (WExec.seq h3 (WExec.seq h4 (WExec.seq h5 (WExec.seq h6 (WExec.seq h7 (h8))))))), ?_, f0, f1, fT, fun q hq hqT => ?_, ?_, ?_, ?_⟩
  · have e2 : ∀ x y z : ℕ, 18 * (x * y * z) = 18 * x * y * z := fun x y z => by ring
    have e3 : ∀ x y : ℕ, 18 * (x * y) = 18 * x * y := fun x y => by ring
    omega
  · have nq : ∀ r' : Fin LNR, (120 ≤ r'.val ∧ r'.val < 127) → q ≠ r' := fun r' h e => by subst e; omega
    rw [hs8, vsv, if_neg (nq rD2 (by decide)), hs7, vsv, if_neg (nq rD2 (by decide)), hs6, vsv, if_neg (nq (ST 0) (by decide)), hs5, vsv, if_neg (nq rRb (by decide)), vsv, if_neg (nq (ST 0) (by decide)), hs4, vsv, if_neg (nq (ST 0) (by decide)), hs3, vsv, if_neg (nq (ST 0) (by decide)), hs2, vsv, if_neg (nq (ST 1) (by decide)), hs1, vsv, if_neg (nq (ST 0) (by decide))]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]
  · simp only [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, WState.setv]

/-- **The seed's numbers** (the six segments). -/
def seedW : WM (LNS 0) LNR := .seq segA (.seq segB (.seq segC (.seq segD (.seq segE segF))))

/-- **The seed's numbers, run**: `ℓ' = max(2kh, ⌈log₂ Q⌉)` in `X 2`, `n_T` in `N 0`, `w` in `WB 0`, `2^w` in `P 1`,
`n_T·2^w` in `CC 0`, `dRow` in `ST 0`, `2·dRow` in `rD2`; every register outside `64 … 126` and the streams
unchanged. -/
theorem seed_spec (cap : ℕ) (s0 : WState (LNS 0) LNR) (Q kh gs fs pi b s r2 r n : ℕ)
    (eQ : s0.val (KB 52) = Q) (ekh : s0.val (SGb 8) = kh) (e21 : s0.val (G 21) = gs) (e41 : s0.val (G 41) = fs)
    (e52 : s0.val (G 52) = pi) (eb : s0.val (SGb 5) = b) (es : s0.val (SGb 4) = s) (er2 : s0.val (SGb 6) = r2)
    (er : s0.val (SGb 3) = r) (en : s0.val dN = n)
    (hz : ∀ q : Fin LNR, 64 ≤ q.val → q.val < 250 → s0.val q = 0) (hc : SeedCap cap Q kh gs fs pi b s r2 r n) :
    ∃ τ c, WExec cap seedW s0 τ c ∧ c ≤ 400 * UnaryPow.sq cap ∧
      τ.val (X 2) = max (kh + kh) (Nat.clog 2 Q) ∧ τ.val (N 0) = gs * fs * pi ∧ τ.val (WB 0) = wOf kh Q ∧
      τ.val (P 1) = 2 ^ wOf kh Q ∧ τ.val (CC 0) = gs * fs * pi * 2 ^ wOf kh Q ∧
      τ.val (ST 0) = (n - r * b + 1) / 2 + (b - s) * r2 ∧
      τ.val rD2 = 0 + ((n - r * b + 1) / 2 + (b - s) * r2) + ((n - r * b + 1) / 2 + (b - s) * r2) ∧
      τ.val (X 0) = kh + kh ∧ τ.val rT0 = 0 ∧
      (∀ q : Fin LNR, (q.val < 64 ∨ 127 ≤ q.val) → τ.val q = s0.val q) ∧
      τ.st = s0.st ∧ τ.sh = s0.sh ∧ τ.cell = s0.cell := by
  have nT : ∀ q : Fin LNR, q.val ≠ 100 → q ≠ rT0 := fun q h e => by subst e; exact h rfl
  have hsq := UnaryPow.sq_ge cap
  have hT0 : s0.val rT0 = 0 := hz rT0 (by decide) (by decide)
  obtain ⟨τA, cA, hA, cAle, fA0, fA1, tA, frA, stA, shA, clA⟩ := segA_spec cap s0 Q kh gs fs pi b s r2 r n eQ ekh
    (fun q h1 h2 => hz q h1 (by omega)) hT0 hc
  have kA : ∀ q : Fin LNR, (q.val < 64 ∨ 84 ≤ q.val) → q.val ≠ 100 → τA.val q = s0.val q :=
    fun q h h' => frA q h (nT q h')
  obtain ⟨τB, cB, hB, cBle, fB0, tB, frB, stB, shB, clB⟩ := segB_spec cap τA Q kh gs fs pi b s r2 r n
    (by rw [kA _ (by right; decide) (by decide)]; exact e21) (by rw [kA _ (by right; decide) (by decide)]; exact e41)
    (by rw [kA _ (by right; decide) (by decide)]; exact e52)
    (fun q h1 h2 => by rw [kA q (by omega) (by omega)]; exact hz q (by omega) (by omega)) tA hc
  have kB : ∀ q : Fin LNR, (q.val < 84 ∨ 89 ≤ q.val) → q.val ≠ 100 → τB.val q = τA.val q :=
    fun q h h' => frB q h (nT q h')
  obtain ⟨τC, cC, hC, cCle, fC0, tC, frC, stC, shC, clC⟩ := segC_spec cap τB Q kh gs fs pi b s r2 r n
    (by rw [kB _ (by left; decide) (by decide)]; exact fA0)
    (by rw [kB _ (by right; decide) (by decide), kA _ (by right; decide) (by decide)]; exact ekh)
    (fun q h1 h2 => by rw [kB q (by omega) (by omega), kA q (by omega) (by omega)]; exact hz q (by omega) (by omega))
    tB hc
  have kC : ∀ q : Fin LNR, (q.val < 89 ∨ 94 ≤ q.val) → q.val ≠ 100 → τC.val q = τB.val q :=
    fun q h h' => frC q h (nT q h')
  obtain ⟨τD, cD, hD, cDle, fD0, fD1, tD, frD, stD, shD, clD⟩ := segD_spec cap τC Q kh gs fs pi b s r2 r n
    (by exact fC0)
    (by rw [kC _ (by left; decide) (by decide)]; exact fB0)
    (fun q h1 h2 => by
      by_cases h100 : q.val = 100
      · have e : q = rT0 := Fin.ext h100
        rw [e]; exact tC
      · rw [kC q (by omega) h100, kB q (by omega) h100, kA q (by omega) h100]; exact hz q (by omega) (by omega))
    tC hc
  have kD : ∀ q : Fin LNR, (q.val < 94 ∨ 106 ≤ q.val) → q.val ≠ 100 → τD.val q = τC.val q :=
    fun q h h' => frD q h (nT q h')
  have k3 : ∀ q : Fin LNR, 106 ≤ q.val → q.val < 250 → τD.val q = 0 := fun q h1 h2 => by
    rw [kD q (by omega) (by omega), kC q (by omega) (by omega), kB q (by omega) (by omega), kA q (by omega) (by omega)]
    exact hz q (by omega) (by omega)
  have kUp : ∀ q : Fin LNR, 250 ≤ q.val → τD.val q = s0.val q := fun q h => by
    rw [kD q (by omega) (by omega), kC q (by omega) (by omega), kB q (by omega) (by omega), kA q (by omega) (by omega)]
  obtain ⟨τE, cE, hE, cEle, fE0, fE1, tE, frE, stE, shE, clE⟩ := segE_spec cap τD Q kh gs fs pi b s r2 r n
    (by rw [kUp _ (by decide)]; exact eb) (by rw [kUp _ (by decide)]; exact es) (by rw [kUp _ (by decide)]; exact er2)
    (by rw [kUp _ (by decide)]; exact er) (fun q h1 h2 => k3 q (by omega) (by omega)) tD hc
  have kE : ∀ q : Fin LNR, (q.val < 106 ∨ 120 ≤ q.val) → q.val ≠ 100 → τE.val q = τD.val q :=
    fun q h h' => frE q h (nT q h')
  obtain ⟨τF, cF, hF, cFle, fF0, fF1, tF, frF, stF, shF, clF⟩ := segF_spec cap τE Q kh gs fs pi b s r2 r n
    (by rw [kE _ (by right; decide) (by decide), kUp _ (by decide)]; exact en)
    (by exact fE1) (by exact fE0)
    (fun q h1 h2 => by rw [kE q (by omega) (by omega)]; exact k3 q (by omega) (by omega)) tE hc
  have kF : ∀ q : Fin LNR, (q.val < 120 ∨ 127 ≤ q.val) → q.val ≠ 100 → τF.val q = τE.val q :=
    fun q h h' => frF q h (nT q h')
  refine ⟨τF, _, WExec.seq hA (WExec.seq hB (WExec.seq hC (WExec.seq hD (WExec.seq hE hF)))), by omega, ?_, ?_, ?_,
    ?_, ?_, fF0, fF1, ?_, tF, fun q hq => ?_, ?_, ?_, ?_⟩
  · rw [kF _ (by left; decide) (by decide), kE _ (by left; decide) (by decide), kD _ (by left; decide) (by decide),
      kC _ (by left; decide) (by decide), kB _ (by left; decide) (by decide)]; exact fA0
  · rw [kF _ (by left; decide) (by decide), kE _ (by left; decide) (by decide), kD _ (by left; decide) (by decide),
      kC _ (by left; decide) (by decide)]; exact fB0
  · rw [kF _ (by left; decide) (by decide), kE _ (by left; decide) (by decide), kD _ (by left; decide) (by decide)]
    exact fC0
  · rw [kF _ (by left; decide) (by decide), kE _ (by left; decide) (by decide)]; exact fD0
  · rw [kF _ (by left; decide) (by decide), kE _ (by left; decide) (by decide)]; exact fD1
  · rw [kF _ (by left; decide) (by decide), kE _ (by left; decide) (by decide), kD _ (by left; decide) (by decide),
      kC _ (by left; decide) (by decide), kB _ (by left; decide) (by decide)]; exact fA1
  · have h100 : q.val ≠ 100 := by omega
    rw [kF q (by omega) h100, kE q (by omega) h100, kD q (by omega) h100, kC q (by omega) h100, kB q (by omega) h100,
      kA q (by omega) h100]
  · rw [stF, stE, stD, stC, stB, stA]
  · rw [shF, shE, shD, shC, shB, shA]
  · rw [clF, clE, clD, clC, clB, clA]

end NearCubicWires.WireExponent3_5.PrimT.C4Set
