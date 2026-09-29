import Proof.Wire_3_5.UnionMachine.FrontTWBridge5
import Proof.Wire_3_5.UnionMachine.FrontOps
import Proof.Wire_3_5.Primitive.Writers.SparseNum

/-! # C6 front, U5: the union machine's numbers (P3:3395-3403, 3485-3491, 3823-3824)

Before the table, the machine computes, in the table writer's registers: the arity `q` of the calls, the PCPP
output's systematic, auxiliary and clause-bit counts, the rounding precision `p = ⌈log₂(q+2)⌉` (`unionBits`), the
grid mass `Λ̄` and the grid size `s = C_δ Λ̄²` (PA's `sparseM`), the entry count, the supports' bit count `sys·q`,
the clause count `2^{cb}` and the six magnitudes (**`numT`**, `numV_out`). After the table, in the table writer's
cleared digit registers, it computes the thresholds of `tr:thresholds` with the rounding slack, the
accumulators' start (**`thrOps`**, `accStart_eq`). Everything stays inside the table writer's 56 registers.
Paper quantity: `Λ̄`, `s`, the magnitudes `|κ|·∏ m_k`, the thresholds. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontOps

/-! ## The magnitudes -/

/-- The magnitudes `s⁴, Λ̄²s², 2Λ̄s³, 2Λ̄³s, Λ̄⁴, Λ̄s³` from `s` (`SS`) and `Λ̄` (`LAM`); temporaries `24–30`. -/
def magOps : List (ROp NR) :=
  [.copy rSS 24 29, .mulAdd ⟨![24, rSS, 25, 29, 30], by decide⟩, .clear 24,
   .copy rLAM 24 29, .mulAdd ⟨![24, rLAM, 26, 29, 30], by decide⟩, .clear 24,
   .mulAdd ⟨![25, rSS, 27, 29, 30], by decide⟩, .mulAdd ⟨![27, rSS, rMa, 29, 30], by decide⟩,
   .mulAdd ⟨![26, 25, rMb, 29, 30], by decide⟩, .mulAdd ⟨![rLAM, 27, rMf, 29, 30], by decide⟩,
   .mulAdd ⟨![rLAM, 27, rMc, 29, 30], by decide⟩, .mulAdd ⟨![rLAM, 27, rMc, 29, 30], by decide⟩,
   .mulAdd ⟨![26, rLAM, 28, 29, 30], by decide⟩, .mulAdd ⟨![28, rSS, rMd, 29, 30], by decide⟩,
   .mulAdd ⟨![28, rSS, rMd, 29, 30], by decide⟩, .mulAdd ⟨![28, rLAM, rMe, 29, 30], by decide⟩,
   .clear 25, .clear 26, .clear 27, .clear 28]

/-! ## The registers -/

abbrev rLL : Fin NR := 52
abbrev rEE : Fin NR := 53
abbrev rQQ : Fin NR := 54
/-- A temporary for `aux`, cleared by the arithmetic. -/
abbrev rAUX : Fin NR := 55
/-- A temporary for `cb` (the table writer's `Z`), cleared by the arithmetic. -/
abbrev rCB : Fin NR := 36
/-- A temporary for the PCPP output's field count (the table writer's `FL`), cleared at once. -/
abbrev rK1 : Fin NR := 37
/-- The accumulators `V⁻ V⁺ Q⁻ Q⁺ μ⁻ μ⁺`, after the table (the table writer's digit registers). -/
abbrev rV0 : Fin NR := 24
abbrev rV1 : Fin NR := 25
abbrev rQ0 : Fin NR := 26
abbrev rQ1 : Fin NR := 27
abbrev rU0 : Fin NR := 28
abbrev rU1 : Fin NR := 29

variable (cap : ℕ)

/-! ## Before the table: the counts and the magnitudes -/

/-- The counts: `sys·q` (`SQ`), `M = 2^{cb}` (`MM`), `E = sys·s + aux·s` (`EE`). -/
def preOps : List (ROp NR) :=
  [.mulAdd ⟨![rSYS, rQQ, rSQ, 34, 35], by decide⟩, .pow2 ⟨![rCB, rMM, 34, 35], by decide⟩,
   .mulAdd ⟨![rSYS, rSS, rEE, 34, 35], by decide⟩, .mulAdd ⟨![rAUX, rSS, rEE, 34, 35], by decide⟩]

/-- The counts, the magnitudes, the temporaries cleared, then the admissibility register `OK := 1`. -/
def numOps : List (ROp NR) := preOps ++ magOps ++ [.clear rCB, .clear rAUX, .addC rOK 1]

/-- The registers holding inputs of the arithmetic. -/
def numIn : List (Fin NR) := [rBIG, rCDF, rSS, rLAM, rLL, rQQ, rSYS, rAUX, rCB]

/-- Every value the arithmetic holds fits the capacity. -/
def numCap (s Λ q sys aux cb : ℕ) : ℕ :=
  s + q + sys + aux + cb + Λ + 2 + sys * q + 2 ^ (cb + 1) + sys * s + aux * s + s * s + s * s * s +
    s * s * s * s + Λ * Λ + Λ * Λ * Λ + Λ * Λ * Λ * Λ + Λ * Λ * (s * s) + 2 * (Λ * (s * s * s)) +
    2 * (Λ * Λ * Λ * s)

theorem numOps_pre (u : Fin NR → ℕ) (s Λ p q sys aux cb : ℕ) (hs : u rSS = s) (hl : u rLAM = Λ)
    (_hp : u rLL = p) (hq : u rQQ = q) (hy : u rSYS = sys) (ha : u rAUX = aux) (hb : u rCB = cb)
    (hz : ∀ r, r ∉ numIn → u r = 0) (hc : numCap s Λ q sys aux cb ≤ cap) : preL cap numOps u := by
  unfold numCap at hc
  have e2 : 2 ^ (cb + 1) = 2 * 2 ^ cb := by rw [pow_succ]; ring
  simp +decide [numOps, preOps, magOps, preL, Function.update_apply, hs, hl, hq, hy, ha, hb, hz, numIn]
  and_intros
  all_goals omega

/-- The registers the arithmetic keeps (inputs and results); every other register ends at `0`. -/
def numKeep : List (Fin NR) := [rBIG, rCDF, rSS, rLAM, rLL, rQQ, rSYS, rSQ, rMM, rEE, rMa, rMb, rMc, rMd, rMe, rMf, rOK]

theorem numOps_val (u : Fin NR → ℕ) (s Λ p q sys aux cb : ℕ) (hs : u rSS = s) (hl : u rLAM = Λ)
    (_hp : u rLL = p) (hq : u rQQ = q) (hy : u rSYS = sys) (ha : u rAUX = aux) (hb : u rCB = cb)
    (hz : ∀ r, r ∉ numIn → u r = 0) :
    evalL numOps u rSQ = sys * q ∧ evalL numOps u rMM = 2 ^ cb ∧ evalL numOps u rEE = sys * s + aux * s ∧
    evalL numOps u rMa = s * s * s * s ∧ evalL numOps u rMb = Λ * Λ * (s * s) ∧
    evalL numOps u rMc = Λ * (s * s * s) + Λ * (s * s * s) ∧ evalL numOps u rMd = Λ * Λ * Λ * s + Λ * Λ * Λ * s ∧
    evalL numOps u rMe = Λ * Λ * Λ * Λ ∧ evalL numOps u rMf = Λ * (s * s * s) ∧ evalL numOps u rOK = 1 ∧
    evalL numOps u 24 = 0 ∧ evalL numOps u 25 = 0 ∧ evalL numOps u 26 = 0 ∧ evalL numOps u 27 = 0 ∧
    evalL numOps u 28 = 0 ∧ evalL numOps u rCB = 0 ∧ evalL numOps u rAUX = 0 := by
  simp +decide [numOps, preOps, magOps, evalL, Function.update_apply, hs, hl, hq, hy, ha, hb, hz, numIn]

/-- Every register outside the kept ones ends at `0`. -/
theorem numOps_zero (u : Fin NR → ℕ) (s Λ p q sys aux cb : ℕ) (hs : u rSS = s) (hl : u rLAM = Λ)
    (hp : u rLL = p) (hq : u rQQ = q) (hy : u rSYS = sys) (ha : u rAUX = aux) (hb : u rCB = cb)
    (hz : ∀ r, r ∉ numIn → u r = 0) (r : Fin NR) (hr : r ∉ numKeep) : evalL numOps u r = 0 := by
  have hv := numOps_val u s Λ p q sys aux cb hs hl hp hq hy ha hb hz
  by_cases hw : r ∈ numOps.flatMap writes
  · simp only [numOps, preOps, magOps, List.cons_append, List.nil_append, List.flatMap_cons, writes,
      List.flatMap_nil, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    simp only [Function.Embedding.coeFn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons] at hw
    rcases hw with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h
    all_goals first
      | (subst h; exfalso; apply hr; simp +decide [numKeep]; done)
      | (subst h; simp +decide [hv]; done)
  · rw [evalL_frame _ u r hw]
    refine hz r (fun hm => ?_)
    simp only [numIn, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp +decide [numKeep, numOps, preOps, magOps, writes] at hr hw

/-! ## After the table: the thresholds with the rounding slack -/

/-- `K' = s⁴2^pM` (from `S4 = s⁴`, `M = 2^{cb}`). -/
def kOf (S4 p M : ℕ) : ℕ := S4 * 2 ^ p * M

/-- `X = s⁴M(1+Λ̄)⁴`. -/
def xOf (S4 Λ M : ℕ) : ℕ := S4 * M * ((Λ + 1) * (Λ + 1) * ((Λ + 1) * (Λ + 1)))

/-- `A = ⌈K'aT/bT⌉`. -/
def aOf (S4 p M aT bT : ℕ) : ℕ := (kOf S4 p M * aT + (bT - 1)) / bT

/-- The thresholds, after the table, from `s⁴` (`Ma`), `p` (`LL`), `M` (`MM`), `Λ̄` (`LAM`), at `v₀ = aV/bV`,
`τ = aT/bT`: `V⁺ = ⌊4K'aV/bV⌋ + 2X`, `Q⁺ = 2K' + 2X + ⌊2K'aV/bV⌋`, `μ⁻ = X ∸ A`, `μ⁺ = A ∸ X` into the table writer's
cleared digit registers `24–29`; temporaries `13–20`, `30–40`, `47–48` (all clear after the table). -/
def thrOps (aV bV aT bT : ℕ) : List (ROp NR) :=
  [.pow2 ⟨![rLL, 30, 47, 48], by decide⟩, .mulAdd ⟨![rMa, 30, 31, 47, 48], by decide⟩,
   .mulAdd ⟨![31, rMM, 32, 47, 48], by decide⟩, .clear 31,
   .copy rLAM 33 47, .addC 33 1, .copy 33 34 47, .mulAdd ⟨![33, 34, 35, 47, 48], by decide⟩, .clear 34,
   .copy 35 34 47, .mulAdd ⟨![35, 34, 36, 47, 48], by decide⟩, .clear 34, .clear 35, .clear 33,
   .mulAdd ⟨![rMa, rMM, 37, 47, 48], by decide⟩, .mulAdd ⟨![37, 36, 38, 47, 48], by decide⟩, .clear 37, .clear 36,
   .addC 39 (4 * aV), .mulAdd ⟨![32, 39, 40, 47, 48], by decide⟩, .clear 39,
   .addC 19 bV, .div ⟨![40, 19, rV1, 13, 14, 15, 16, 17, 18], by decide⟩, .clear 40,
   .addC 39 2, .mulAdd ⟨![38, 39, rV1, 47, 48], by decide⟩,
   .mulAdd ⟨![32, 39, rQ1, 47, 48], by decide⟩, .mulAdd ⟨![38, 39, rQ1, 47, 48], by decide⟩, .clear 39,
   .addC 39 (2 * aV), .mulAdd ⟨![32, 39, 40, 47, 48], by decide⟩, .clear 39,
   .div ⟨![40, 19, rQ1, 13, 14, 15, 16, 17, 18], by decide⟩, .clear 40, .clear 19,
   .addC 39 aT, .mulAdd ⟨![32, 39, 40, 47, 48], by decide⟩, .clear 39, .addC 40 (bT - 1), .addC 19 bT,
   .div ⟨![40, 19, 20, 13, 14, 15, 16, 17, 18], by decide⟩, .clear 40, .clear 19,
   .copy 38 rU0 47, .sub ⟨![rU0, 20, 47, 48], by decide⟩, .copy 20 rU1 47, .sub ⟨![rU1, 38, 47, 48], by decide⟩,
   .clear 20, .clear 38, .clear 32, .clear 30]

/-- The registers the thresholds need clear (all clear after the table). -/
def thrZero : List (Fin NR) :=
  [13, 14, 15, 16, 17, 18, 19, 20, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 47, 48]

/-- Every value the threshold arithmetic holds fits the capacity. -/
def thrCap (S4 p M Λ aV bV aT bT : ℕ) : ℕ :=
  S4 + M + Λ + 2 + 2 ^ (p + 1) + S4 * 2 ^ p + (Λ + 1) * (Λ + 1) + (Λ + 1) * (Λ + 1) * ((Λ + 1) * (Λ + 1)) +
    S4 * M + 2 * (S4 * M * ((Λ + 1) * (Λ + 1) * ((Λ + 1) * (Λ + 1)))) + 2 * (S4 * 2 ^ p * M) + 4 * aV + bV + aT +
    bT + S4 * 2 ^ p * M * (4 * aV) + S4 * 2 ^ p * M * (2 * aV) + S4 * 2 ^ p * M * aT

theorem thrOps_pre (aV bV aT bT : ℕ) (u : Fin NR → ℕ) (S4 p M Λ : ℕ) (hS : u rMa = S4) (hp : u rLL = p)
    (hM : u rMM = M) (hl : u rLAM = Λ) (hz : ∀ r, r ∈ thrZero → u r = 0) (hbV : 1 ≤ bV) (hbT : 1 ≤ bT)
    (hc : thrCap S4 p M Λ aV bV aT bT ≤ cap) : preL cap (thrOps aV bV aT bT) u := by
  unfold thrCap at hc
  have e1 : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ]; ring
  have d1 := Nat.div_le_self (S4 * 2 ^ p * M * (4 * aV)) bV
  have d2 := Nat.div_le_self (S4 * 2 ^ p * M * (2 * aV)) bV
  have d3 := Nat.div_le_self (S4 * 2 ^ p * M * aT + (bT - 1)) bT
  have m1 := Nat.mod_le (S4 * 2 ^ p * M * (4 * aV)) bV
  have m2 := Nat.mod_le (S4 * 2 ^ p * M * (2 * aV)) bV
  have m3 := Nat.mod_le (S4 * 2 ^ p * M * aT + (bT - 1)) bT
  simp +decide [thrOps, preL, Function.update_apply, hS, hp, hM, hl, hz, thrZero]
  and_intros
  all_goals omega

theorem thrOps_val (aV bV aT bT : ℕ) (u : Fin NR → ℕ) (S4 p M Λ : ℕ) (hS : u rMa = S4) (hp : u rLL = p)
    (hM : u rMM = M) (hl : u rLAM = Λ) (hz : ∀ r, r ∈ thrZero → u r = 0) :
    evalL (thrOps aV bV aT bT) u rV0 = 0 ∧
    evalL (thrOps aV bV aT bT) u rV1 = kOf S4 p M * (4 * aV) / bV + xOf S4 Λ M * 2 ∧
    evalL (thrOps aV bV aT bT) u rQ0 = 0 ∧
    evalL (thrOps aV bV aT bT) u rQ1 = kOf S4 p M * 2 + xOf S4 Λ M * 2 + kOf S4 p M * (2 * aV) / bV ∧
    evalL (thrOps aV bV aT bT) u rU0 = xOf S4 Λ M - aOf S4 p M aT bT ∧
    evalL (thrOps aV bV aT bT) u rU1 = aOf S4 p M aT bT - xOf S4 Λ M := by
  simp +decide [thrOps, evalL, Function.update_apply, hS, hp, hM, hl, hz, thrZero, kOf, xOf, aOf]

/-! ## The reads: `q` from the request word, the PCPP output's counts -/

section Reads
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.RepairRepresentation (natWord)
variable (src : Fin 11 → List Bool)

/-- Read `q` (the request word's first field) into `QQ`; read the PCPP output's `count, sys, aux, cb` into
`K1` (then cleared), `SYS`, `AUX`, `CB`; rewind both streams. -/
def numReads : WM 10 NR :=
  .seq (readNatM true sHd rF rC rQQ rP rTT) (.seq (rewB sHd rBIG rT)
    (.seq (readNatM false sPO rF rC rK1 rP rTT) (.seq (WM.clear rK1)
    (.seq (readNatM false sPO rF rC rSYS rP rTT) (.seq (readNatM false sPO rF rC rAUX rP rTT)
    (.seq (readNatM false sPO rF rC rCB rP rTT) (rewB sPO rBIG rT)))))))

/-- A field read's cost. -/
def readC (x : ℕ) : ℕ := (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)

/-- One field of a stream read into a clear register `R`. -/
theorem readTs (ε : Bool) (s : Fin 11) (hs1 : s ≠ sOut) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool)
    (R : Fin NR) (hR : R ≠ rF ∧ R ≠ rC ∧ R ≠ rP ∧ R ≠ rTT ∧ R ≠ rOP) (x : ℕ) (pre rest : List Bool)
    (hsrc : src s = pre ++ enc ε (natWord x) ++ rest) (hh : (ts src h o v c).sh s = pre.length)
    (hf : v rF = 0) (hc : v rC = 0) (hp : v rP = 0) (ht : v rTT = 0) (hR0 : v R = 0)
    (hcap : 2 ^ (natBitLength x + 1) ≤ cap) :
    WExec cap (readNatM ε s rF rC R rP rTT) (ts src h o v c)
      (((ts src h o v c).seth s (pre.length + stp ε * (natWord x).length)).setv R x) (readC x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  have e := readNatM_spec cap ε s rF rC R rP rTT (by decide) (Ne.symm h1) (by decide) (by decide) (Ne.symm h2)
    (by decide) (by decide) (Ne.symm h3) (by decide) h4 x pre rest (ts src h o v c)
    (by rw [ts_st _ _ _ _ _ _ hs1, hsrc]) hh (by rw [ts_val _ _ _ _ _ rF (by decide)]; exact hf)
    (by rw [ts_val _ _ _ _ _ rC (by decide)]; exact hc) (by rw [ts_val _ _ _ _ _ rP (by decide)]; exact hp)
    (by rw [ts_val _ _ _ _ _ rTT (by decide)]; exact ht) (by rw [ts_val _ _ _ _ _ R h5, hR0]; omega)
  rw [ts_val _ _ _ _ _ R h5, hR0, Nat.zero_add] at e
  exact e

theorem ts_rew (s : Fin 11) (h1 : s ≠ sOut) (h2 : s ≠ sPO) (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool)
    (P : ℕ) (r : Fin NR) (hr : r ≠ rOP) (x : ℕ) :
    (((ts src h o v c).seth s P).setv r x).seth s 0 = ts src h o (Function.update v r x) c := by
  show (((ts src h o v c).setv r x).seth s P).seth s 0 = _
  rw [ts_setv src h o v c r hr x, ts_seth_zero src h o _ c s h1 h2 P]

theorem ts_readPO (h : ℕ) (o : List Bool) (v : Fin NR → ℕ) (c : Bool) (P : ℕ) (r : Fin NR) (hr : r ≠ rOP) (x : ℕ) :
    ((ts src h o v c).seth sPO P).setv r x = ts src P o (Function.update v r x) c := by
  rw [ts_seth_PO, ts_setv src P o v c r hr x]

/-- The reads' cost at the rewind budget `B`. -/
def readsCost (q sys aux cb B : ℕ) : ℕ :=
  readC q + readC 3 + readC sys + readC aux + readC cb + 2 * (9 * B + 3 + 7 * B) + 10 + 7

/-- **The reads.** -/
theorem numReadsT (c : Bool) (v : Fin NR → ℕ) (q sys aux cb : ℕ) (restH restP : List Bool)
    (hH : src sHd = enc true (natWord q) ++ restH)
    (hP : src sPO = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP)
    (hf : v rF = 0) (hc : v rC = 0) (hp : v rP = 0) (ht : v rTT = 0) (hT : v rT = 0) (hq0 : v rQQ = 0)
    (hk0 : v rK1 = 0) (hy0 : v rSYS = 0) (ha0 : v rAUX = 0) (hb0 : v rCB = 0)
    (hB1 : 2 * (natWord q).length ≤ v rBIG)
    (hB2 : (natWord 3).length + (natWord sys).length + (natWord aux).length + (natWord cb).length ≤ v rBIG)
    (hBc : v rBIG ≤ cap) (cq : 2 ^ (natBitLength q + 1) ≤ cap) (c3 : 2 ^ (natBitLength 3 + 1) ≤ cap)
    (cs : 2 ^ (natBitLength sys + 1) ≤ cap) (ca : 2 ^ (natBitLength aux + 1) ≤ cap)
    (cc : 2 ^ (natBitLength cb + 1) ≤ cap) :
    WExec cap numReads (ts src 0 [] v c)
      (ts src 0 [] (Function.update (Function.update (Function.update (Function.update v rQQ q) rSYS sys) rAUX aux)
        rCB cb) c) (readsCost q sys aux cb (v rBIG)) := by
  -- 1. `q`, rewind the request word
  have r1 := readTs cap src true sHd (by decide) 0 [] v c rQQ (by decide) q [] restH (by rw [hH]; rfl)
    (by rw [ts_sh_src src 0 [] v c sHd (by decide) (by decide)]; rfl) hf hc hp ht hq0 cq
  set v1 := Function.update v rQQ q with hv1
  have hB : (((ts src 0 [] v c).seth sHd (([] : List Bool).length + stp true * (natWord q).length)).setv rQQ q).val rBIG = v rBIG := by
    simp +decide [ts, Function.update_apply]
  have hTv : (((ts src 0 [] v c).seth sHd (([] : List Bool).length + stp true * (natWord q).length)).setv rQQ q).val rT = 0 := by
    simp +decide [ts, Function.update_apply, hT]
  have hsh : (((ts src 0 [] v c).seth sHd (([] : List Bool).length + stp true * (natWord q).length)).setv rQQ q).sh sHd =
      2 * (natWord q).length := by
    simp +decide [ts, Function.update_apply, stp]
  have w1 := rewB_spec cap sHd rBIG rT (by decide)
    (((ts src 0 [] v c).seth sHd (([] : List Bool).length + stp true * (natWord q).length)).setv rQQ q) hTv
    (by rw [hsh, hB]; exact hB1) (by rw [hB]; exact hBc)
  rw [ts_rew src sHd (by decide) (by decide) 0 [] v c _ rQQ (by decide) q, hB] at w1
  -- 2. the count (cleared), `sys`, `aux`, `cb`
  have r2 := readTs cap src false sPO (by decide) 0 [] v1 c rK1 (by decide) 3 []
    (natWord sys ++ natWord aux ++ natWord cb ++ restP) (by rw [hP]; simp [PrimAsm.ParseNat.enc])
    (by simp) (by simp +decide [v1, hf]) (by simp +decide [v1, hc]) (by simp +decide [v1, hp])
    (by simp +decide [v1, ht]) (by simp +decide [v1, hk0]) c3
  rw [ts_readPO src 0 [] v1 c _ rK1 (by decide) 3] at r2
  have k2 := wclear_spec cap rK1 3 (ts src (([] : List Bool).length + stp false * (natWord 3).length) [] (Function.update v1 rK1 3) c)
    (by rw [ts_val _ _ _ _ _ rK1 (by decide)]; simp)
    (by
      have h3 : 3 < 2 ^ natBitLength 3 := Nat.lt_pow_succ_log_self (by norm_num) 3
      have e3 : 2 ^ (natBitLength 3 + 1) = 2 * 2 ^ natBitLength 3 := by rw [pow_succ]; ring
      rw [ts_val _ _ _ _ _ rK1 (by decide)]; simp; omega)
  have e0 : Function.update v1 rK1 0 = v1 := by
    rw [Function.update_eq_self_iff]; simp +decide [v1, hk0]
  rw [ts_setv src _ [] _ c rK1 (by decide) 0, Function.update_idem, e0] at k2
  have r3 := readTs cap src false sPO (by decide) (([] : List Bool).length + stp false * (natWord 3).length) [] v1 c rSYS (by decide)
    sys (natWord 3) (natWord aux ++ natWord cb ++ restP) (by rw [hP]; simp [PrimAsm.ParseNat.enc])
    (by simp [stp] <;> omega) (by simp +decide [v1, hf]) (by simp +decide [v1, hc]) (by simp +decide [v1, hp])
    (by simp +decide [v1, ht]) (by simp +decide [v1, hy0]) cs
  rw [ts_readPO src _ [] v1 c _ rSYS (by decide) sys] at r3
  set v2 := Function.update v1 rSYS sys with hv2
  have r4 := readTs cap src false sPO (by decide) ((natWord 3).length + stp false * (natWord sys).length) [] v2 c rAUX
    (by decide) aux (natWord 3 ++ natWord sys) (natWord cb ++ restP) (by rw [hP]; simp [PrimAsm.ParseNat.enc])
    (by simp [stp] <;> omega) (by simp +decide [v2, v1, hf]) (by simp +decide [v2, v1, hc]) (by simp +decide [v2, v1, hp])
    (by simp +decide [v2, v1, ht]) (by simp +decide [v2, v1, ha0]) ca
  rw [ts_readPO src _ [] v2 c _ rAUX (by decide) aux] at r4
  set v3 := Function.update v2 rAUX aux with hv3
  have r5 := readTs cap src false sPO (by decide) ((natWord 3 ++ natWord sys).length + stp false * (natWord aux).length)
    [] v3 c rCB (by decide) cb (natWord 3 ++ natWord sys ++ natWord aux) restP (by rw [hP]; simp [PrimAsm.ParseNat.enc])
    (by simp [stp] <;> omega) (by simp +decide [v3, v2, v1, hf]) (by simp +decide [v3, v2, v1, hc])
    (by simp +decide [v3, v2, v1, hp]) (by simp +decide [v3, v2, v1, ht]) (by simp +decide [v3, v2, v1, hb0]) cc
  rw [ts_readPO src _ [] v3 c _ rCB (by decide) cb] at r5
  set v4 := Function.update v3 rCB cb with hv4
  have l3 := PrimAsm.ParseNat.natWord_length 3
  have ls := PrimAsm.ParseNat.natWord_length sys
  have la := PrimAsm.ParseNat.natWord_length aux
  have lb := PrimAsm.ParseNat.natWord_length cb
  have w2 := rewB_spec cap sPO rBIG rT (by decide)
    (ts src ((natWord 3 ++ natWord sys ++ natWord aux).length + stp false * (natWord cb).length) [] v4 c)
    (by rw [ts_val _ _ _ _ _ rT (by decide)]; simp +decide [v4, v3, v2, v1, hT])
    (by rw [ts_sh_PO, ts_val _ _ _ _ _ rBIG (by decide)]; simp +decide [v4, v3, v2, v1, stp]; omega)
    (by rw [ts_val _ _ _ _ _ rBIG (by decide)]; simp +decide [v4, v3, v2, v1]; omega)
  rw [ts_seth_PO, ts_val _ _ _ _ _ rBIG (by decide)] at w2
  have eB : v4 rBIG = v rBIG := by simp +decide [v4, v3, v2, v1]
  rw [eB] at w2
  refine WExec.cast cap (WExec.seq r1 (WExec.seq w1 (WExec.seq r2 (WExec.seq k2 (WExec.seq r3 (WExec.seq r4
    (WExec.seq r5 w2))))))) rfl ?_
  unfold readsCost
  omega

end Reads

/-! ## The precision and the grid (PA's `phaseA1`, `sparseM`) -/

section Grid
open NearCubicWires.WireExponent3_5.PrimAsm.StarNums NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
variable (src : Fin 11 → List Bool) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- `phaseA1`'s registers: `S 0 = QQ`, `S 1 = LL`, scratch from the clear block. -/
def sA : Fin 20 ↪ Fin NR :=
  ⟨![rQQ, rLL, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 13, 14, 15, 16, 17, 18], by decide⟩

/-- `sparseM`'s registers: `G 0 = LL`, `G 11 = LAM`, `G 12 = SS`, scratch from the clear block. -/
def gS : Fin 24 ↪ Fin NR :=
  ⟨![rLL, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, rLAM, rSS, 34, 35, 13, 14, 15, 16, 17, 18, 19, 20, 21], by decide⟩

/-- The registers holding the reads. -/
def readIn : List (Fin NR) := [rBIG, rCDF, rQQ, rSYS, rAUX, rCB]

theorem ts_val_eq (h : ℕ) (v : Fin NR → ℕ) (c : Bool) (hO : v rOP = 0) : (ts src h [] v c).val = v := by
  simp only [ts, List.length_nil]; exact Function.update_eq_self_iff.mpr hO.symm

theorem withVal_ts (h : ℕ) (v w : Fin NR → ℕ) (c : Bool) (hO : w rOP = 0) :
    withVal (ts src h [] v c) w = ts src h [] w c := by
  refine WState.eq rfl rfl ?_ rfl
  simp only [withVal, ts, List.length_nil]; exact (Function.update_eq_self_iff.mpr hO.symm).symm

theorem sA_out : ∀ i : Fin 20, i ≠ 0 → sA i ∉ readIn := by decide
theorem gS_out : ∀ i : Fin 24, i ≠ 0 → gS i ∉ readIn ∧ gS i ≠ rLL := by decide

/-- **The precision `p = ⌈log₂(q+2)⌉` and the grid `Λ̄(q)`, `s(q)`.** -/
theorem numGridT (Cδ : ℕ) (c : Bool) (u : Fin NR → ℕ) (q : ℕ) (hq : u rQQ = q) (hu : ∀ r, r ∉ readIn → u r = 0)
    (hq4 : q + 4 ≤ cap) (hcap : sparseBound ζ Cδ (Ledger.Lq q) (Ledger.rowBt h0 h1 q - 1) ≤ cap) :
    WExec cap (.seq (phaseA1 sA) (sparseM ζ Cδ gS)) (ts src 0 [] u c)
      (ts src 0 [] (Function.update (Function.update (Function.update u rLL (Ledger.Lq q)) rLAM
        (Ledger.rowBLambda h0 h1 2 q)) rSS (Ledger.rowBSparse h0 h1 2 Cδ q)) c)
      (90 * q + 200 + 1 + (Ledger.rowBt h0 h1 q + 5) * (40 * PrimAsm.UnaryPow.sq cap)) := by
  have hO : u rOP = 0 := hu rOP (by decide)
  have a1 := phaseA1_spec cap sA (ts src 0 [] u c)
    (by
      intro i hi
      rw [ts_val_eq src 0 u c hO]
      exact hu _ (sA_out i hi))
    (by rw [ts_val_eq src 0 u c hO]; simp +decide [sA, hq]; omega)
  have eL : natBitLength ((ts src 0 [] u c).val (sA 0) + 1) = Ledger.Lq q := by
    rw [ts_val_eq src 0 u c hO]; simp +decide [sA, hq, Ledger.Lq, clog_two_add_two]
  have e0 : (ts src 0 [] u c).val (sA 0) = q := by rw [ts_val_eq src 0 u c hO]; exact hq
  rw [eL, e0, show sA 1 = rLL from rfl, ts_setv src 0 [] u c rLL (by decide)] at a1
  set u1 := Function.update u rLL (Ledger.Lq q) with hu1
  have hO1 : u1 rOP = 0 := by simp +decide [u1, hO]
  have sp := sparse_spec cap h0 h1 Cδ gS (ts src 0 [] u1 c) q
    (by rw [ts_val_eq src 0 u1 c hO1]; simp +decide [gS, u1])
    (by
      intro i hi
      rw [ts_val_eq src 0 u1 c hO1, hu1, Function.update_of_ne (gS_out i hi).2]
      exact hu _ (gS_out i hi).1)
    hcap
  rw [show gS 11 = rLAM from rfl, show gS 12 = rSS from rfl, ts_setv src 0 [] u1 c rLAM (by decide),
    ts_setv src 0 [] _ c rSS (by decide)] at sp
  exact WExec.seq a1 sp

end Grid

/-! ## The numbers, composed -/

section Compose
open NearCubicWires.WireExponent3_5.PrimAsm.StarNums NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.RepairRepresentation (natWord)
variable (src : Fin 11 → List Bool) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The numbers' program**: the reads, the precision and the grid, the arithmetic. -/
def numP (ζ : ℚ) (Cδ : ℕ) : WM 10 NR :=
  .seq numReads (.seq (.seq (phaseA1 sA) (sparseM ζ Cδ gS)) (compileL numOps))

/-- The registers before the arithmetic. -/
def numU (v : Fin NR → ℕ) (q sys aux cb p Λ s : ℕ) : Fin NR → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update v rQQ q) rSYS sys) rAUX aux) rCB cb) rLL p) rLAM Λ) rSS s

/-- The registers after the numbers. -/
def numV (v : Fin NR → ℕ) (q sys aux cb p Λ s : ℕ) : Fin NR → ℕ :=
  evalL numOps (numU v q sys aux cb p Λ s)

theorem numU_facts (v : Fin NR → ℕ) (q sys aux cb p Λ s : ℕ) (hv : ∀ r, r ≠ rBIG → r ≠ rCDF → v r = 0) :
    numU v q sys aux cb p Λ s rSS = s ∧ numU v q sys aux cb p Λ s rLAM = Λ ∧ numU v q sys aux cb p Λ s rLL = p ∧
    numU v q sys aux cb p Λ s rQQ = q ∧ numU v q sys aux cb p Λ s rSYS = sys ∧
    numU v q sys aux cb p Λ s rAUX = aux ∧ numU v q sys aux cb p Λ s rCB = cb ∧
    ∀ r, r ∉ numIn → numU v q sys aux cb p Λ s r = 0 := by
  refine ⟨by simp +decide [numU], by simp +decide [numU], by simp +decide [numU], by simp +decide [numU],
    by simp +decide [numU], by simp +decide [numU], by simp +decide [numU], ?_⟩
  intro r hr
  simp only [numIn, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hr
  simp only [numU, Function.update_of_ne a3, Function.update_of_ne a4, Function.update_of_ne a5,
    Function.update_of_ne a6, Function.update_of_ne a7, Function.update_of_ne a8, Function.update_of_ne a9]
  exact hv r a1 a2

/-- The numbers' cost. -/
def numCost (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (q sys aux cb B : ℕ) : ℕ :=
  readsCost q sys aux cb B + 90 * q + 205 + (Ledger.rowBt h0 h1 q + 5) * (40 * PrimAsm.UnaryPow.sq cap) +
    numOps.length * (200 * (cap + 2) * (cap + 2) + 1)

/-- **The numbers.** From the request word (`q`) and the PCPP output (`sys, aux, cb`) at the streams' starts, all
registers clear but the rewind budget `BIG` and the constant's description flag `CDF`, the program leaves the
arithmetic's registers `numV` (`p = L(q)`, `Λ̄ = Λ̄(q)`, `s = s(q)` at `C_Λ = 2`). -/
theorem numT (Cδ : ℕ) (c : Bool) (v : Fin NR → ℕ) (q sys aux cb : ℕ) (restH restP : List Bool)
    (hH : src sHd = enc true (natWord q) ++ restH)
    (hP : src sPO = natWord 3 ++ natWord sys ++ natWord aux ++ natWord cb ++ restP)
    (hv : ∀ r, r ≠ rBIG → r ≠ rCDF → v r = 0)
    (hB1 : 2 * (natWord q).length ≤ v rBIG)
    (hB2 : (natWord 3).length + (natWord sys).length + (natWord aux).length + (natWord cb).length ≤ v rBIG)
    (hBc : v rBIG ≤ cap) (cq : 2 ^ (natBitLength q + 1) ≤ cap) (c3 : 2 ^ (natBitLength 3 + 1) ≤ cap)
    (cs : 2 ^ (natBitLength sys + 1) ≤ cap) (ca : 2 ^ (natBitLength aux + 1) ≤ cap)
    (cc : 2 ^ (natBitLength cb + 1) ≤ cap) (hq4 : q + 4 ≤ cap)
    (hsp : sparseBound ζ Cδ (Ledger.Lq q) (Ledger.rowBt h0 h1 q - 1) ≤ cap)
    (hc : numCap (Ledger.rowBSparse h0 h1 2 Cδ q) (Ledger.rowBLambda h0 h1 2 q) q sys aux cb ≤ cap) :
    WExec cap (numP ζ Cδ) (ts src 0 [] v c)
      (ts src 0 [] (numV v q sys aux cb (Ledger.Lq q) (Ledger.rowBLambda h0 h1 2 q)
        (Ledger.rowBSparse h0 h1 2 Cδ q)) c) (numCost cap h0 h1 q sys aux cb (v rBIG)) := by
  have z : ∀ r : Fin NR, r ≠ rBIG → r ≠ rCDF → v r = 0 := hv
  have rd := numReadsT cap src c v q sys aux cb restH restP hH hP (z _ (by decide) (by decide))
    (z _ (by decide) (by decide)) (z _ (by decide) (by decide)) (z _ (by decide) (by decide))
    (z _ (by decide) (by decide)) (z _ (by decide) (by decide)) (z _ (by decide) (by decide))
    (z _ (by decide) (by decide)) (z _ (by decide) (by decide)) (z _ (by decide) (by decide)) hB1 hB2 hBc cq c3 cs
    ca cc
  set u0 := Function.update (Function.update (Function.update (Function.update v rQQ q) rSYS sys) rAUX aux) rCB cb
    with hu0
  have gr := numGridT cap src h0 h1 Cδ c u0 q (by simp +decide [u0])
    (by
      intro r hr
      simp only [readIn, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hr
      simp only [u0, Function.update_of_ne a3, Function.update_of_ne a4, Function.update_of_ne a5,
        Function.update_of_ne a6]
      exact hv r a1 a2) hq4 hsp
  set U := numU v q sys aux cb (Ledger.Lq q) (Ledger.rowBLambda h0 h1 2 q) (Ledger.rowBSparse h0 h1 2 Cδ q) with hU
  have eU : Function.update (Function.update (Function.update u0 rLL (Ledger.Lq q)) rLAM
      (Ledger.rowBLambda h0 h1 2 q)) rSS (Ledger.rowBSparse h0 h1 2 Cδ q) = U := rfl
  rw [eU] at gr
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := numU_facts v q sys aux cb (Ledger.Lq q) (Ledger.rowBLambda h0 h1 2 q)
    (Ledger.rowBSparse h0 h1 2 Cδ q) hv
  have hpre := numOps_pre cap U _ _ _ _ _ _ _ f1 f2 f3 f4 f5 f6 f7 f8 hc
  have hO : U rOP = 0 := f8 rOP (by decide)
  have op := opsT cap numOps (ts src 0 [] U c) (by rw [ts_val_eq src 0 U c hO]; exact hpre)
  rw [ts_val_eq src 0 U c hO, withVal_ts src 0 U _ c
    (by rw [evalL_frame _ U rOP (by simp +decide [numOps, preOps, magOps, writes])]; exact hO)] at op
  have hcl := costL_le cap numOps U hpre
  refine WExec.cast cap (WExec.seq rd (WExec.seq gr op)) rfl ?_
  unfold numCost
  omega

end Compose

/-! ## The thresholds are `tr:thresholds` with the rounding slack -/

section Thresholds
open NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge

theorem ceil_div_nat (m n : ℕ) (hn : 0 < n) : ⌈((m : ℚ) / n)⌉ = (((m + (n - 1)) / n : ℕ) : ℤ) := by
  set k := (m + (n - 1)) / n with hk
  have h1 : k * n ≤ m + (n - 1) := Nat.div_mul_le_self _ _
  have h2 : m + (n - 1) < k * n + n := Nat.lt_div_mul_add hn
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [Int.ceil_eq_iff]
  push_cast
  constructor
  · rw [lt_div_iff₀ hn']
    have : k * n < m + n := by omega
    have : ((k * n : ℕ) : ℚ) < ((m + n : ℕ) : ℚ) := by exact_mod_cast this
    push_cast at this
    linarith
  · rw [div_le_iff₀ hn']
    have : m ≤ k * n := by omega
    exact_mod_cast this

theorem floor_div_add (N d X : ℕ) : ⌊((N : ℚ) / d + X)⌋ = ((N / d + X : ℕ) : ℤ) := by
  rw [Int.floor_add_natCast, Int.floor_div_natCast, Int.floor_natCast]
  push_cast; ring

/-- **The accumulators' start** at `v₀ = aV/bV`, `τ = aT/bT`, `δ = (1+Λ̄)⁴/2^p` (`slackOf`), `K = s⁴2^p·2M`,
`K' = s⁴2^pM`, `M = 2^{cb}`: `threshAcc ⌊K(2v₀+δ)⌋ ⌊K(1+v₀+δ)⌋ ⌈K'(τ−δ)⌉` is the machine's six values. -/
theorem thrVals (s Λ p cb aV bV aT bT : ℕ) (hbV : 0 < bV) (hbT : 0 < bT) :
    threshAcc ⌊(s : ℚ) ^ 4 * 2 ^ p * (2 ^ cb * 2) * (2 * ((aV : ℚ) / bV) + (1 + (Λ : ℚ)) ^ 4 / 2 ^ p)⌋
      ⌊(s : ℚ) ^ 4 * 2 ^ p * (2 ^ cb * 2) * (1 + (aV : ℚ) / bV + (1 + (Λ : ℚ)) ^ 4 / 2 ^ p)⌋
      ⌈(s : ℚ) ^ 4 * 2 ^ p * 2 ^ cb * ((aT : ℚ) / bT - (1 + (Λ : ℚ)) ^ 4 / 2 ^ p)⌉ =
    ![0, kOf (s * s * s * s) p (2 ^ cb) * (4 * aV) / bV + xOf (s * s * s * s) Λ (2 ^ cb) * 2, 0,
      kOf (s * s * s * s) p (2 ^ cb) * 2 + xOf (s * s * s * s) Λ (2 ^ cb) * 2 +
        kOf (s * s * s * s) p (2 ^ cb) * (2 * aV) / bV,
      xOf (s * s * s * s) Λ (2 ^ cb) - aOf (s * s * s * s) p (2 ^ cb) aT bT,
      aOf (s * s * s * s) p (2 ^ cb) aT bT - xOf (s * s * s * s) Λ (2 ^ cb)] := by
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  have hbV' : (0 : ℚ) < bV := by exact_mod_cast hbV
  have hbT' : (0 : ℚ) < bT := by exact_mod_cast hbT
  have eV : (s : ℚ) ^ 4 * 2 ^ p * (2 ^ cb * 2) * (2 * ((aV : ℚ) / bV) + (1 + (Λ : ℚ)) ^ 4 / 2 ^ p) =
      ((kOf (s * s * s * s) p (2 ^ cb) * (4 * aV) : ℕ) : ℚ) / bV + ((xOf (s * s * s * s) Λ (2 ^ cb) * 2 : ℕ) : ℚ) := by
    unfold kOf xOf; push_cast; field_simp; ring
  have eQ : (s : ℚ) ^ 4 * 2 ^ p * (2 ^ cb * 2) * (1 + (aV : ℚ) / bV + (1 + (Λ : ℚ)) ^ 4 / 2 ^ p) =
      ((kOf (s * s * s * s) p (2 ^ cb) * (2 * aV) : ℕ) : ℚ) / bV +
        ((kOf (s * s * s * s) p (2 ^ cb) * 2 + xOf (s * s * s * s) Λ (2 ^ cb) * 2 : ℕ) : ℚ) := by
    unfold kOf xOf; push_cast; field_simp; ring
  have eM : (s : ℚ) ^ 4 * 2 ^ p * 2 ^ cb * ((aT : ℚ) / bT - (1 + (Λ : ℚ)) ^ 4 / 2 ^ p) =
      ((kOf (s * s * s * s) p (2 ^ cb) * aT : ℕ) : ℚ) / bT - ((xOf (s * s * s * s) Λ (2 ^ cb) : ℕ) : ℚ) := by
    unfold kOf xOf; push_cast; field_simp; ring
  rw [eV, eQ, eM, floor_div_add, floor_div_add, Int.ceil_sub_natCast, ceil_div_nat _ _ hbT]
  unfold aOf
  generalize kOf (s * s * s * s) p (2 ^ cb) * (4 * aV) / bV = A1
  generalize kOf (s * s * s * s) p (2 ^ cb) * (2 * aV) / bV = A2
  generalize (kOf (s * s * s * s) p (2 ^ cb) * aT + (bT - 1)) / bT = A0
  generalize xOf (s * s * s * s) Λ (2 ^ cb) = X
  generalize kOf (s * s * s * s) p (2 ^ cb) = K
  funext i
  fin_cases i <;> simp [threshAcc] <;> omega

end Thresholds

/-! ## What the numbers leave -/

/-- The registers after the numbers. -/
structure NumOut (w : Fin NR → ℕ) (B cdf q sys aux cb p Λ s : ℕ) : Prop where
  ss : w rSS = s
  lam : w rLAM = Λ
  ll : w rLL = p
  qq : w rQQ = q
  sy : w rSYS = sys
  big : w rBIG = B
  cdf : w rCDF = cdf
  sq : w rSQ = sys * q
  mm : w rMM = 2 ^ cb
  ee : w rEE = sys * s + aux * s
  ma : w rMa = s * s * s * s
  mb : w rMb = Λ * Λ * (s * s)
  mc : w rMc = Λ * (s * s * s) + Λ * (s * s * s)
  md : w rMd = Λ * Λ * Λ * s + Λ * Λ * Λ * s
  me : w rMe = Λ * Λ * Λ * Λ
  mf : w rMf = Λ * (s * s * s)
  ok : w rOK = 1
  zero : ∀ r, r ∉ numKeep → w r = 0

theorem numV_out (v : Fin NR → ℕ) (q sys aux cb p Λ s : ℕ) (hv : ∀ r, r ≠ rBIG → r ≠ rCDF → v r = 0) :
    NumOut (numV v q sys aux cb p Λ s) (v rBIG) (v rCDF) q sys aux cb p Λ s := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := numU_facts v q sys aux cb p Λ s hv
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, -⟩ :=
    numOps_val (numU v q sys aux cb p Λ s) _ _ _ _ _ _ _ f1 f2 f3 f4 f5 f6 f7 f8
  have fr : ∀ r, r ∉ numOps.flatMap writes → numV v q sys aux cb p Λ s r = numU v q sys aux cb p Λ s r :=
    fun r hr => evalL_frame _ _ r hr
  have nw : ∀ r, r ∈ [rBIG, rCDF, rSS, rLAM, rLL, rQQ, rSYS] → r ∉ numOps.flatMap writes := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [numOps, preOps, magOps, writes]
  have v1 : ∀ r, r ∈ [rBIG, rCDF, rSS, rLAM, rLL, rQQ, rSYS] →
      numV v q sys aux cb p Λ s r = numU v q sys aux cb p Λ s r := fun r hr => fr r (nw r hr)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, ?_⟩
  · rw [v1 _ (by decide)]; exact f1
  · rw [v1 _ (by decide)]; exact f2
  · rw [v1 _ (by decide)]; exact f3
  · rw [v1 _ (by decide)]; exact f4
  · rw [v1 _ (by decide)]; exact f5
  · rw [v1 _ (by decide)]; simp +decide [numU]
  · rw [v1 _ (by decide)]; simp +decide [numU]
  · exact numOps_zero (numU v q sys aux cb p Λ s) _ _ _ _ _ _ _ f1 f2 f3 f4 f5 f6 f7 f8

theorem digits_not_kept : ∀ r : Fin NR, 24 ≤ r.val ∧ r.val < 36 → r ∉ numKeep := by decide

/-- The table writer's start registers are the numbers' (digits clear, `OK = 1`). -/
theorem regsOf_numOut (w : Fin NR → ℕ) {B cdf q sys aux cb p Λ s : ℕ} (h : NumOut w B cdf q sys aux cb p Λ s) :
    regsOf w Z4 Z4 Z4 1 = w := by
  funext r
  unfold regsOf
  split_ifs with h1 h2 h3 h4
  · rw [h1, h.ok]
  · exact (h.zero r (digits_not_kept r ⟨h2.1, by omega⟩)).symm
  · exact (h.zero r (digits_not_kept r ⟨by omega, by omega⟩)).symm
  · exact (h.zero r (digits_not_kept r ⟨by omega, h4.2⟩)).symm
  · rfl

/-- The numbers leave the readers' scratch clear. -/
theorem rdOK_numOut (w : Fin NR → ℕ) {B cdf q sys aux cb p Λ s : ℕ} (h : NumOut w B cdf q sys aux cb p Λ s) :
    RdOK w :=
  ⟨h.zero _ (by decide), h.zero _ (by decide), h.zero _ (by decide), h.zero _ (by decide), h.zero _ (by decide),
    h.zero _ (by decide), h.zero _ (by decide)⟩

theorem scr_numOut (w : Fin NR → ℕ) {B cdf q sys aux cb p Λ s : ℕ} (h : NumOut w B cdf q sys aux cb p Λ s) :
    Scr w :=
  ⟨h.zero _ (by decide), h.zero _ (by decide), h.zero _ (by decide), h.zero _ (by decide), h.zero _ (by decide),
    h.zero _ (by decide)⟩

/-- The magnitudes of `MagRegs` at `D.s = s`. -/
theorem magRegs_numOut (D : Transfer.UnionCheckData) (w : Fin NR → ℕ) {B cdf q sys aux cb p Λ s : ℕ}
    (h : NumOut w B cdf q sys aux cb p Λ s) (hs : D.s = s) : MagRegs D Λ w :=
  ⟨by rw [h.ma, hs], by rw [h.mb, hs]; ring, by rw [h.mc, hs]; ring, by rw [h.md, hs]; ring, h.me,
    by rw [h.mf, hs]; ring⟩

/-- The registers the thresholds need clear are clear after the numbers. -/
theorem thrZero_numOut (w : Fin NR → ℕ) {B cdf q sys aux cb p Λ s : ℕ} (h : NumOut w B cdf q sys aux cb p Λ s) :
    ∀ r, r ∈ thrZero → w r = 0 := fun r hr => h.zero r (by
  revert r; decide)

/-- The accumulator registers. -/
def rAcc (i : Fin 6) : Fin NR := ⟨24 + i.val, by have := i.isLt; show 24 + i.val < 56; omega⟩

/-- **The accumulators' start is `decision_slack`'s**: after the thresholds, from registers with `s⁴` (`Ma`),
`p` (`LL`), `2^{cb}` (`MM`), `Λ̄` (`LAM`) and the threshold scratch clear, at `D.s = s`, `D.mass = Λ̄`, `D`'s clause
bits `cb`, `v₀ = aV/bV`, `τ = aT/bT`, the six accumulator registers are
`threshAcc ⌊K(2v₀+δ)⌋ ⌊K(1+v₀+δ)⌋ ⌈K'(τ−δ)⌉` with `K = scaleVQ D p`, `K' = scaleMu D p`, `δ = slackOf D.mass p`
. -/
theorem accStart_eq (D : Transfer.UnionCheckData) (aV bV aT bT : ℕ) (u : Fin NR → ℕ) (s Λ p cb : ℕ)
    (hS : u rMa = s * s * s * s) (hp : u rLL = p) (hM : u rMM = 2 ^ cb) (hl : u rLAM = Λ)
    (hz : ∀ r, r ∈ thrZero → u r = 0) (hs : D.s = s) (hm : D.mass = Λ) (hcb : D.pcpp.clauseBits = cb) (v0 τ : ℚ)
    (hv0 : v0 = (aV : ℚ) / bV) (hτ : τ = (aT : ℚ) / bT) (hbV : 0 < bV) (hbT : 0 < bT) :
    (fun i => evalL (thrOps aV bV aT bT) u (rAcc i)) = DecisionBridge.threshAcc
      ⌊Bridge.scaleVQ D p * (2 * v0 + slackOf D.mass p)⌋ ⌊Bridge.scaleVQ D p * (1 + v0 + slackOf D.mass p)⌋
      ⌈Bridge.scaleMu D p * (τ - slackOf D.mass p)⌉ := by
  have e := thrVals s Λ p cb aV bV aT bT hbV hbT
  obtain ⟨t0, t1, t2, t3, t4, t5⟩ := thrOps_val aV bV aT bT u _ _ _ _ hS hp hM hl hz
  unfold Bridge.scaleVQ Bridge.scaleMu slackOf
  rw [hs, hm, hcb, hv0, hτ, e]
  funext i
  fin_cases i
  · exact t0
  · exact t1
  · exact t2
  · exact t3
  · exact t4
  · exact t5

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
