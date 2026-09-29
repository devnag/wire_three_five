import Proof.CaseAnalysis.WeakRuntime

/-! # The weak machine's running time: `Runtime3` and its `o(T(N))` closure

Realizes `tr:time` (P3:3797-3811): "the time for all polynomially many verification calls has the form
`2^{q−k/4}q^A + 2^{q/2+O(k)}q^{O(1)} + 2^{νq}`, `ν < 1`, where `A` is fixed by the syntax and accuracy envelopes
before a constant multiplier in `r` is chosen [...] All full-row and auxiliary-seed enumerations belong to additive
preprocessing, not an unlisted per-column loop", with the budget classes of `prim:runtime` (P3:3105-3115), the clock
`T(N) = N^{C_clk}` and `2^{q(N)}/T(N) = q(N)^{O(1)}` (P3:3632-3644), and the source work `N^{d_ver}q^{O_G(1)}` with
`C_clk > d_ver + 2` (P3:3653-3655).

Main types:
* `TimeBudget kclk E`: the machine-independent time ledger. Its per-call budget `callBudget q` is the running time
  of one primitive call at native width `q` (`prim:runtime`), split into the classes of `BudgetClass`; the envelope
  `E` (every polynomial exponent) is fixed before the star width `k`. The ledger owns the star multiplier `r(q)`
  (P3:3823-3824: "Take an even `r = Θ(log L)`"), the per-mode caps `B_i(q)` (`tr:B`, P3:3425-3430, with the per-mode
  wire cap of P3:3406-3407) and the load constant `C_D` (P3:3094-3097); the star width `kOf q = r·⌊log₂(q/r+1)⌋`
  (P3:1188-1189) and the load `psiOf q = max{Ψ_T, Ψ_S, Ψ_aux}` (`prim:main-load`, `prim:aux-load`, P3:3094-3102) are
  definitions from them, not free fields.
* `Runtime3 M kclk E`: that ledger together with `tr:time`'s split of the weak machine `M`'s running time into source
  work plus `q^{callDeg}` primitive calls.
* `Runtime3.littleO`: the refuter's promise `o(T(N))` (P3:3808-3811), through the Theorem 2.5 consumer
  `CloseoutWeakRuntime.littleO_of_split`.

The per-class damping `damp_of_pow_le` is restated verbatim from `CloseoutFinal` (`FinalRuntimeSplit.lean:31-38`),
whose import closure is far larger than this module's. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5

/-- The two class modes of `thm:tradeoff` (P3:209-216). Declared with the ledger, which holds one cap per mode
(`tr:B`, P3:3406-3407, 3425-3430); their circuits and semantics are in `Proof.Wire_3_5.Foundations.Skeleton`. -/
inductive Mode
  | thr
  | sym

end NearCubicWires.WireExponent3_5

namespace NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutWeakRuntime

/-- P18: the budget classes of `prim:runtime` / `tr:time`, plus the two non-exponential ones. -/
inductive BudgetClass
  /-- `poly(N)`: parsing, PCP construction, substitution (P3:3653-3655). -/
  | sourcePoly
  /-- `2^{q/2+O(k)}q^{O(1)}`: common-coset selection (P3:3107, 3335, 3800). -/
  | selection
  /-- `2^{O(Ψ)}q^{O(1)}`: additive preprocessing (P3:3108, 3112-3114, 3804-3807). -/
  | preprocessing
  /-- `2^{q-k}q^{O(1)}` per printer call (P3:2231-2234, 2996-2998). -/
  | table
  /-- `2^{q-k/4}q^A`: the one tight term (P3:3109, 3001, 3800). -/
  | mainPass
  deriving DecidableEq

/-- Every polynomial exponent, before `r` (P3:3114-3115, 3803-3804, 3693-3697). -/
structure Envelope where
  /-- damping power; the Ledger requires `proofLog+2 ≤ sigma` (P3:3644). -/
  sigma : ℕ
  /-- "polynomially many verification calls" (P3:3797-3798): at most `q^callDeg`. -/
  callDeg : ℕ
  /-- C5 + C6 per call: `2^{q-k/4}q^Amain` (P3:3001, 3046-3054, 3109). -/
  Amain : ℕ
  /-- C3 + C4 printer calls of one primitive call: `2^{q-k}q^Atable` (P3:2231-2234, 2996-2998, 3170-3171). -/
  Atable : ℕ
  /-- C1: `2^{q/2+csel·k}q^Asel` (P3:1335, 1359-1360). -/
  Asel : ℕ
  csel : ℕ
  /-- C2 + C4 preprocessing: `2^{cpsi·Ψ}q^Apre` (P3:3108, 3170-3173). -/
  Apre : ℕ
  cpsi : ℕ

/-- The class bound at native width `q`, star width `k` and load `Ψ` (P3:3098-3100). -/
def classBound (E : Envelope) : BudgetClass → (q k psi : ℕ) → ℕ
  | .sourcePoly, q, _, _ => q ^ E.Amain
  | .selection, q, k, _ => 2 ^ (q / 2 + E.csel * k) * q ^ E.Asel
  | .preprocessing, q, _, psi => 2 ^ (E.cpsi * psi) * q ^ E.Apre
  | .table, q, k, _ => 2 ^ (q - k) * q ^ E.Atable
  | .mainPass, q, k, _ => 2 ^ (q - k / 4) * q ^ E.Amain

/-- The per-call cost contracts of C1-C6 (the machine contracts' budget fields are exactly these).
Each is a function of `(q, k, Ψ)` for EVERY `k`: a machine family uniform in `r`. One constant
coefficient `coef` is shared (it becomes the `B` of `littleO_of_split`). -/
structure ComponentCosts (E : Envelope) where
  coef : ℕ
  /-- C1 coset selection. -/
  sel : ℕ → ℕ → ℕ → ℕ
  /-- C2 explicit lists and expansions, C4 conditional-probability coefficients. -/
  pre : ℕ → ℕ → ℕ → ℕ
  /-- C3 printer table work of all `O(L²+k+L)` prefix decisions of one call. -/
  table : ℕ → ℕ → ℕ → ℕ
  /-- C5 final pass plus C6 per-call glue. -/
  main : ℕ → ℕ → ℕ → ℕ
  hsel : ∀ q k psi, sel q k psi ≤ coef * classBound E .selection q k psi
  hpre : ∀ q k psi, pre q k psi ≤ coef * classBound E .preprocessing q k psi
  htable : ∀ q k psi, table q k psi ≤ coef * classBound E .table q k psi
  hmain : ∀ q k psi, main q k psi ≤ coef * classBound E .mainPass q k psi

/-- One primitive call's time at `(q, k, Ψ)`: the sum of the component costs. -/
def ComponentCosts.perCall {E : Envelope} (C : ComponentCosts E) (q k psi : ℕ) : ℕ :=
  C.sel q k psi + C.pre q k psi + C.table q k psi + C.main q k psi

/-- The Ledger's fit conditions at one width (the only place `r`, through `k`, and `Ψ` meet the
envelope). `lg` is a supplied binary-log bound, as in the Theorem 2.5 repository's `hdamp_of_ledger`. -/
structure Fits (E : Envelope) (q lg k psi : ℕ) : Prop where
  hlog : q ≤ 2 ^ lg
  /-- main pass: `q^{Amain+callDeg+sigma} ≤ 2^{k/4}`; this is "A fixed before r" (P3:3808-3811). -/
  main : (E.Amain + E.callDeg + E.sigma) * lg ≤ k / 4
  table : (E.Atable + E.callDeg + E.sigma) * lg ≤ k
  kq : k ≤ q
  sel : E.csel * k + (E.Asel + E.callDeg + E.sigma) * lg ≤ q - q / 2
  /-- the load is `o(q)` (tr:load, P3:3787-3795, B9) and `2^{O(Ψ)} ≤ 2^{νq}` (P3:3112-3114). -/
  pre : E.cpsi * psi + (E.Apre + E.callDeg + E.sigma) * lg ≤ q

/-- Verbatim from the Theorem 2.5 repository's `CloseoutFinal.damp_of_pow_le` (`FinalRuntimeSplit.lean:31-38`). -/
theorem damp_of_pow_le {width tableExp power : ℕ} (hK : tableExp ≤ width)
    (h : width^power ≤ 2^tableExp) :
    2^(width-tableExp)*width^power ≤ 2^width := by
  calc 2^(width-tableExp)*width^power
      ≤ 2^(width-tableExp)*2^tableExp := Nat.mul_le_mul_left _ h
    _ = 2^((width-tableExp)+tableExp) := (pow_add 2 (width-tableExp) tableExp).symm
    _ = 2^width := by rw [Nat.sub_add_cancel hK]

theorem pow_le_two_pow {q lg P e : ℕ} (hlog : q ≤ 2 ^ lg) (h : P * lg ≤ e) : q ^ P ≤ 2 ^ e :=
  calc q ^ P ≤ (2 ^ lg) ^ P := Nat.pow_le_pow_left hlog P
    _ = 2 ^ (P * lg) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h

/-- One class, damped: `bound · q^{callDeg+sigma} ≤ 2^q`. -/
theorem damp_class (E : Envelope) (cls : BudgetClass) (q lg k psi : ℕ) (F : Fits E q lg k psi)
    (hcls : cls ≠ .sourcePoly) :
    classBound E cls q k psi * q ^ (E.callDeg + E.sigma) ≤ 2 ^ q := by
  cases cls with
  | sourcePoly => exact absurd rfl hcls
  | selection =>
    have hP : q ^ (E.Asel + (E.callDeg + E.sigma)) ≤ 2 ^ (q - q / 2 - E.csel * k) :=
      pow_le_two_pow F.hlog (by have := F.sel; rw [← Nat.add_assoc]; omega)
    calc classBound E .selection q k psi * q ^ (E.callDeg + E.sigma)
        = 2 ^ (q / 2 + E.csel * k) * q ^ (E.Asel + (E.callDeg + E.sigma)) := by
          simp only [classBound, pow_add]; ring
      _ ≤ 2 ^ (q / 2 + E.csel * k) * 2 ^ (q - q / 2 - E.csel * k) := Nat.mul_le_mul_left _ hP
      _ = 2 ^ q := by
          rw [← pow_add]; congr 1; have := F.sel; omega
  | preprocessing =>
    have hP : q ^ (E.Apre + (E.callDeg + E.sigma)) ≤ 2 ^ (q - E.cpsi * psi) :=
      pow_le_two_pow F.hlog (by have := F.pre; rw [← Nat.add_assoc]; omega)
    calc classBound E .preprocessing q k psi * q ^ (E.callDeg + E.sigma)
        = 2 ^ (E.cpsi * psi) * q ^ (E.Apre + (E.callDeg + E.sigma)) := by
          simp only [classBound, pow_add]; ring
      _ ≤ 2 ^ (E.cpsi * psi) * 2 ^ (q - E.cpsi * psi) := Nat.mul_le_mul_left _ hP
      _ = 2 ^ q := by rw [← pow_add]; congr 1; have := F.pre; omega
  | table =>
    have hP : q ^ (E.Atable + (E.callDeg + E.sigma)) ≤ 2 ^ k :=
      pow_le_two_pow F.hlog (by have := F.table; rw [← Nat.add_assoc]; exact this)
    calc classBound E .table q k psi * q ^ (E.callDeg + E.sigma)
        = 2 ^ (q - k) * q ^ (E.Atable + (E.callDeg + E.sigma)) := by
          simp only [classBound, pow_add]; ring
      _ ≤ 2 ^ q := damp_of_pow_le F.kq hP
  | mainPass =>
    have hP : q ^ (E.Amain + (E.callDeg + E.sigma)) ≤ 2 ^ (k / 4) :=
      pow_le_two_pow F.hlog (by have := F.main; rw [← Nat.add_assoc]; exact this)
    calc classBound E .mainPass q k psi * q ^ (E.callDeg + E.sigma)
        = 2 ^ (q - k / 4) * q ^ (E.Amain + (E.callDeg + E.sigma)) := by
          simp only [classBound, pow_add]; ring
      _ ≤ 2 ^ q := damp_of_pow_le (le_trans (Nat.div_le_self k 4) F.kq) hP

/-- All verification calls of one input length, damped: `B = 4·coef`. -/
theorem damp_calls (E : Envelope) (C : ComponentCosts E) (q lg k psi : ℕ)
    (F : Fits E q lg k psi) :
    (q ^ E.callDeg * C.perCall q k psi) * q ^ E.sigma ≤ (4 * C.coef) * 2 ^ q := by
  have hs := Nat.mul_le_mul_left C.coef (damp_class E .selection q lg k psi F (by decide))
  have hp := Nat.mul_le_mul_left C.coef (damp_class E .preprocessing q lg k psi F (by decide))
  have ht := Nat.mul_le_mul_left C.coef (damp_class E .table q lg k psi F (by decide))
  have hm := Nat.mul_le_mul_left C.coef (damp_class E .mainPass q lg k psi F (by decide))
  have hsum : C.perCall q k psi ≤ C.coef * classBound E .selection q k psi +
      C.coef * classBound E .preprocessing q k psi + C.coef * classBound E .table q k psi +
      C.coef * classBound E .mainPass q k psi := by
    unfold ComponentCosts.perCall
    have := C.hsel q k psi; have := C.hpre q k psi; have := C.htable q k psi
    have := C.hmain q k psi; omega
  have hq : q ^ E.callDeg * q ^ E.sigma = q ^ (E.callDeg + E.sigma) := (pow_add q _ _).symm
  set P := q ^ (E.callDeg + E.sigma)
  calc (q ^ E.callDeg * C.perCall q k psi) * q ^ E.sigma
      = C.perCall q k psi * P := by rw [← hq]; ring
    _ ≤ (C.coef * classBound E .selection q k psi + C.coef * classBound E .preprocessing q k psi +
          C.coef * classBound E .table q k psi + C.coef * classBound E .mainPass q k psi) * P :=
          Nat.mul_le_mul_right _ hsum
    _ = C.coef * (classBound E .selection q k psi * P) +
          C.coef * (classBound E .preprocessing q k psi * P) +
          C.coef * (classBound E .table q k psi * P) +
          C.coef * (classBound E .mainPass q k psi * P) := by ring
    _ ≤ (4 * C.coef) * 2 ^ q := by
          have e : (4 * C.coef) * 2 ^ q = C.coef * 2 ^ q + C.coef * 2 ^ q + C.coef * 2 ^ q +
            C.coef * 2 ^ q := by ring
          rw [e]; exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs hp) ht) hm

/-! ## The load of one primitive call (`prim:main-load`, `prim:aux-load`, P3:3094-3102) -/

/-- An upper square root: `√x ≤ sqrtUp x`. -/
def sqrtUp (x : ℕ) : ℕ := Nat.sqrt x + 1

/-- The star width `k = r·s`, `s = ⌊log₂(q/r+1)⌋` (`star:partition`, P3:1188-1189). -/
def starWidth (r q : ℕ) : ℕ := r * Nat.log 2 (q / r + 1)

/-- The `THR` main load `Ψ_T = C_D((k+L)² d_T + k + L²)` with `d_T = C_D(√(B_T L) + L²)` (P3:3094-3100). -/
def loadThr (CD k L B : ℕ) : ℕ := CD * ((k + L) ^ 2 * (CD * (sqrtUp (B * L) + L ^ 2)) + k + L ^ 2)

/-- The `SYM` main load `Ψ_S = C_D((k+L)² d_S + k + L²)` with `d_S = C_D(√B_S + L)` (P3:3094-3100). -/
def loadSym (CD k L B : ℕ) : ℕ := CD * ((k + L) ^ 2 * (CD * (sqrtUp B + L)) + k + L ^ 2)

/-- The auxiliary load `Ψ_aux = C_D[k + L² + (k+L³)L²(k+L)]` (P3:3101-3102). -/
def loadAux (CD k L : ℕ) : ℕ := CD * (k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L))

/-- **The load** `max{Ψ_T, Ψ_S, Ψ_aux}` of the load condition (P3:3106-3107), with the per-mode caps `B_T`, `B_S`. -/
def loadPsi (CD k L BT BS : ℕ) : ℕ := max (loadThr CD k L BT) (max (loadSym CD k L BS) (loadAux CD k L))

/-- The machine-independent time ledger of `tr:time` (P3:3797-3811): the native width `q(N)` (P3:3637-3640) with
its log bound; the star multiplier `r(q)` (P3:3823-3824), the per-mode caps `B_i(q)` (`tr:B`, P3:3425-3430) and the
load constant `C_D` (P3:3094-3097), from which the star width `kOf` and the load `psiOf` are defined; the
per-call cost contracts; the source work `A·(N+1)^a` with `a ≤ C_clk − 1` (P3:3653-3655); the proof-table bound
`2^q ≤ C·N^{C_clk}·q^d` (P3:3644); and the ledger's fit conditions, eventually along `q(N)`. -/
structure TimeBudget (kclk : ℕ) (E : Envelope) where
  /-- native width `q(N)` (P3:3637-3640) and its log bound. -/
  q : ℕ → ℕ
  lg : ℕ → ℕ
  /-- the star multiplier `r(q)` (P3:3823-3824: "Take an even `r = Θ(log L)`"). -/
  rOf : ℕ → ℕ
  /-- the regular filters' cap `B_i(q) ≥ 1` in each class mode (`tr:B`, P3:3406-3407, 3425-3430). -/
  capOf : Mode → ℕ → ℕ
  capOf_pos : ∀ m q, 1 ≤ capOf m q
  /-- the load constant `C_D` of `prim:main-load` (P3:3094-3097), fixed with the envelopes before `r`. -/
  CD : ℕ
  costs : ComponentCosts E
  /-- source work `N^{d_ver}q^{O_G(1)}`, with `C_clk > d_ver + 2` (P3:3653-3655). -/
  A : ℕ
  a : ℕ
  ha : a ≤ kclk + 1
  /-- the proof-table bound `2^q ≤ C·T(N)·q^d` (P3:3644; the Theorem 2.5 repository's `actual_table_bound`). -/
  Ctab : ℕ
  d : ℕ
  hsigma : d + 1 ≤ E.sigma
  growth : ∀ m, ∃ onset, ∀ N, onset ≤ N → m ≤ q N
  onset : ℕ
  table : ∀ N, onset ≤ N → 2 ^ q N ≤ Ctab * N ^ (kclk + 2) * q N ^ d
  fits : ∀ N, onset ≤ N → Fits E (q N) (lg (q N)) (starWidth (rOf (q N)) (q N))
    (loadPsi CD (starWidth (rOf (q N)) (q N)) (Nat.clog 2 (q N + 2)) (capOf .thr (q N)) (capOf .sym (q N)))

/-- The star width at native width `q`: `k = r(q)·⌊log₂(q/r(q)+1)⌋` (P3:1188-1189), a definition from the ledger's
`r`. -/
def TimeBudget.kOf {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (q : ℕ) : ℕ := starWidth (B.rOf q) q

/-- The load at native width `q`: `max{Ψ_T(B_T), Ψ_S(B_S), Ψ_aux}` at `k = kOf q`, `L = ⌈log₂(q+2)⌉`
(P3:3094-3107), a definition from the ledger's caps and `C_D`. -/
def TimeBudget.psiOf {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (q : ℕ) : ℕ :=
  loadPsi B.CD (B.kOf q) (Nat.clog 2 (q + 2)) (B.capOf .thr q) (B.capOf .sym q)

/-- The running time of one primitive call at native width `q` (`prim:runtime`, P3:3105-3115): the sum of the
component costs at star width `kOf q` and load `psiOf q`. -/
def TimeBudget.callBudget {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (q : ℕ) : ℕ :=
  B.costs.perCall q (B.kOf q) (B.psiOf q)

/-- The ledger's fit conditions at one width `n` (the per-call form of the load condition
`max{Ψ_i, Ψ_aux} ≤ c₀(n − k)`, P3:3106-3107, and of the class inequalities). `B.fits` gives it at `q(N)` past the
onset. -/
def TimeBudget.FitsAt {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (n : ℕ) : Prop :=
  Fits E n (B.lg n) (B.kOf n) (B.psiOf n)

/-- `tr:time`'s split of a weak machine's running time (P3:3797-3807): past the onset, the source work plus
`q(N)^{callDeg}` primitive calls, each within `callBudget`. -/
def TimeBudget.Split {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) (M : OrdinaryWeakMachine) : Prop :=
  ∀ N, B.onset ≤ N → M.runtime N ≤ B.A * (N + 1) ^ B.a + B.q N ^ E.callDeg * B.callBudget (B.q N)

/-- **`Runtime3`.** The weak machine's runtime split into the source-polynomial part and `q^callDeg` primitive
calls, each costed by the contracts; the ledger fits hold eventually along the machine's own schedule
`k = kOf (q N)`, `Ψ = psiOf (q N)`. -/
structure Runtime3 (M : OrdinaryWeakMachine) (kclk : ℕ) (E : Envelope) extends TimeBudget kclk E where
  split : toTimeBudget.Split M

/-- **`Runtime3` closes.** It gives the refuter's `o(T(N))` promise (P3:3808-3811). -/
theorem Runtime3.littleO {M : OrdinaryWeakMachine} {kclk : ℕ} {E : Envelope}
    (R : Runtime3 M kclk E) : OrdinaryLittleO M (fun n => n ^ (kclk + 2)) :=
  littleO_of_split M kclk R.A (4 * R.costs.coef) R.Ctab R.a R.d E.sigma R.q
    (fun N => R.q N ^ E.callDeg * R.costs.perCall (R.q N) (R.kOf (R.q N)) (R.psiOf (R.q N)))
    R.ha R.hsigma R.growth
    ⟨R.onset, fun N hN => ⟨R.split N hN,
      damp_calls E R.costs (R.q N) (R.lg (R.q N)) (R.kOf (R.q N)) (R.psiOf (R.q N)) (R.fits N hN),
      R.table N hN⟩⟩

/-! ## Counting lemmas: columns × per-column cost, before any machine

These turn a per-unit contract into its class bound; they are the arithmetic every C component cites. -/

/-! ## Satisfiability: the fit premises hold at a plausible instantiation

Envelope: sigma = 8, callDeg = 4, every other exponent 6, csel = 2, cpsi = 1.
Width q = 2^40 (lg = 40). Star width k = 4·(6+4+8)·40 = 2880, i.e. `r·s` with `s ≈ 40`,
`r = 72`. Load Ψ = q/2 (a stand-in for the `o(q)` load of `tr:load`). -/
def satEnvelope : Envelope :=
  { sigma := 8, callDeg := 4, Amain := 6, Atable := 6, Asel := 6, csel := 2, Apre := 6, cpsi := 1 }

end NearCubicWires.WireExponent3_5.Cost
