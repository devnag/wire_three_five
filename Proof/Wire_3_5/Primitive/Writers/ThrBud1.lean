import Proof.Wire_3_5.Primitive.Writers.ThrB7Base
import Proof.Wire_3_5.Primitive.Writers.ThrBigS
import Proof.Wire_3_5.Primitive.SeedFix.C4BudEBase

/-! # c4 THR block, piece 8 part 1: the THR stage's steps within the seed-fixing budget (the arithmetic)

The THR twin of the C4Bud (`wrap_split`, `rest_le`, `budget_le`, generic): the THR setup's cost is the SYM setup's
at the data stage `n₃ + 1 + bigCost W c_h` (the THR data stage, then the hash bits) (**`thrSetup_eq`**); the strip's
C3 budget is the compiler writer's plus the strip's own steps (**`thrB_split`**); the hash bits' steps
(**`hbXCost_le`**), the THR numbers machine's (**`thrBig_le`**), the finisher's (**`fin_le`**) and the data word's
unary length (**`unary_le`**) are bounded; and **`thr_steps_core`**: every term at its rate, the stage's steps are
within `c₄·seedClasses E₄` (P3:3105-3115).

Paper quantity of the main type: the THR stage's steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrBud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)

/-- **The THR setup's cost is the SYM setup's** at the data stage `n₃ + 1 + bigCost W c_h`. -/
theorem thrSetup_eq (L : Lay) (w : List Bool) (n CL Cd Cc n3 ch : ℕ) (u : List Bool) (c ell d2 ρ B3 : ℕ) :
    ThrSet.setupT3Cost L w n CL Cd Cc n3 (2 ^ PrimT.C4Cap.capExp2 Cc n) ch u c ell d2 ρ B3 =
      PrimT.C4Cap.setupCost3 L w n CL Cd Cc (n3 + 1 + bigCost (2 ^ PrimT.C4Cap.capExp2 Cc n) ch) u c ell d2 ρ B3 := by
  unfold ThrSet.setupT3Cost PrimT.C4Cap.setupCost3 Lay.midCost ThrSet.cbCost
  omega

/-- **The strip's C3 budget** is the compiler writer's plus the strip's own steps. -/
theorem thrB_split (B cs pr wl h Q m : ℕ) : ThrStrip.thrB B cs pr wl h Q m = B + ThrStrip.thrB 0 cs pr wl h Q m := by
  unfold ThrStrip.thrB
  omega

/-- **The hash bits' steps** are quadratic in a bound `N` of their inputs. -/
theorem hbXCost_le (n a c Kb t hl L N : ℕ) (ha : a ≤ 4) (hc : c ≤ 4) (hn : n ≤ N) (hKb : Kb ≤ N) (ht : t ≤ N)
    (hhl : hl ≤ N) (hL : L ≤ N) : ThrHB.hbXCost n a c Kb t hl L ≤ 400 * ((N + 12) * (N + 12)) + 40000 := by
  have hbl : ∀ v, natBitLength v ≤ v + 1 := fun v => Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hna : natBitLength a ≤ 5 := by have := hbl a; omega
  have hnc : natBitLength c ≤ 5 := by have := hbl c; omega
  have hnn := hbl n
  have ha2 : 2 ^ natBitLength a ≤ 32 := le_trans (Nat.pow_le_pow_right (by norm_num) hna) (by norm_num)
  have hc2 : 2 ^ natBitLength c ≤ 32 := le_trans (Nat.pow_le_pow_right (by norm_num) hnc) (by norm_num)
  have t1 : (natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40) ≤ 7 * 1320 := Nat.mul_le_mul (by omega) (by omega)
  have t2 : (natBitLength c + 2) * (40 * 2 ^ natBitLength c + 40) ≤ 7 * 1320 := Nat.mul_le_mul (by omega) (by omega)
  have t3 : a * (20 * Kb + 20 + 4) ≤ 4 * (20 * N + 24) := Nat.mul_le_mul ha (by omega)
  have t4 : c * (20 * Kb + 20 + 4) ≤ 4 * (20 * N + 24) := Nat.mul_le_mul hc (by omega)
  have t5 : (t + 12) * (300 * t + 300) ≤ 300 * ((N + 12) * (N + 12)) := by nlinarith
  have t6 : 24 * N ≤ (N + 12) * (N + 12) := by nlinarith
  unfold ThrHB.hbXCost
  omega

/-- **The THR numbers machine's steps**: quadratic in the capacity, plus the free program's. -/
theorem thrBig_le (cap n a nc Kb fc : ℕ) (hn : n ≤ cap) (ha : a ≤ 4) (hnc : nc ≤ 4) (hK : Kb ≤ cap) :
    ThrCap.thrBigCost cap n a nc Kb fc ≤ 300000 * ((cap + 2) * (cap + 2)) + fc := by
  have r1 := SymSizes.reqParseCost_le n a nc Kb cap hn ha hnc hK
  have hsq : UnaryPow.sq cap = 200 * ((cap + 2) * (cap + 2)) := by unfold UnaryPow.sq; ring
  unfold ThrCap.thrBigCost ThrNums.numsTCost ThrNums.p1TCost
  rw [hsq]
  have hg : 4 ≤ (cap + 2) * (cap + 2) := by nlinarith
  omega

/-- **The THR finisher's steps**: the sample expansion and the append. -/
theorem fin_le (P : Sampler.SeedParams) (s : Fin (8 * P.ell) → Bool) (hbF : List Bool) :
    ThrFin.finCost P s hbF ≤ 1048576 * (P.Q + 1) * 2 ^ (4 * P.ell) + 4 * (P.Q * (5 * P.kh + 5)) +
      16 * hbF.length + 12 := by
  have h1 := samp_le P
  have h2 : (PrimT.C4Iface.seedPairs P s).length = P.Q := List.length_ofFn
  unfold ThrFin.finCost ThrFin.faCost
  rw [h2]
  have e : 2 * P.Q * (5 * P.kh + 5) = 2 * (P.Q * (5 * P.kh + 5)) := by ring
  omega

/-- **The data word's unary length** at entries below `M`. -/
theorem unary_le (cs : List ℕ) (M : ℕ) (h : ∀ v ∈ cs, v + 1 ≤ M) : (Data.unaryList cs).length ≤ cs.length * M :=
  CallSize.flatMap_length_le _ _ _ (fun v hv => by
    rw [List.length_append, List.length_replicate, List.length_singleton]
    exact h v hv)

/-- **The THR stage's steps within the seed-fixing budget** (generic in the terms' values): the front, the data
stage and the hash bits, the counts, the numbers machine, the modulus searches, the center bits, the pad's exponent,
the finisher and the strip's own steps at their rates, the compiler writer within its class. -/
theorem thr_steps_core (E₄ EW : Envelope) (L : Lay) (w : List Bool) (n CL Cd Cc n3 ch : ℕ) (u : List Bool)
    (c ell d2 ρ Bc Y nf k psi : ℕ) (Fm : PrimT.C4Loop.ChildFam) (cW Kp Dp K0 K1 K2 KF KN KH KU KC Kl Kq KR KS KP : ℕ)
    (hcell : Fm.cellCost + 1 ≤ 2 ^ ρ) (hb : Fm.bound ≤ 8 * ell)
    (hF : PrimT.C4Cap.frontCost3 L w n CL Cd Cc ≤ KF * 2 ^ (n / 8)) (hN : n3 ≤ KN * 2 ^ (n / 8))
    (hH : ch ≤ KH * 2 ^ (n / 8)) (hU : u.length ≤ KU * 2 ^ (n / 8)) (hc : c ≤ KC * 2 ^ (3 * (n / 8)))
    (hl : 2 ^ (3 * ell) ≤ Kl * 2 ^ (n / 8)) (hρx : ρ ≤ KR * 2 ^ (n / 8)) (hs : nf ≤ KS * 2 ^ (n / 8))
    (hY : Y ≤ KP * 2 ^ (n / 8)) (hn : 1 ≤ n) (hk : k ≤ n / 16 + K0) (hkn : k ≤ n) (hlin : ell ≤ Kq * (n + 1))
    (hd2 : d2 ≤ n - k + 1)
    (hρ : 2 ^ ρ ≤ Kp * (2 ^ (n - k) * (n + 1) ^ Dp + 2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2)))
    (hK1 : Dp * (natBitLength n + 1) ^ 2 ≤ n / 16 + K1) (hK2 : n + 1 ≤ 2 ^ (n / 8 + K2))
    (hB3 : Bc ≤ cW * classBound EW .preprocessing n k psi)
    (hEc : EW.cpsi ≤ E₄.cpsi) (hEa : EW.Apre ≤ E₄.Apre) (hAt : Dp + 1 ≤ E₄.Atable) :
    wrapCost (ThrSet.setupT3Cost L w n CL Cd Cc n3 (2 ^ PrimT.C4Cap.capExp2 Cc n) ch u c ell d2 ρ (Bc + Y)) Fm
        (2 ^ ρ) nf + 1 ≤
      (2 ^ (Nat.clog 2 (KF + (KN + 2 * KH + 22 * 2 ^ Cc + 49) + 34 * KU + 22 * 2 ^ Cc + 2 * KC + 600 * Kl +
        40 * 2 ^ K2 + 40 * KR + KS + KP + 400) + K0) +
        (32 * Kq + 34) * ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + K2 + 1)) + cW) * seedClasses E₄ n k psi := by
  have hW : 2 ^ PrimT.C4Cap.capExp2 Cc n = 2 ^ Cc * 2 ^ (n / 8) := by
    unfold PrimT.C4Cap.capExp2; rw [pow_add, mul_comm]
  have hX : 1 ≤ 2 ^ (n / 8) := Nat.one_le_two_pow
  have hD : n3 + 1 + bigCost (2 ^ PrimT.C4Cap.capExp2 Cc n) ch ≤ (KN + 2 * KH + 22 * 2 ^ Cc + 49) * 2 ^ (n / 8) := by
    unfold bigCost
    rw [hW]
    have e : (KN + 2 * KH + 22 * 2 ^ Cc + 49) * 2 ^ (n / 8) = KN * 2 ^ (n / 8) + 2 * (KH * 2 ^ (n / 8)) +
        22 * (2 ^ Cc * 2 ^ (n / 8)) + 49 * 2 ^ (n / 8) := by ring
    omega
  have hd2x : d2 ≤ 2 ^ K2 * 2 ^ (n / 8) := by
    have e : 2 ^ (n / 8 + K2) = 2 ^ K2 * 2 ^ (n / 8) := by rw [pow_add, mul_comm]
    omega
  have hR := rest_le L w n CL Cd Cc _ u c ell d2 ρ nf Y KF (KN + 2 * KH + 22 * 2 ^ Cc + 49) KU KC Kl (2 ^ K2) KR KS KP
    hF hD hU hc hl hd2x hρx hs hY
  have hws := wrap_split L w n CL Cd Cc (n3 + 1 + bigCost (2 ^ PrimT.C4Cap.capExp2 Cc n) ch) u c ell d2 ρ (Bc + Y) Fm
    nf 0 hcell hb
  rw [← thrSetup_eq] at hws
  refine budget_le E₄ EW n k psi _ _ ell d2 ρ Bc _ K0 Kq Kp Dp K1 K2 cW hn ?_ hR hk hkn hlin hd2 hρ hK1 hK2 hB3 hEc
    hEa hAt
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.ThrBud
