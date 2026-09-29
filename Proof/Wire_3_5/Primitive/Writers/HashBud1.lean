import Proof.Wire_3_5.Primitive.Writers.ThrBud1
import Proof.Wire_3_5.Primitive.Writers.HashN2

/-! # c4 HASH budget (C), part 1: the HASH stage's steps within the seed-fixing budget (the arithmetic)

P3:3098-3100, 3105-3115 (the seed phase's steps within `c₄·seedClasses E₄`, `E₄` before `F`, `c₄` after): the HASH
twin of `ThrBud.thr_steps_core`. The HASH setup `M0H`'s cost (`setupH_run`'s `c0` bound) is the THR setup's
`setupT3Cost` plus the two front copies, the data stage's re-run and copy-in, the cell (`HashCell.callCost`), the kept
words writer and the `1^{Q'}` copy; the HASH loop's family bound is `s_h = 2tℓ₀` (not the setup's modulus length),
so the loop's split carries its own linear bound `L_b ≥ ℓ` (**`wrap_splitH`**); the HASH numbers machine is quadratic
in the capacity (**`hashBig_le`**); and **`hash_steps_core`**: every term at its rate (the cell and the writer at any
rate `≤ 7`), the HASH stage's steps are within `c₄·seedClasses E₄`.

Paper quantity of the main type: the HASH stage's steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashBud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost loopZCost loopCost)

/-- **The HASH stage's steps, split** (the loop's bound `L_b` separate from the setup's modulus length `ℓ`). -/
theorem wrap_splitH (L : Lay) (w : List Bool) (n CL Cd Cc cD : ℕ) (u : List Bool) (c ell d2 ρ B3 : ℕ)
    (Fm : PrimT.C4Loop.ChildFam) (samp P Lb : ℕ) (hcell : Fm.cellCost + 1 ≤ 2 ^ ρ) (hb : Fm.bound ≤ 8 * Lb) :
    wrapCost (PrimT.C4Cap.setupCost3 L w n CL Cd Cc cD u c ell d2 ρ B3) Fm (2 ^ ρ) samp + 1 + P + 20 ≤
      (PrimT.C4Cap.frontCost3 L w n CL Cd Cc + Lay.midCost cD u (2 ^ PrimT.C4Cap.capExp2 Cc n) c +
        2 * PrimAsm.Modulus.modCost ell + 40 * (d2 + ρ) + 80 * ell + samp + (P + 80 * Lb) + 300) +
      (32 * Lb + 34) * (2 ^ d2 + 2 ^ ρ) + B3 := by
  unfold wrapCost PrimT.C4Cap.setupCost3 Lay.tailCost Lay.modsCost srcCost loopZCost loopCost
  have h1 : Fm.bound * (2 * Fm.cellCost + 2 + 1 + (2 * 2 ^ ρ + 4) + 3) ≤ 8 * Lb * (4 * 2 ^ ρ + 10) :=
    Nat.mul_le_mul hb (by omega)
  have h2 : 8 * Lb * (4 * 2 ^ ρ + 10) = 32 * Lb * 2 ^ ρ + 80 * Lb := by ring
  have h3 : (32 * Lb + 34) * (2 ^ d2 + 2 ^ ρ) = 32 * Lb * 2 ^ d2 + 34 * 2 ^ d2 + 32 * Lb * 2 ^ ρ + 34 * 2 ^ ρ := by
    ring
  have h4 : 0 ≤ 32 * Lb * 2 ^ d2 := Nat.zero_le _
  omega

/-- **The HASH numbers machine's steps**: quadratic in the capacity, plus the free program's. -/
theorem hashBig_le (cap n a nc Kb t fc : ℕ) (hn : n ≤ cap) (ha : a ≤ 4) (hnc : nc ≤ 4) (hK : Kb ≤ cap)
    (ht : t ≤ cap) : ThrNums.hashBigCost cap n a nc Kb t fc ≤ 3000000 * ((cap + 2) * (cap + 2)) + fc := by
  have r1 := SymSizes.reqParseCost_le n a nc Kb cap hn ha hnc hK
  have hsq : UnaryPow.sq cap = 200 * ((cap + 2) * (cap + 2)) := by unfold UnaryPow.sq; ring
  unfold ThrNums.hashBigCost ThrNums.numsTCost ThrNums.p1TCost
  rw [hsq]
  have hg : 4 ≤ (cap + 2) * (cap + 2) := by nlinarith
  have hg2 : cap ≤ (cap + 2) * (cap + 2) := by nlinarith
  omega

/-- **The HASH stage's steps, split into the rate part and the loop part.** -/
theorem hash_total (L : Lay) (w : List Bool) (n CL Cd Cc n3 ch : ℕ) (u : List Bool) (c ell d2 ρ B3 nf Lb : ℕ)
    (Fm : PrimT.C4Loop.ChildFam) (pre cpz cc wk qc : ℕ) (hcell : Fm.cellCost + 1 ≤ 2 ^ ρ) (hb : Fm.bound ≤ 8 * Lb) :
    wrapCost (ThrSet.setupT3Cost L w n CL Cd Cc n3 (2 ^ PrimT.C4Cap.capExp2 Cc n) ch u c ell d2 ρ B3 + 1 +
        (PrimT.C4Cap.frontCost3 L w n CL Cd Cc + 1 + (PrimT.C4Cap.frontCost3 L w n CL Cd Cc + 1 +
          (n3 + 1 + cpz + 1 + (cc + 1 + (wk + 1 + qc))))) + 1 + (2 * pre + 2 + 1 + (2 * 2 ^ ρ + 4))) Fm (2 ^ ρ) nf + 1 ≤
      ((PrimT.C4Cap.frontCost3 L w n CL Cd Cc +
          Lay.midCost (n3 + 1 + bigCost (2 ^ PrimT.C4Cap.capExp2 Cc n) ch) u (2 ^ PrimT.C4Cap.capExp2 Cc n) c +
          2 * PrimAsm.Modulus.modCost ell + 40 * (d2 + ρ) + 80 * ell + nf +
          (2 * PrimT.C4Cap.frontCost3 L w n CL Cd Cc + n3 + (2 * pre + cpz + qc) + 80 * Lb) + 300) + (cc + wk)) +
        (32 * (Lb + 1) + 34) * (2 ^ d2 + 2 ^ ρ) + B3 := by
  have hws := wrap_splitH L w n CL Cd Cc (n3 + 1 + bigCost (2 ^ PrimT.C4Cap.capExp2 Cc n) ch) u c ell d2 ρ B3 Fm
    nf (2 * PrimT.C4Cap.frontCost3 L w n CL Cd Cc + n3 + (2 * pre + cpz + qc)) Lb hcell hb
  rw [← ThrBud.thrSetup_eq] at hws
  obtain ⟨S0, hS0⟩ : ∃ x, x = ThrSet.setupT3Cost L w n CL Cd Cc n3 (2 ^ PrimT.C4Cap.capExp2 Cc n) ch u c ell d2 ρ B3 :=
    ⟨_, rfl⟩
  obtain ⟨Fr, hFr⟩ : ∃ x, x = PrimT.C4Cap.frontCost3 L w n CL Cd Cc := ⟨_, rfl⟩
  obtain ⟨Md, hMd⟩ : ∃ x, x = Lay.midCost (n3 + 1 + bigCost (2 ^ PrimT.C4Cap.capExp2 Cc n) ch) u
      (2 ^ PrimT.C4Cap.capExp2 Cc n) c := ⟨_, rfl⟩
  obtain ⟨Mo, hMo⟩ : ∃ x, x = PrimAsm.Modulus.modCost ell := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ x, x = loopZCost Fm (2 ^ ρ) := ⟨_, rfl⟩
  rw [← hS0, ← hFr, ← hMd, ← hMo] at hws ⊢
  unfold wrapCost at hws ⊢
  rw [← hLz] at hws ⊢
  have e1 : (32 * (Lb + 1) + 34) * (2 ^ d2 + 2 ^ ρ) = (32 * Lb + 34) * (2 ^ d2 + 2 ^ ρ) + 32 * 2 ^ d2 + 32 * 2 ^ ρ := by
    ring
  have hd1 : 1 ≤ 2 ^ d2 := Nat.one_le_two_pow
  omega

/-- **The HASH stage's steps within the seed-fixing budget** (generic in the terms' values): the THR setup's terms at
their rates (front, data stage, hash bits, counts, numbers machine, modulus searches, pad's exponent, finisher), the
setup's rate-1 extras (the front copies, the pre-loop stage, the copy-in, the `1^{Q'}` copy), the cell and the kept
words writer at rate `≤ 7`, the loop's bound `L_b ≥ ℓ` linear in `n`, the compiler writer within its class. -/
theorem hash_steps_core (E₄ EW : Envelope) (L : Lay) (w : List Bool) (n CL Cd Cc n3 ch : ℕ) (u : List Bool)
    (c ell d2 ρ B3 nf k psi Lb : ℕ) (Fm : PrimT.C4Loop.ChildFam) (pre cpz cc wk qc : ℕ)
    (cW Kp Dp K0 K1 K2 Kl KF KN KH KU KC KL KR KS KP cX : ℕ)
    (hcell : Fm.cellCost + 1 ≤ 2 ^ ρ) (hb : Fm.bound ≤ 8 * Lb)
    (hF : PrimT.C4Cap.frontCost3 L w n CL Cd Cc ≤ KF * 2 ^ (n / 8)) (hN : n3 ≤ KN * 2 ^ (n / 8))
    (hH : ch ≤ KH * 2 ^ (n / 8)) (hU : u.length ≤ KU * 2 ^ (n / 8)) (hc : c ≤ KC * 2 ^ (3 * (n / 8)))
    (hl : 2 ^ (3 * ell) ≤ KL * 2 ^ (n / 8)) (hρx : ρ ≤ KR * 2 ^ (n / 8)) (hs : nf ≤ KS * 2 ^ (n / 8))
    (hP : 2 * pre + cpz + qc ≤ KP * 2 ^ (n / 8)) (hX : Ex n 7 cX (cc + wk))
    (hn : 1 ≤ n) (hk : k ≤ n / 16 + K0) (hkn : k ≤ n) (hlin : Lb ≤ Kl * (n + 1)) (hd2 : d2 ≤ n - k + 1)
    (hρ : 2 ^ ρ ≤ Kp * (2 ^ (n - k) * (n + 1) ^ Dp + 2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2)))
    (hK1 : Dp * (natBitLength n + 1) ^ 2 ≤ n / 16 + K1) (hK2 : n + 1 ≤ 2 ^ (n / 8 + K2))
    (hB3 : B3 ≤ cW * classBound EW .preprocessing n k psi)
    (hEc : EW.cpsi ≤ E₄.cpsi) (hEa : EW.Apre ≤ E₄.Apre) (hAt : Dp + 1 ≤ E₄.Atable) :
    wrapCost (ThrSet.setupT3Cost L w n CL Cd Cc n3 (2 ^ PrimT.C4Cap.capExp2 Cc n) ch u c ell d2 ρ B3 + 1 +
        (PrimT.C4Cap.frontCost3 L w n CL Cd Cc + 1 + (PrimT.C4Cap.frontCost3 L w n CL Cd Cc + 1 +
          (n3 + 1 + cpz + 1 + (cc + 1 + (wk + 1 + qc))))) + 1 + (2 * pre + 2 + 1 + (2 * 2 ^ ρ + 4))) Fm (2 ^ ρ) nf + 1 ≤
      (2 ^ (Nat.clog 2 (KF + (KN + 2 * KH + 22 * 2 ^ Cc + 49) + 34 * KU + 22 * 2 ^ Cc + 2 * KC + 600 * KL +
        40 * 2 ^ K2 + 40 * KR + KS + (2 * KF + KN + KP + 80 * Kl * 2 ^ K2) + 400) + cX + 1 + K0) +
        (32 * (Kl + 1) + 34) * ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + K2 + 1)) + cW) *
        seedClasses E₄ n k psi := by
  have hW : 2 ^ PrimT.C4Cap.capExp2 Cc n = 2 ^ Cc * 2 ^ (n / 8) := by
    unfold PrimT.C4Cap.capExp2; rw [pow_add, mul_comm]
  have hX1 : 1 ≤ 2 ^ (n / 8) := Nat.one_le_two_pow
  have e8 : 2 ^ (n / 8 + K2) = 2 ^ K2 * 2 ^ (n / 8) := by rw [pow_add, mul_comm]
  have hD : n3 + 1 + bigCost (2 ^ PrimT.C4Cap.capExp2 Cc n) ch ≤ (KN + 2 * KH + 22 * 2 ^ Cc + 49) * 2 ^ (n / 8) := by
    unfold bigCost
    rw [hW]
    have e : (KN + 2 * KH + 22 * 2 ^ Cc + 49) * 2 ^ (n / 8) = KN * 2 ^ (n / 8) + 2 * (KH * 2 ^ (n / 8)) +
        22 * (2 ^ Cc * 2 ^ (n / 8)) + 49 * 2 ^ (n / 8) := by ring
    omega
  have hd2x : d2 ≤ 2 ^ K2 * 2 ^ (n / 8) := by omega
  have hLb : 80 * Lb ≤ 80 * Kl * 2 ^ K2 * 2 ^ (n / 8) := by
    have h1 : Kl * (n + 1) ≤ Kl * (2 ^ K2 * 2 ^ (n / 8)) := Nat.mul_le_mul_left _ (by omega)
    have e2 : 80 * Kl * 2 ^ K2 * 2 ^ (n / 8) = 80 * (Kl * (2 ^ K2 * 2 ^ (n / 8))) := by ring
    omega
  have hPP : 2 * PrimT.C4Cap.frontCost3 L w n CL Cd Cc + n3 + (2 * pre + cpz + qc) + 80 * Lb ≤
      (2 * KF + KN + KP + 80 * Kl * 2 ^ K2) * 2 ^ (n / 8) := by
    have e : (2 * KF + KN + KP + 80 * Kl * 2 ^ K2) * 2 ^ (n / 8) = 2 * (KF * 2 ^ (n / 8)) + KN * 2 ^ (n / 8) +
        KP * 2 ^ (n / 8) + 80 * Kl * 2 ^ K2 * 2 ^ (n / 8) := by ring
    omega
  have hR := rest_le L w n CL Cd Cc _ u c ell d2 ρ nf
    (2 * PrimT.C4Cap.frontCost3 L w n CL Cd Cc + n3 + (2 * pre + cpz + qc) + 80 * Lb)
    KF (KN + 2 * KH + 22 * 2 ^ Cc + 49) KU KC KL (2 ^ K2) KR KS (2 * KF + KN + KP + 80 * Kl * 2 ^ K2)
    hF hD hU hc hl hd2x hρx hs hPP
  have hR2 := ex_add hR hX
  have hlin2 : Lb + 1 ≤ (Kl + 1) * (n + 1) := by
    have e : (Kl + 1) * (n + 1) = Kl * (n + 1) + (n + 1) := by ring
    omega
  exact budget_le E₄ EW n k psi _ _ (Lb + 1) d2 ρ B3 _ K0 (Kl + 1) Kp Dp K1 K2 cW hn
    (hash_total L w n CL Cd Cc n3 ch u c ell d2 ρ B3 nf Lb Fm pre cpz cc wk qc hcell hb) hR2 hk hkn hlin2 hd2 hρ hK1
    hK2 hB3 hEc hEa hAt

end NearCubicWires.WireExponent3_5.PrimAsm.HashBud
