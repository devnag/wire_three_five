import Proof.Wire_3_5.Primitive.Writers.ThrSide8Base

/-! # PA2 c4 THR block, piece 6 part 9: the range and the request's numbers at a THR call

The THR twins of the SymHr and SymCost1-2 (RULING #167: plain THR twins on the mode-generic cores).
* **`hrange_thr`** (ThrEAt3's exact recovery range): `2^{m−1}·V_p(z) < 2^{Q'}` at `Q' = d_Q(k+L)`, `d_Q ≥ cST + 1`
  (alg:compiler, P3:1886-1890; samp:range, P3:2919-2921), through the generic `sampElim_lt`.
* `sT` (`⌊√(B_T L)⌋ + L² − L`, so that the SYM shape `U = (k+L)²(S+L)` is the THR load's `(k+L)²(⌊√(B_T L)⌋ + L²)`),
  `cmT` (`m ≤ c_m(k+L)`), `add_le_pow_add`, **`fix_numT`** (`fix_num` at `m ≤ c_m(k+L)`: the exponent
  `efOf (c_D + c_m)`), **`occ_numT`** (the occurrence count at `A ≤ 2^{A₁(k+L) + B·L²}`, `m ≤ c_m(k+L)`).
* **`thrFix_le`** (the THR request's fixed fields and displayed parameters below `2^{e_F}`), **`thrOcc_le`** (the
  charged occurrence count at every prefix below `2^{c_O U}`).

Paper quantities of the main types: the exact recovery range and the compiler input's size and `𝒮` at a THR child
request (P3:1886-1906, 3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC cDa one_le_L n2_le_L pow_mono_mul kL_le_U fix_num efOf coOf lt_pow_self' dense_length two_dRow_le n26_le bnOf sampElim_lt)

/-- **The THR load's square-root term, shifted**: `⌊√(B L)⌋ + L² − L`. -/
def sT (B L : ℕ) : ℕ := Nat.sqrt (B * L) + L * L - L

theorem sT_add (B L : ℕ) : sT B L + L = Nat.sqrt (B * L) + L * L := by
  unfold sT
  have := Nat.le_mul_self L
  omega

theorem add_le_pow_add {x y a b : ℕ} (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    x + y ≤ 2 ^ (a + b) := by
  have h1 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  rw [pow_add]
  generalize 2 ^ a = A at hx h1
  generalize 2 ^ b = B at hy h2
  nlinarith

/-- **The fixed fields and the displayed parameters below `2^{e_F}`** at `m ≤ c_m(k+L)` (the `fix_num` at
`m = 0`, plus the factor count at `2^{c_m U}`). -/
theorem fix_numT (K L S n cD cm dQ dD dH eH dP eP Qv Df Dl m h pr w dR cl dg Pex : ℕ)
    (hL1 : 1 ≤ L) (hn : n + 2 ≤ 2 ^ L) (hcD : 1 ≤ cD) (hcm : 1 ≤ cm)
    (hQ : Qv = dQ * (K + L)) (hDf : Df + 1 ≤ 2 ^ (K + cD * L)) (hDl : Dl ≤ 2 ^ (K + 26 * L + 5))
    (hm : m ≤ cm * (K + L)) (hh : h = dH * (n + 1) ^ eH) (hpr : pr = dP * (n + 1) ^ eP)
    (hw : w ≤ n + 1) (hdR : dR ≤ n + 1) (hcl : cl ≤ n + 1) (hdg : dg = dD * (S + L)) (hPex : Pex ≤ Df) :
    Qv + Df + Dl + m + h + pr + w + dR + cl + 1 + (pr + w + Pex + h + Qv + dg + 1) ≤
      2 ^ efOf (cD + cm) dQ dD dH eH dP eP ((K + L) * (K + L) * (S + L)) L := by
  have k0 := fix_num K L S n cD dQ dD dH eH dP eP Qv Df Dl 0 h pr w dR cl dg Pex hL1 hn hcD hQ hDf hDl
    (Nat.zero_le _) hh hpr hw hdR hcl hdg hPex
  have hKU := kL_le_U K L S hL1
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L) := ⟨_, rfl⟩
  rw [← hU] at k0 hKU ⊢
  have tm : m ≤ 2 ^ (cm * U) := by
    have : m ≤ cm * U := hm.trans (Nat.mul_le_mul_left _ hKU)
    exact this.trans (lt_pow_self' _)
  have e : efOf (cD + cm) dQ dD dH eH dP eP U L = efOf cD dQ dD dH eH dP eP U L + cm * U := by unfold efOf; ring
  have h1 : 1 ≤ efOf cD dQ dD dH eH dP eP U L := by unfold efOf; omega
  have h2 : 1 ≤ cm * U := Nat.mul_pos (by omega) (by omega)
  rw [e]
  have := add_le_pow_add k0 tm h1 h2
  omega

/-- **The charged occurrence count below `2^{c_O U}`** at `A ≤ 2^{A₁(k+L) + B·L²}`, `m ≤ c_m(k+L)`, `L² ≤ S + L`. -/
theorem occ_numT (K L S A1c B cm cD dQ dD Vl m Qv Df d : ℕ) (hL1 : 1 ≤ L) (hcD : 1 ≤ cD) (hLL : L * L ≤ S + L)
    (hV : Vl ≤ 2 ^ (A1c * (K + L) + B * (L * L))) (hm : m ≤ cm * (K + L)) (hQ : Qv = dQ * (K + L))
    (hDf : Df + 1 ≤ 2 ^ (K + cD * L)) (hd : d = dD * (S + L)) :
    max 1 Vl * 2 ^ m * (Qv * (Df + 1) ^ (Qv * d)) ≤
      2 ^ (coOf (A1c + B + cm) dQ cD dD * ((K + L) * (K + L) * (S + L))) := by
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L) := ⟨_, rfl⟩
  rw [← hU]
  have hKU : K + L ≤ U := by rw [hU]; exact kL_le_U K L S hL1
  have hLU : L * L ≤ U := by
    rw [hU]
    calc L * L ≤ S + L := hLL
      _ = 1 * 1 * (S + L) := by ring
      _ ≤ (K + L) * (K + L) * (S + L) := Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  have h1 : max 1 Vl ≤ 2 ^ (A1c * (K + L) + B * (L * L)) := max_le Nat.one_le_two_pow hV
  have h2 : 2 ^ m ≤ 2 ^ (cm * (K + L)) := Nat.pow_le_pow_right (by norm_num) hm
  have h3 : Qv ≤ 2 ^ (dQ * (K + L)) := by rw [hQ]; exact lt_pow_self' _
  have h4 : (Df + 1) ^ (Qv * d) ≤ 2 ^ ((Qv * d) * (K + cD * L)) := pow_mono_mul _ hDf
  have h5 : (Qv * d) * (K + cD * L) ≤ cD * dQ * dD * U := by
    have a1 : K + cD * L ≤ cD * (K + L) := by
      have := Nat.mul_le_mul_right K hcD
      have e : cD * (K + L) = cD * K + cD * L := by ring
      omega
    rw [hQ, hd, hU]
    calc dQ * (K + L) * (dD * (S + L)) * (K + cD * L) ≤ dQ * (K + L) * (dD * (S + L)) * (cD * (K + L)) :=
          Nat.mul_le_mul_left _ a1
      _ = cD * dQ * dD * ((K + L) * (K + L) * (S + L)) := by ring
  have h6 : A1c * (K + L) + B * (L * L) + cm * (K + L) + dQ * (K + L) ≤ (A1c + B + cm + 400 + dQ) * U := by
    have a1 : A1c * (K + L) ≤ A1c * U := Nat.mul_le_mul_left _ hKU
    have a2 : B * (L * L) ≤ B * U := Nat.mul_le_mul_left _ hLU
    have a3 : cm * (K + L) ≤ cm * U := Nat.mul_le_mul_left _ hKU
    have a4 : dQ * (K + L) ≤ dQ * U := Nat.mul_le_mul_left _ hKU
    have e : (A1c + B + cm + 400 + dQ) * U = A1c * U + B * U + cm * U + 400 * U + dQ * U := by ring
    omega
  have hE : 2 ^ (A1c * (K + L) + B * (L * L)) * 2 ^ (cm * (K + L)) * (2 ^ (dQ * (K + L)) * 2 ^ ((Qv * d) * (K + cD * L))) =
      2 ^ (A1c * (K + L) + B * (L * L) + cm * (K + L) + dQ * (K + L) + (Qv * d) * (K + cD * L)) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    ring
  calc max 1 Vl * 2 ^ m * (Qv * (Df + 1) ^ (Qv * d))
      ≤ 2 ^ (A1c * (K + L) + B * (L * L)) * 2 ^ (cm * (K + L)) * (2 ^ (dQ * (K + L)) * 2 ^ ((Qv * d) * (K + cD * L))) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (Nat.mul_le_mul h3 h4)
    _ = 2 ^ (A1c * (K + L) + B * (L * L) + cm * (K + L) + dQ * (K + L) + (Qv * d) * (K + cD * L)) := hE
    _ ≤ 2 ^ (coOf (A1c + B + cm) dQ cD dD * U) := by
        apply Nat.pow_le_pow_right (by norm_num)
        have e : coOf (A1c + B + cm) dQ cD dD * U = (A1c + B + cm + 400 + dQ) * U + cD * dQ * dD * U := by
          unfold coOf; ring
        omega

section Gate

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
