import Proof.Wire_3_5.Primitive.SeedFix.HbOdo

/-! # C4.Hb, machine part 16: the cells of the enumeration (`filt:soft`, P3:2253-2290)

"Expand each `A`-product into at most `2^{2t}` signed products of hash prefix indicators; for each product and each
`J_j`, the Gaussian-elimination machine counts [...] with at most `O(t)` equations" (P3:2262-2266). The Hb machine's
data (`HbX`): PA's HASH rows `F_{q,e}` (`Fs`, entry `q·nE + e`), the populations, the cleared weights' bits `W_λ`,
the sizes, the elimination's field and prefix, and the tape capacities. Its cell of counter value `c`: the row
`qOf c`, aux seed `eOf c`, population `pOf c`, level `lamOf c`, signs `γsOf c`, positions `ιsOf c` (mixed radix,
signs fastest); the cell's constraints (`consOfC`), elimination (`ggOf`) and printed word (**`cellWord`**); the
output before cell `c` (**`outAt`**). The odometer's word is the counter's low digit in binary (**`ctrWord_eq`**);
the machine's step is `c ↦ c + 1` (**`odo_next`**).

Paper quantity of the main type: the printed words `cellWord`, `outAt`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord)

/-- **The Hb machine's data.** -/
structure HbX where
  Fs : List (List (List ℕ))
  pops : List (Bool × List ℕ)
  Ws : List (List Bool)
  G : ℕ
  N2 : ℕ
  nE : ℕ
  J : ℕ
  T2 : ℕ
  ℓ : ℕ
  mod : ℕ
  plen : ℕ
  pfx : ℕ
  m : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  RV : ℕ
  cL : ℕ
  cE : ℕ
  cK : ℕ
  cC : ℕ
  cap : ℕ
  capL : ℕ

namespace HbX
variable (X : HbX)

/-- The odometer word's length and radix. -/
def L : ℕ := X.T2 + X.T2 * X.ℓ
def B : ℕ := 2 ^ X.L
def P : ℕ := X.pops.length
/-- The number of cells. -/
def n : ℕ := X.B * (X.J + 1) * X.P * X.nE * X.N2

def d0 (c : ℕ) : ℕ := c % X.B
def lamOf (c : ℕ) : ℕ := c / X.B % (X.J + 1)
def pOf (c : ℕ) : ℕ := c / X.B / (X.J + 1) % X.P
def eOf (c : ℕ) : ℕ := c / X.B / (X.J + 1) / X.P % X.nE
def qOf (c : ℕ) : ℕ := c / X.B / (X.J + 1) / X.P / X.nE % X.N2
def γsOf (c : ℕ) : List Bool := binary X.T2 (X.d0 c % 2 ^ X.T2)
def ιsOf (c : ℕ) : List ℕ := (List.range X.T2).map fun r => X.d0 c / 2 ^ X.T2 / 2 ^ (r * X.ℓ) % 2 ^ X.ℓ
def popOf (c : ℕ) : Bool × List ℕ := X.pops.getD (X.pOf c) (false, [])
def idxOf (c : ℕ) : ℕ := X.eOf c + X.qOf c * X.nE

/-- The cell's validity, constraints, width and elimination. -/
def validC (c : ℕ) : Bool := validB (X.popOf c).2.length (X.lamOf c) X.J (X.γsOf c) (X.ιsOf c)
def consOfC (c : ℕ) : List (ℕ × ℕ) := consL (X.lamOf c) X.J (X.γsOf c) (X.ιsOf c)
def kOfC (c : ℕ) : ℕ := kOfL (X.lamOf c) X.J
def ggOf (c : ℕ) : Bool × ℕ :=
  JoinElimination.gauss (X.T2 * X.ℓ - X.plen)
    (JoinElimination.system X.mod X.ℓ X.T2 (X.kOfC c) X.plen X.pfx (X.consOfC c))
def xOf (c : ℕ) : ℕ := X.T2 * X.ℓ - X.plen - (X.ggOf c).2

/-- The cell's term word. -/
def tbOf (c : ℕ) : List Bool :=
  termBits (X.lamOf c < X.J ∧ parZ (X.γsOf c) = 1) (X.xOf c) (X.Ws.getD (X.lamOf c) []) (X.Fs.getD (X.idxOf c) [])
    ((X.ιsOf c).flatMap fun i => zRec X.G (X.qOf c) (X.popOf c).1 ((X.popOf c).2.getD i 0))

/-- **The cell's printed word**: its term, when it is valid and its system consistent. -/
def cellWord (c : ℕ) : List Bool := if X.validC c = true ∧ (X.ggOf c).1 = true then X.tbOf c else []

/-- **The output before cell `c`.** -/
def outAt (c : ℕ) : List Bool := (List.range c).flatMap X.cellWord

theorem outAt_succ (c : ℕ) : X.outAt (c + 1) = X.outAt c ++ X.cellWord c := by
  simp [outAt, List.range_succ, List.flatMap_append]

end HbX

section Ctr

theorem binary_fields (ℓ : ℕ) : ∀ (k n : ℕ),
    binary (k * ℓ) n = ((List.range k).map fun r => binary ℓ (n / 2 ^ (r * ℓ) % 2 ^ ℓ)).flatten
  | 0, n => by simp [SignedSortKey.binary]
  | k + 1, n => by
    rw [show (k + 1) * ℓ = ℓ + k * ℓ by ring, binary_split', binary_fields ℓ k (n / 2 ^ ℓ)]
    rw [List.range_succ_eq_map, List.map_cons, List.flatten_cons, List.map_map]
    congr 1
    · simp only [Nat.zero_mul, pow_zero, Nat.div_one]; exact (binary_mod' ℓ n).symm
    · congr 1
      refine List.map_congr_left (fun r _ => ?_)
      simp only [Function.comp_apply]
      rw [Nat.div_div_eq_div_mul, ← pow_add, show ℓ + r * ℓ = (r + 1) * ℓ by ring]

theorem ctrWord_eq (X : HbX) (c : ℕ) : ctrWord (X.γsOf c) (X.ιsOf c) X.ℓ = binary X.L (X.d0 c) := by
  unfold ctrWord HbX.γsOf HbX.ιsOf HbX.L
  rw [binary_split', binary_mod', binary_fields X.ℓ X.T2 (X.d0 c / 2 ^ X.T2), List.map_map]
  rfl

end Ctr

section Next
variable (X : HbX)

theorem pos_of_lt_n (c : ℕ) (hc : c < X.n) : 0 < X.B ∧ 0 < X.J + 1 ∧ 0 < X.P ∧ 0 < X.nE ∧ 0 < X.N2 := by
  unfold HbX.n at hc
  refine ⟨Nat.pos_of_ne_zero ?_, by omega, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_⟩ <;>
    intro h <;> simp [h] at hc

theorem top_zero (c : ℕ) (hc : c < X.n) : c / X.B / (X.J + 1) / X.P / X.nE / X.N2 = 0 := by
  unfold HbX.n at hc
  simp only [Nat.div_div_eq_div_mul]
  exact Nat.div_eq_of_lt hc

theorem top_one (c : ℕ) (hc : c + 1 = X.n) : (c + 1) / X.B / (X.J + 1) / X.P / X.nE / X.N2 = 1 := by
  have hpos := pos_of_lt_n X c (by omega)
  simp only [Nat.div_div_eq_div_mul]
  rw [hc]; unfold HbX.n
  exact Nat.div_self (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hpos.1 hpos.2.1) hpos.2.2.1) hpos.2.2.2.1)
    hpos.2.2.2.2)

/-- **The machine's step is `c ↦ c + 1`**: the binary word's successor, and the counters' step on its carry. -/
theorem odo_next (c : ℕ) (hc : c < X.n) :
    binSucc (binary X.L (X.d0 c)) = binary X.L (X.d0 (c + 1)) ∧
    odoStep X.J X.P X.nE X.N2 (if lead (binary X.L (X.d0 c)) < X.L then 0 else 1)
      ⟨X.lamOf c, X.pOf c, X.eOf c, X.qOf c, 0⟩ =
      ⟨X.lamOf (c + 1), X.pOf (c + 1), X.eOf (c + 1), X.qOf (c + 1), if c + 1 = X.n then 1 else 0⟩ := by
  obtain ⟨hB, hJ, hP, hE, hN⟩ := pos_of_lt_n X c hc
  have hd0 : X.d0 c < 2 ^ X.L := Nat.mod_lt _ hB
  obtain ⟨hs1, hs2⟩ := binSucc_binary X.L (X.d0 c) hd0
  have k0 := digit_succ c 1 X.B hB le_rfl
  have c0e : (if lead (binary X.L (X.d0 c)) < X.L then 0 else 1) = (dstep 1 (c % X.B) X.B).2 := by
    unfold dstep; simp only [one_ne_zero, if_false]
    unfold HbX.d0 at hs2 ⊢; unfold HbX.B at *
    by_cases h : c % 2 ^ X.L + 1 < 2 ^ X.L
    · rw [if_pos (hs2.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hs2.mp h')), if_neg h]
  refine ⟨?_, ?_⟩
  · rw [hs1]; unfold HbX.d0; unfold HbX.B
    rw [Nat.add_mod (c % 2 ^ X.L) 1 (2 ^ X.L), Nat.mod_mod]
    rw [(Nat.add_mod c 1 (2 ^ X.L)).symm]
  · rw [c0e]
    set k1 := (dstep 1 (c % X.B) X.B).2
    have hk1 : k1 ≤ 1 := dstep_carry_le _ _ _
    have k1e := digit_succ (c / X.B) k1 (X.J + 1) hJ hk1
    set k2 := (dstep k1 (c / X.B % (X.J + 1)) (X.J + 1)).2
    have hk2 : k2 ≤ 1 := dstep_carry_le _ _ _
    have k2e := digit_succ (c / X.B / (X.J + 1)) k2 X.P hP hk2
    set k3 := (dstep k2 (c / X.B / (X.J + 1) % X.P) X.P).2
    have hk3 : k3 ≤ 1 := dstep_carry_le _ _ _
    have k3e := digit_succ (c / X.B / (X.J + 1) / X.P) k3 X.nE hE hk3
    set k4 := (dstep k3 (c / X.B / (X.J + 1) / X.P % X.nE) X.nE).2
    have hk4 : k4 ≤ 1 := dstep_carry_le _ _ _
    have k4e := digit_succ (c / X.B / (X.J + 1) / X.P / X.nE) k4 X.N2 hN hk4
    have q1 : (c + 1) / X.B = c / X.B + k1 := k0.2
    have q2 : (c + 1) / X.B / (X.J + 1) = c / X.B / (X.J + 1) + k2 := by rw [q1]; exact k1e.2
    have q3 : (c + 1) / X.B / (X.J + 1) / X.P = c / X.B / (X.J + 1) / X.P + k3 := by rw [q2]; exact k2e.2
    have q4 : (c + 1) / X.B / (X.J + 1) / X.P / X.nE = c / X.B / (X.J + 1) / X.P / X.nE + k4 := by
      rw [q3]; exact k3e.2
    have q5 : (c + 1) / X.B / (X.J + 1) / X.P / X.nE / X.N2 =
        c / X.B / (X.J + 1) / X.P / X.nE / X.N2 + (dstep k4 (c / X.B / (X.J + 1) / X.P / X.nE % X.N2) X.N2).2 := by
      rw [q4]; exact k4e.2
    rw [top_zero X c hc, Nat.zero_add] at q5
    unfold odoStep
    simp only [HbX.lamOf, HbX.pOf, HbX.eOf, HbX.qOf]
    congr 1
    · rw [q1]; exact k1e.1.symm
    · rw [q2]; exact k2e.1.symm
    · rw [q3]; exact k3e.1.symm
    · rw [q4]; exact k4e.1.symm
    · rw [← q5]
      by_cases h : c + 1 = X.n
      · rw [if_pos h, top_one X c h]
      · rw [if_neg h]
        apply Nat.div_eq_of_lt
        simp only [Nat.div_div_eq_div_mul]
        apply Nat.div_lt_of_lt_mul
        unfold HbX.n at hc h
        omega

end Next

end NearCubicWires.WireExponent3_5.PrimT.HbM
