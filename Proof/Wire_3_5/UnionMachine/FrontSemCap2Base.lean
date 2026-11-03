import Proof.Wire_3_5.UnionMachine.FrontSemCap1Base
import Proof.Wire_3_5.UnionMachine.FrontSemPOBase

/-! # C6 front, the semantic core (13): the table writer's bounds at a guess (P3:3485-3491, 3669-3691)

From a guess's size envelope `GEnv g Λ K`: the table writer's data fits **`BK K`** (**`bnd_of`**: the head, the
translation, the constant, the parity and carrier codes, the entries, the flag strings), the PCPP output word fits
`BK K` (**`po_len`**), and the numbers' capacities fit **`PW K`** (**`numCap_le`**, **`thrCap_le`**).

Paper quantity of the main types: the table writer's data and the PCPP output at a guess, against the width. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap2
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires.SourceInterfaces (Literal)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (frItems)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt (entOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1 (natWord_le natWord_bits frame_len flatMap_le)

/-- The data bound. -/
def BK (K : ℕ) : ℕ := 64 * (K + 1) ^ 3

/-- The numbers' bound. -/
def PW (K : ℕ) : ℕ := 1024 * (K + 1) ^ 9

theorem pow2_bits (x : ℕ) : 2 ^ (natBitLength x + 1) ≤ 4 * x + 4 := by
  have := C1Cnt.pow_nbl_le x; rw [pow_succ]; omega

theorem bits_le (x : ℕ) : natBitLength x ≤ 2 * x + 2 :=
  (Nat.lt_two_pow_self (n := natBitLength x)).le.trans (C1Cnt.pow_nbl_le x)

theorem literalIndex_lt {n : ℕ} (l : Literal n) : literalIndex l < 2 * n := by
  cases l with
  | positive i => have := i.isLt; show 2 * i.val < 2 * n; omega
  | negative i => have := i.isLt; show 2 * i.val + 1 < 2 * n; omega

theorem mem_pairsOf_lt {M m : ℕ} (a b : Fin M → ℕ) (ha : ∀ j, a j < m) (hb : ∀ j, b j < m) :
    ∀ x ∈ pairsOf a b, x < m := by
  intro x hx
  unfold pairsOf at hx
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hx
  rcases List.mem_cons.1 hj with e | hj'
  · rw [e]; exact ha j
  · rw [List.mem_singleton.1 hj']; exact hb j

theorem frItems_le (ws : List (List Bool)) (k : ℕ) (h : ∀ w ∈ ws, w.length ≤ k) :
    (frItems ws).length ≤ ws.length * (2 * k + 1) := by
  unfold frItems
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, frame_len]
    have h1 := h w (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    rw [Nat.add_mul, one_mul]; omega

theorem entsW_le (es : List (Bool × Bool × ℕ)) (k : ℕ) (h : ∀ e ∈ es, (natWord e.2.2).length ≤ k) :
    (entsW es).length ≤ es.length * (k + 4) := by
  unfold entsW
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, entW]
    have h1 := h e (by simp)
    have h2 := ih (fun v hv => h v (by simp [hv]))
    simp only [List.length_cons, List.length_nil] at *
    rw [Nat.add_mul, one_mul]; omega

theorem bk_hd (K : ℕ) : 2 * (2 * K + 15) + 1 ≤ BK K := by unfold BK; ring_nf; omega
theorem bk_tl (K : ℕ) : 2 * K + 1 ≤ BK K := by unfold BK; ring_nf; omega
theorem bk_pc (K : ℕ) : K * (2 * K + 1) ≤ BK K := by unfold BK; ring_nf; omega
theorem bk_cr (K : ℕ) : K * (2 * (2 * K + 1) + 1) ≤ BK K := by unfold BK; ring_nf; omega
theorem bk_es (K : ℕ) : K * K * (K + 4) ≤ BK K := by unfold BK; ring_nf; omega
theorem bk_df (K : ℕ) : K * K ≤ BK K := by unfold BK; ring_nf; omega
theorem bk_po (K : ℕ) : 9 + 3 * (2 * K + 3) + K * K + (4 * K + 3) + (8 * (K * K) + 6 * K) ≤ BK K := by
  unfold BK; ring_nf; omega

section Env

end Env

/-- **The magnitudes' capacity** at `K`. -/
theorem numCap_le (s Λ q sys aux cb K : ℕ) (hs : s ≤ K) (hΛ : Λ ≤ K) (hq : q ≤ K) (hsy : sys ≤ K) (hau : aux ≤ K)
    (hcb : cb ≤ K) (hc2 : 2 ^ cb ≤ K) : numCap s Λ q sys aux cb ≤ PW K := by
  unfold numCap
  rw [pow_succ]
  generalize 2 ^ cb = M at hc2
  calc s + q + sys + aux + cb + Λ + 2 + sys * q + M * 2 + sys * s + aux * s + s * s + s * s * s + s * s * s * s +
        Λ * Λ + Λ * Λ * Λ + Λ * Λ * Λ * Λ + Λ * Λ * (s * s) + 2 * (Λ * (s * s * s)) + 2 * (Λ * Λ * Λ * s)
      ≤ K + K + K + K + K + K + 2 + K * K + K * 2 + K * K + K * K + K * K + K * K * K + K * K * K * K +
        K * K + K * K * K + K * K * K * K + K * K * (K * K) + 2 * (K * (K * K * K)) + 2 * (K * K * K * K) := by
          gcongr
    _ ≤ PW K := by unfold PW; ring_nf; omega

/-- **The threshold's capacity** at `K`. -/
theorem thrCap_le (S4 p M Λ aV bV aT bT K : ℕ) (hS : S4 ≤ K * K * K * K) (hp : 2 ^ p ≤ 4 * K + 4) (hM : M ≤ K)
    (hΛ : Λ ≤ K) (h1 : aV ≤ K) (h2 : bV ≤ K) (h3 : aT ≤ K) (h4 : bT ≤ K) :
    thrCap S4 p M Λ aV bV aT bT ≤ PW K := by
  unfold thrCap
  rw [pow_succ]
  generalize 2 ^ p = t at hp
  calc S4 + M + Λ + 2 + t * 2 + S4 * t + (Λ + 1) * (Λ + 1) + (Λ + 1) * (Λ + 1) * ((Λ + 1) * (Λ + 1)) +
        S4 * M + 2 * (S4 * M * ((Λ + 1) * (Λ + 1) * ((Λ + 1) * (Λ + 1)))) + 2 * (S4 * t * M) + 4 * aV + bV + aT +
        bT + S4 * t * M * (4 * aV) + S4 * t * M * (2 * aV) + S4 * t * M * aT
      ≤ K * K * K * K + K + K + 2 + (4 * K + 4) * 2 + K * K * K * K * (4 * K + 4) + (K + 1) * (K + 1) +
        (K + 1) * (K + 1) * ((K + 1) * (K + 1)) + K * K * K * K * K +
        2 * (K * K * K * K * K * ((K + 1) * (K + 1) * ((K + 1) * (K + 1)))) +
        2 * (K * K * K * K * (4 * K + 4) * K) + 4 * K + K + K + K +
        K * K * K * K * (4 * K + 4) * K * (4 * K) + K * K * K * K * (4 * K + 4) * K * (2 * K) +
        K * K * K * K * (4 * K + 4) * K * K := by
          gcongr
    _ ≤ PW K := by unfold PW; ring_nf; omega

theorem bnd_mono {d : TWData} {B B' : ℕ} (h : d.Bnd B) (hB : B ≤ B') : d.Bnd B' :=
  ⟨h.hd.trans hB, h.tl.trans hB, h.cc.trans hB, h.pc.trans hB, h.cr.trans hB, h.es.trans hB, h.df.trans hB,
    h.pf.trans hB, h.ef.trans hB⟩

theorem pw_small (K : ℕ) : 4 * (K * K) + 16 * K + 32 ≤ PW K := by unfold PW; ring_nf; omega

section Caps

end Caps

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap2
