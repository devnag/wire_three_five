import Proof.Wire_3_5.Foundations.OutMachineCarPipe

/-! # The output machine carrier phase, part 7: the bound `T`

"This takes polynomial time" (P3:3175-3178). The masked stages' costs, below one power of the input's length:

* `blocks_le`, **`setup_le`** (PA's setup cost, linear in `N`, `n`, `L`), **`carCostB_le`** (the table fuel,
  `carTableCost_poly`: degree `76`), **`m1_le`**;
* `CcT` (the fuel coefficient), `Kb`, **`DtC`** (`1976 + log₂ Kb + 1`, an irreducible constant);
* **`T_bounds`**: at `T = (N + 2)^{DtC}`, both masked stages' needs (`carPipe`'s `hT1`, `hT2`) hold;
* **`caps`**, **`T_le_cap`**: the capacity `2^{Dt}·(N + 1)^{Dt}` holds every stage;
* **`pipe_le`**, **`T_le_Cs`**: the pipeline's steps and its residues' lengths within `CsOf Dt·(N + 1)^{2·Dt}`.

Paper quantity of the main type: the carrier phase's running time as a power of the input's length (P3:3175-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1 NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarS

theorem slot_le (x n L : ℕ) : slotCost x n L ≤ 70 * (RepairRepresentation.natWord x).length + 18 * n + 18 * L + 75 := by
  unfold slotCost; omega

theorem blocks_le (n L B : ℕ) : ∀ (trips : List Trip) (cs : List ℕ), (∀ x ∈ cs, slotCost x n L ≤ B) →
    blocksCost n L trips cs ≤ trips.length * (B + 2)
  | [], _, _ => by simp [blocksCost]
  | _ :: l, [], _ => by
    have := blocks_le n L B l [] (by simp)
    simp only [blocksCost, List.length_cons, Nat.succ_mul]; omega
  | _ :: l, x :: cs, h => by
    have := blocks_le n L B l cs (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [blocksCost, List.length_cons, Nat.succ_mul]; omega

theorem small_term (a : ℕ) (ha : a ≤ 4) : (natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40) ≤ 3080 := by
  have h1 := nbl_le a
  have h2 := two_pow_nbl a
  rw [pow_succ] at h2
  have h3 : natBitLength a + 2 ≤ 7 := by omega
  have h4 : 40 * 2 ^ natBitLength a + 40 ≤ 440 := by omega
  calc (natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40) ≤ 7 * 440 := Nat.mul_le_mul h3 h4
    _ = 3080 := by norm_num

/-- **PA's setup cost is linear**. -/
theorem setup_le (N n L : ℕ) (codes cc : List ℕ) (ha : codes.length ≤ 4) (hk : cc.length ≤ 2)
    (hx : ∀ x ∈ codes, (RepairRepresentation.natWord x).length ≤ N)
    (hy : ∀ y ∈ cc, (RepairRepresentation.natWord y).length ≤ N) :
    setupCost n L codes cc ≤ 700 * N + 200 * n + 150 * L + 20000 := by
  have hsl : ∀ x ∈ codes ++ cc, slotCost x n L ≤ 70 * N + 18 * n + 18 * L + 75 := by
    intro x hx'
    have := slot_le x n L
    rcases List.mem_append.1 hx' with h | h
    · have := hx x h; omega
    · have := hy x h; omega
  have b1 := blocks_le n L (70 * N + 18 * n + 18 * L + 75) symTrips codes (fun x h => hsl x (by simp [h]))
  have b2 := blocks_le n L (70 * N + 18 * n + 18 * L + 75) carTrips cc (fun x h => hsl x (by simp [h]))
  have e1 : symTrips.length = 4 := rfl
  have e2 : carTrips.length = 2 := rfl
  rw [e1] at b1
  rw [e2] at b2
  have s1 := small_term codes.length ha
  have s2 := small_term cc.length (by omega)
  have hn := nbl_le n
  unfold setupCost
  omega

/-- The table fuel coefficient (`carTableCost_poly`). -/
def CcT : ℕ := 10 ^ 160 + 16 * 1000000000000000000 + BlockPlatform.UnaryCalc.polyCoefficient 50 PrimT.CarBounds.cC2

/-- **A carrier slot's step bound** below `CcT·(N + n + L + 1)^{76} + 2`. -/
theorem carCostB_le {n : ℕ} (carriers : List (Stars.Carrier n)) (N L k : ℕ) (h2 : 2 ≤ n + L)
    (hy : ∀ y ∈ carriers.map Stars.Carrier.code, (RepairRepresentation.natWord y).length ≤ N) :
    CarM2.carCostB carriers L k ≤ CcT * (N + n + L + 1) ^ 76 + 2 := by
  unfold CarM2.carCostB
  split_ifs with h
  · have hp : PrimT.CarTable.carTableCost (carriers.get ⟨k, h⟩) L ≤
        CcT * (natBitLength (carriers.get ⟨k, h⟩).code + n + L + 1) ^ 76 :=
      PrimT.CarCost.carTableCost_poly (carriers.get ⟨k, h⟩) L h2
    have hw := hy (carriers.get ⟨k, h⟩).code
      (List.mem_map.2 ⟨carriers.get ⟨k, h⟩, List.get_mem carriers ⟨k, h⟩, rfl⟩)
    rw [PrimAsm.ParseNat.natWord_length] at hw
    have hm : natBitLength (carriers.get ⟨k, h⟩).code + n + L + 1 ≤ N + n + L + 1 := by omega
    have h76 := Nat.pow_le_pow_left hm 76
    have := Nat.mul_le_mul_left CcT h76
    omega
  · omega

theorem sq_le (c M : ℕ) (h : c + 2 ≤ 6 * M) : PrimAsm.UnaryPow.sq c ≤ 7200 * M ^ 2 := by
  unfold PrimAsm.UnaryPow.sq
  have := Nat.mul_le_mul h h
  calc 200 * (c + 2) * (c + 2) = 200 * ((c + 2) * (c + 2)) := by ring
    _ ≤ 200 * (6 * M * (6 * M)) := Nat.mul_le_mul_left _ this
    _ = 7200 * M ^ 2 := by ring

theorem sq_ge_self (c : ℕ) : c ≤ PrimAsm.UnaryPow.sq c := by unfold PrimAsm.UnaryPow.sq; nlinarith

theorem m1_le (n : ℕ) : m1Cost (c1Of n) n ≤ 10 ^ 7 * (Lof n + n + 1) ^ 2 := by
  have hn := nbl_le n
  have h2 := two_pow_nbl n
  rw [pow_succ] at h2
  have hL1 : 1 ≤ Lof n := by unfold Lof; omega
  have hc1 : c1Of n + 2 ≤ 6 * (Lof n + n + 1) := by unfold c1Of; omega
  have hsq := sq_le (c1Of n) (Lof n + n + 1) hc1
  have a1 : natBitLength n + 2 ≤ 3 * (Lof n + n + 1) := by omega
  have a2 : 40 * 2 ^ natBitLength n + 40 ≤ 100 * (Lof n + n + 1) := by omega
  have hr : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 300 * (Lof n + n + 1) ^ 2 := by
    calc (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 3 * (Lof n + n + 1) * (100 * (Lof n + n + 1)) :=
          Nat.mul_le_mul a1 a2
      _ = 300 * (Lof n + n + 1) ^ 2 := by ring
  have hMsq : Lof n + n + 1 ≤ (Lof n + n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold m1Cost
  omega

/-- `K·(N + 2)^e ≤ (N + 2)^{e + log₂ K + 1}`. -/
theorem dom_gen (K e N : ℕ) : K * (N + 2) ^ e ≤ (N + 2) ^ (e + Nat.log 2 K + 1) := by
  have h2 : K < 2 ^ (Nat.log 2 K).succ := Nat.lt_pow_succ_log_self (by norm_num) K
  have h1 : 2 ^ (Nat.log 2 K).succ ≤ (N + 2) ^ (Nat.log 2 K).succ := Nat.pow_le_pow_left (by omega) _
  have h3 : K ≤ (N + 2) ^ (Nat.log 2 K + 1) := (lt_of_lt_of_le h2 h1).le
  calc K * (N + 2) ^ e ≤ (N + 2) ^ (Nat.log 2 K + 1) * (N + 2) ^ e := Nat.mul_le_mul_right _ h3
    _ = (N + 2) ^ (e + Nat.log 2 K + 1) := by rw [← pow_add]; congr 1; omega

theorem kb_gen (C a b X : ℕ) (hab : a ≤ b) (hb : 1 ≤ b) :
    2 * (C * a * X) + 10 ^ 8 * X ≤ (2 * C + 10 ^ 8) * b * X := by
  have h1 := Nat.mul_le_mul_left (C * X) hab
  have h2 := Nat.mul_le_mul_left (10 ^ 8 * X) hb
  calc 2 * (C * a * X) + 10 ^ 8 * X = 2 * (C * X * a) + 10 ^ 8 * X * 1 := by ring
    _ ≤ 2 * (C * X * b) + 10 ^ 8 * X * b := Nat.add_le_add (Nat.mul_le_mul_left 2 h1) h2
    _ = (2 * C + 10 ^ 8) * b * X := by ring

/-- The bound's coefficient and **the phase's exponent** (irreducible constants). -/
irreducible_def Kb : ℕ := (2 * CcT + 10 ^ 8) * 4 ^ 76
irreducible_def DtC : ℕ := 1976 + Nat.log 2 Kb + 1

theorem Kb_ge (X : ℕ) : 2 * (CcT * 3 ^ 76 * X) + 10 ^ 8 * X ≤ Kb * X := by
  rw [Kb_def]
  exact kb_gen CcT (3 ^ 76) (4 ^ 76) X (Nat.pow_le_pow_left (by norm_num) 76) (Nat.one_le_pow _ _ (by norm_num))

/-- **`T = (N + 2)^{DtC}` dominates `Kb·(N + 2)^{1976}`**. -/
theorem T_dom (N : ℕ) : Kb * (N + 2) ^ 1976 ≤ (N + 2) ^ DtC := by
  rw [DtC_def]; exact dom_gen Kb 1976 N

theorem one_le_DtC : 1 ≤ DtC := by rw [DtC_def]; omega

/-! The arithmetic of `T_bounds`, in clean contexts (no large literal powers in scope). -/

theorem Lof_two (n : ℕ) : 2 ≤ n + Lof n := by
  unfold Lof; have := Nat.one_le_pow 26 (n + 1) (Nat.succ_pos n); omega

theorem Lof_le_pow (n N : ℕ) (h : n ≤ N) : Lof n ≤ (N + 2) ^ 26 := by
  unfold Lof
  have : (n + 1) ^ 26 < (N + 2) ^ 26 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

theorem ar_M (L N n Q : ℕ) (hLQ : L ≤ Q) (hNQ : N + 2 ≤ Q) (hnN : n ≤ N) : L + n + 1 ≤ 2 * Q := by omega

theorem ar_b (L N n Q : ℕ) (hLQ : L ≤ Q) (hNQ : N + 2 ≤ Q) (hnN : n ≤ N) : N + n + L + 1 ≤ 3 * Q := by omega

theorem ar_one (N Q : ℕ) (hNQ : N + 2 ≤ Q) : 1 ≤ Q := by omega

theorem ar_1 (m1 A Q2 X KX T Z : ℕ) (h1 : m1 ≤ 10 ^ 7 * A) (h2 : A ≤ 4 * Q2) (hQ2X : Q2 ≤ X)
    (hKb : 2 * Z + 10 ^ 8 * X ≤ KX) (hdom : KX ≤ T) : m1 ≤ T := by omega

theorem ar_cb (c A B Z : ℕ) (h1 : c ≤ A + 2) (h2 : A ≤ B) (e : B = Z) : c ≤ Z + 2 := by omega

theorem ar_2 (L N n Q X KX T Z s c0 c1 : ℕ) (hLQ : L ≤ Q) (hNQ : N + 2 ≤ Q) (hnN : n ≤ N) (hQX : Q ≤ X)
    (hs : s ≤ 700 * N + 200 * n + 150 * L + 20000) (h0 : c0 ≤ Z + 2) (h1 : c1 ≤ Z + 2)
    (hKb : 2 * Z + 10 ^ 8 * X ≤ KX) (hdom : KX ≤ T) :
    L + (s + 1 + (3 * (2 * N + n + L + 20) + 1 + 1 + (3 * (2 * N + n + L + 20) + 1)) + 1 + (c0 + 1 + c1)) ≤ T := by
  omega

/-- **Both masked stages fit in `T = (N + 2)^{DtC}`** (`carPipe`'s `hT1`, `hT2`), at any request with `n ≤ N`, at
most four codes and two carriers, each code's word within `N`. -/
theorem T_bounds (N n : ℕ) (codes : List ℕ) (carriers : List (Stars.Carrier n)) (hnN : n ≤ N)
    (ha : codes.length ≤ 4) (hk : carriers.length ≤ 2)
    (hx : ∀ x ∈ codes, (RepairRepresentation.natWord x).length ≤ N)
    (hy : ∀ y ∈ carriers.map Stars.Carrier.code, (RepairRepresentation.natWord y).length ≤ N) :
    m1Cost (c1Of n) n ≤ (N + 2) ^ DtC ∧
      Lof n + CarM2.m2Bnd (c2Of N n) n (Lof n) codes carriers ≤ (N + 2) ^ DtC := by
  have hdom := T_dom N
  have hKb := Kb_ge ((N + 2) ^ 1976)
  have hXQ : (N + 2) ^ 1976 = ((N + 2) ^ 26) ^ 76 := by rw [← pow_mul]
  have hLQ := Lof_le_pow n N hnN
  have hNQ : N + 2 ≤ (N + 2) ^ 26 := Nat.le_self_pow (by norm_num) _
  have hQ1 := ar_one N _ hNQ
  have hQX : (N + 2) ^ 26 ≤ (N + 2) ^ 1976 := by rw [hXQ]; exact Nat.le_self_pow (by norm_num) _
  have hQ2X : ((N + 2) ^ 26) ^ 2 ≤ (N + 2) ^ 1976 := by rw [hXQ]; exact Nat.pow_le_pow_right hQ1 (by norm_num)
  constructor
  · have h1 := m1_le n
    have hM := ar_M (Lof n) N n _ hLQ hNQ hnN
    have h2 : (Lof n + n + 1) ^ 2 ≤ 4 * ((N + 2) ^ 26) ^ 2 := by
      calc (Lof n + n + 1) ^ 2 ≤ (2 * (N + 2) ^ 26) ^ 2 := Nat.pow_le_pow_left hM 2
        _ = 4 * ((N + 2) ^ 26) ^ 2 := by ring
    exact ar_1 _ _ _ _ _ _ _ h1 h2 hQ2X hKb hdom
  · have hs := setup_le N n (Lof n) codes (carriers.map Stars.Carrier.code) ha (by simpa using hk) hx hy
    have hb := ar_b (Lof n) N n _ hLQ hNQ hnN
    have hb76 : (N + n + Lof n + 1) ^ 76 ≤ (3 * (N + 2) ^ 26) ^ 76 := Nat.pow_le_pow_left hb 76
    have e : CcT * (3 * (N + 2) ^ 26) ^ 76 = CcT * 3 ^ 76 * (N + 2) ^ 1976 := by rw [hXQ, mul_pow, Nat.mul_assoc]
    have hcb : ∀ k, CarM2.carCostB carriers (Lof n) k ≤ CcT * 3 ^ 76 * (N + 2) ^ 1976 + 2 := fun k =>
      ar_cb _ _ _ _ (carCostB_le carriers N (Lof n) k (Lof_two n) hy) (Nat.mul_le_mul_left CcT hb76) e
    exact ar_2 (Lof n) N n _ _ _ _ _ _ _ _ hLQ hNQ hnN hQX hs (hcb 0) (hcb 1) hKb hdom

/-- **The capacities** the three stages need, from `T`'s two bounds. -/
theorem caps (Dt N n : ℕ) (codes : List ℕ) {n' : ℕ} (carriers : List (Stars.Carrier n'))
    (hT1 : m1Cost (c1Of n) n ≤ (N + 2) ^ Dt)
    (hT2 : Lof n + CarM2.m2Bnd (c2Of N n) n (Lof n) codes carriers ≤ (N + 2) ^ Dt) :
    c1Of n ≤ (N + 2) ^ Dt ∧ c2Of N n ≤ (N + 2) ^ Dt ∧ 2 * N + 2 ≤ (N + 2) ^ Dt := by
  have hs := sq_ge_self (c1Of n)
  have e1 : c1Of n ≤ m1Cost (c1Of n) n := by unfold m1Cost; omega
  have e2 : c2Of N n ≤ CarM2.m2Bnd (c2Of N n) n (Lof n) codes carriers := by unfold CarM2.m2Bnd; omega
  have e3 : 2 * N + 2 ≤ c2Of N n := by unfold c2Of; omega
  omega

/-- **The capacity `2^{Dt}·(N + 1)^{Dt}` holds `T`.** -/
theorem T_le_cap (Dt N : ℕ) : (N + 2) ^ Dt ≤ 2 ^ Dt * (N + 1) ^ Dt := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _

/-- The phase's step coefficient. -/
def CsOf (Dt : ℕ) : ℕ := (57600 * (Dt + 1) + 10 ^ 6) * 2 ^ (2 * Dt)

theorem cap_sq (Dt N : ℕ) : (2 ^ Dt * (N + 1) ^ Dt) ^ 2 = 2 ^ (2 * Dt) * (N + 1) ^ (2 * Dt) := by
  rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm Dt 2]

/-- **The pipeline's steps within `CsOf Dt·(N + 1)^{2·Dt}`** at the capacity `2^{Dt}·(N + 1)^{Dt}`. -/
theorem pipe_le (Dt N n : ℕ) (hDt : 1 ≤ Dt) (codes : List ℕ) {n' : ℕ} (carriers : List (Stars.Carrier n'))
    (hT1 : m1Cost (c1Of n) n ≤ (N + 2) ^ Dt)
    (hT2 : Lof n + CarM2.m2Bnd (c2Of N n) n (Lof n) codes carriers ≤ (N + 2) ^ Dt) :
    pipeCost (2 ^ Dt * (N + 1) ^ Dt) Dt N n codes carriers ≤ CsOf Dt * (N + 1) ^ (2 * Dt) := by
  have hTC := T_le_cap Dt N
  have hN2 : N + 2 ≤ (N + 2) ^ Dt := Nat.le_self_pow (by omega) _
  have hC2 := cap_sq Dt N
  have e : CsOf Dt * (N + 1) ^ (2 * Dt) = 57600 * ((Dt + 1) * (2 ^ (2 * Dt) * (N + 1) ^ (2 * Dt))) +
      10 ^ 6 * (2 ^ (2 * Dt) * (N + 1) ^ (2 * Dt)) := by unfold CsOf; ring
  rw [e, ← hC2]
  generalize 2 ^ Dt * (N + 1) ^ Dt = C at hTC hC2 ⊢
  have hsq := sq_le C C (by omega)
  have hCC : C ≤ C ^ 2 := Nat.le_self_pow (by norm_num) _
  have hmk : mkTCost C Dt N ≤ (Dt + 1) * (4 * PrimAsm.UnaryPow.sq C) + 27 * N + 12 := by unfold mkTCost; omega
  have hmk2 : (Dt + 1) * (4 * PrimAsm.UnaryPow.sq C) ≤ (Dt + 1) * (28800 * C ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have hr : (Dt + 1) * (28800 * C ^ 2) = 28800 * ((Dt + 1) * C ^ 2) := by ring
  unfold pipeCost s1Cost s3Cost
  omega

/-- **`T` within the step bound** (the residues' lengths). -/
theorem T_le_Cs (Dt N : ℕ) : (N + 2) ^ Dt ≤ CsOf Dt * (N + 1) ^ (2 * Dt) := by
  have hTC := T_le_cap Dt N
  have hC2 := cap_sq Dt N
  have hCC : 2 ^ Dt * (N + 1) ^ Dt ≤ (2 ^ Dt * (N + 1) ^ Dt) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1 : 2 ^ (2 * Dt) * (N + 1) ^ (2 * Dt) ≤ CsOf Dt * (N + 1) ^ (2 * Dt) := by
    unfold CsOf
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ (by omega)
  omega

end NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound
