import Proof.Wire_3_5.UnionMachine.RadSpec
import Proof.Wire_3_5.Primitive.Writers.PopSetupMath
import Proof.Wire_3_5.Primitive.Writers.BShape1

/-! # The RADIX row's capacities, Route B (the stage 7 (a))

row:radix P3:2585-2623 at the Route-B capacities `R = U^40`, `Lg = R + 1`, `cap = U^45`,
`U = 2^20·((8L+2)^{3·lb+1} + M + τ + L + M_lab + lb + lw + p + b₀ + 2)` (POP's power scale, `PopSetupNeed`): at an
admissible request whose digit lists have at most `L` occurrences with exactly four labels each, labels at most
`M_lab`, `listBound D ≤ lb` and table word (at `L`) of length at most `lw`, every capacity condition of
`radRow_step` holds (`RadReqB.Caps`): each visit factor's stage cost is `≤ 2U⁵` (`PopCap.costC_le_popKc` with the
block `≤ U²`), the scrub loop `2τ(M+1)(4R+9)`, the residue loop (`2τ(M+1)` constants below `p`), the masked
selection (`2τ(M+1)` prints of `≤ popPW` bits) and the odometer are `≤ U⁴²`.

* `lvw_mono`, `mem_storeFrom`, `consFrom_lt`, `storeFrom_getD_pw`, **`radCaps`**.

Paper quantity of the main type: the RADIX row's capacities (Route B) against the row's numbers. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.RadB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

/-- The table word's length is monotone in the point length. -/
theorem lvw_mono (D : ListData) {L L' : ℕ} (h : L ≤ L') :
    (FinalPass.ListEval.levelWord D.M D.J D.W (FinalPass.ListEval.rowsOf D L)).length ≤
      (FinalPass.ListEval.levelWord D.M D.J D.W (FinalPass.ListEval.rowsOf D L')).length := by
  unfold FinalPass.ListEval.levelWord
  simp only [List.length_append, List.length_flatMap]
  have hr : ∀ j ∈ FinalPass.ListEval.levels D.J,
      (FinalPass.ListEval.record D.J D.W (FinalPass.ListEval.rowsOf D L) j).length ≤
        (FinalPass.ListEval.record D.J D.W (FinalPass.ListEval.rowsOf D L') j).length := by
    intro j _
    unfold FinalPass.ListEval.record FinalPass.ListEval.rowsOf
    simp only [List.length_cons, List.length_append, List.length_map, List.length_range]
    omega
  have := List.sum_le_sum hr
  omega

theorem mem_storeFrom (K : ℕ) (Pp Pm : ℕ → ℕ → Poly) : ∀ (o n : ℕ) (f : Poly), f ∈ storeFrom K Pp Pm o n →
    ∃ d t, f = Pp d t ∨ f = Pm d t
  | _, 0, f, h => by simp [storeFrom] at h
  | o, n + 1, f, h => by
    simp only [storeFrom, List.mem_append, List.mem_map, List.mem_range] at h
    rcases h with ⟨t, _, rfl⟩ | ⟨t, _, rfl⟩ | h
    · exact ⟨o, t, Or.inl rfl⟩
    · exact ⟨o, t, Or.inr rfl⟩
    · exact mem_storeFrom K Pp Pm (o + 1) n f h

theorem consFrom_lt (K p b0 : ℕ) (hp : 0 < p) : ∀ (o n : ℕ), ∀ k ∈ consFrom K p b0 o n, k < p
  | _, 0, k, h => by simp [consFrom] at h
  | o, n + 1, k, h => by
    simp only [consFrom, List.mem_append, List.mem_map, List.mem_range] at h
    rcases h with ⟨t, _, rfl⟩ | ⟨t, _, rfl⟩ | h
    · exact Nat.mod_lt _ hp
    · exact Nat.mod_lt _ hp
    · exact consFrom_lt K p b0 hp (o + 1) n k h

/-- **Every print of the RADIX store is short**: `|polyWord| ≤ (8L+2)^{3lb}(6lb(M_lab+1)+2)+1`. -/
theorem storeFrom_getD_pw (D : ListData) (digs : List Dig) (Lmax Mlab lb : ℕ) (hlb : listBound D ≤ lb)
    (hdg : ∀ dg ∈ digs, dg.1 ≤ Lmax ∧ ∀ lab ∈ dg.2, lab ≤ Mlab) (j : ℕ) :
    (Rec.polyWord ((radFs D digs).getD j [])).length ≤
      (8 * Lmax + 2) ^ (3 * lb) * (2 * (3 * lb) * (Mlab + 1) + 2) + 1 := by
  have hdig : ∀ d, (digAt digs d).1 ≤ Lmax ∧ ∀ lab ∈ (digAt digs d).2, lab ≤ Mlab := by
    intro d
    unfold digAt
    by_cases hd : d < digs.length
    · rw [List.getD_eq_getElem _ _ hd]; exact hdg _ (List.getElem_mem hd)
    · rw [List.getD_eq_default _ _ (by omega)]; exact ⟨Nat.zero_le _, fun lab h => by simp at h⟩
  have hpw : ∀ d t (sgn : Bool), (Rec.polyWord (polyC D (digAt digs d).1 t sgn false (digAt digs d).2)).length ≤
      (8 * Lmax + 2) ^ (3 * lb) * (2 * (3 * lb) * (Mlab + 1) + 2) + 1 := by
    intro d t sgn
    refine (PrimAsm.PopCap.polyWord_polyC_le D _ t sgn false _ Mlab (hdig d).2).trans ?_
    unfold PrimAsm.PopCap.popPW
    have h1 : (8 * (digAt digs d).1 + 2) ^ (3 * listBound D) ≤ (8 * Lmax + 2) ^ (3 * lb) :=
      (Nat.pow_le_pow_left (by have := (hdig d).1; omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : 2 * (3 * listBound D) * (Mlab + 1) + 2 ≤ 2 * (3 * lb) * (Mlab + 1) + 2 := by
      have : 3 * listBound D ≤ 3 * lb := by omega
      have := Nat.mul_le_mul_right (Mlab + 1) (Nat.mul_le_mul_left 2 this)
      omega
    exact Nat.add_le_add_right (Nat.mul_le_mul h1 h2) 1
  by_cases hj : j < (radFs D digs).length
  · rw [List.getD_eq_getElem _ _ hj]
    obtain ⟨d, t, h | h⟩ := mem_storeFrom D.M (radPp D digs) (radPm D digs) 0 digs.length _ (List.getElem_mem hj)
    · rw [h]; exact hpw d t true
    · rw [h]; exact hpw d t false
  · rw [List.getD_eq_default _ _ (by omega)]
    have : (Rec.polyWord ([] : Poly)).length = 1 := rfl
    rw [this]; omega

/-- The capacities at any scale `U = 2^20·X` above the row's numbers. -/
theorem caps_of (r : RadReq) (Lmax Mlab lb lw X U : ℕ) (hUX : U = 2 ^ 20 * X) (hPre : r.Pre)
    (hlb : listBound r.D ≤ lb)
    (hdg : ∀ dg ∈ r.digs, dg.1 ≤ Lmax ∧ dg.2.length = 4 * dg.1 ∧ ∀ lab ∈ dg.2, lab ≤ Mlab)
    (hlw : (FinalPass.ListEval.levelWord r.D.M r.D.J r.D.W (FinalPass.ListEval.rowsOf r.D Lmax)).length ≤ lw)
    (hQX : (8 * Lmax + 2) ^ (3 * lb) ≤ X) (hM : r.D.M ≤ X) (hτ : r.digs.length ≤ X) (hL : Lmax ≤ X)
    (hMl : Mlab ≤ X) (hlbX : lb ≤ X) (hlwX : lw ≤ X) (hpX : r.p ≤ X) (h2X : 2 ≤ X) :
    RadReqB.Caps ⟨r, U ^ 40, U ^ 40 + 1, U ^ 45⟩ := by
  obtain ⟨_, _, _, hsp⟩ := hPre
  have hU20 : 2 ^ 20 ≤ U := by rw [hUX]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hU20' : 1048576 ≤ U := by have : (2 : ℕ) ^ 20 = 1048576 := by norm_num
                                 omega
  have hXU : 1048576 * X ≤ U := by rw [hUX]; norm_num
  have e2 : U * U = U ^ 2 := by ring
  have pw : ∀ a b : ℕ, a ≤ b → U ^ a ≤ U ^ b := fun a b h => Nat.pow_le_pow_right (by omega) h
  have pwL : ∀ a b : ℕ, a < b → 1048576 * U ^ a ≤ U ^ b := by
    intro a b h
    calc 1048576 * U ^ a ≤ U * U ^ a := Nat.mul_le_mul_right _ hU20'
      _ = U ^ (a + 1) := by ring
      _ ≤ U ^ b := pw _ _ h
  have hU1 : U ^ 1 = U := pow_one U
  -- the scrub capacity
  have hR : 2 ≤ U ^ 40 := le_trans (by omega) (Nat.le_self_pow (by norm_num) U)
  have hcaps : ∀ dg ∈ r.digs, ∀ t ≤ r.D.M, ∀ sgn : Bool, costC r.D dg.1 t sgn false dg.2 + 1 ≤ U ^ 40 := by
    intro dg hd t ht sgn
    obtain ⟨hL1, hlen, hlab⟩ := hdg dg hd
    have hlw1 := (lvw_mono r.D hL1).trans hlw
    obtain ⟨L, hLd⟩ : ∃ L, L = dg.1 := ⟨_, rfl⟩
    obtain ⟨labs, hlabsd⟩ : ∃ labs, labs = dg.2 := ⟨_, rfl⟩
    rw [← hLd, ← hlabsd] at hlen ⊢
    rw [← hlabsd] at hlab
    rw [← hLd] at hL1 hlw1
    have hcapC : capC r.D L ≤ 4 * (lw + Lmax + 1) := by
      unfold capC FinalPass.ListEval.capOf; omega
    have hsum1 : (labs.map fun lab => lab + 1).sum ≤ 4 * L * (Mlab + 1) := by
      have := PrimAsm.BShape.sum_map_le_card labs (fun lab => lab + 1) (Mlab + 1) (fun lab h => by
        have := hlab lab h; omega)
      rw [hlen] at this; exact this
    have hsum2 : (labs.map fun lab => 2 * lab + 10).sum ≤ 4 * L * (2 * Mlab + 10) := by
      have := PrimAsm.BShape.sum_map_le_card labs (fun lab => 2 * lab + 10) (2 * Mlab + 10) (fun lab h => by
        have := hlab lab h; omega)
      rw [hlen] at this; exact this
    have hlabSum : PrimAsm.FiltRec.labSum labs ≤ 5 + 4 * L * (2 * Mlab + 10) := by
      unfold PrimAsm.FiltRec.labSum; omega
    have hbl := PrimAsm.PopSetupMath.blockC_len r.D L t sgn false labs
    rw [PrimAsm.PopSetupMath.cap1C_eq L labs hlen] at hbl
    have hkc := PrimAsm.PopCap.costC_le_popKc r.D L t sgn false labs hlen _ le_rfl
    refine Nat.add_le_add_right hkc 1 |>.trans ?_
    unfold PrimAsm.PopCap.popKc
    -- sizes against `X`
    have hLX : L ≤ X := hL1.trans hL
    have hLm : 4 * L * (Mlab + 1) ≤ 4 * X * (X + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hLX) (by omega)
    have hLm2 : 4 * L * (2 * Mlab + 10) ≤ 4 * X * (2 * X + 10) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hLX) (by omega)
    obtain ⟨XX, hXXd⟩ : ∃ XX, XX = X * X := ⟨_, rfl⟩
    have e3 : 4 * X * (X + 1) = 4 * XX + 4 * X := by rw [hXXd]; ring
    have e4 : 4 * X * (2 * X + 10) = 8 * XX + 40 * X := by rw [hXXd]; ring
    have hXXU : 1048576 * XX ≤ U ^ 2 := by
      rw [hXXd, ← e2]
      calc 1048576 * (X * X) ≤ 1048576 * (X * X) * 1048576 := Nat.le_mul_of_pos_right _ (by norm_num)
        _ = (1048576 * X) * (1048576 * X) := by ring
        _ ≤ U * U := Nat.mul_le_mul hXU hXU
    have hXX1 : X ≤ XX := by rw [hXXd]; exact Nat.le_mul_of_pos_left _ (by omega)
    -- the block
    have hblk : 2 * (blockC r.D L t sgn false labs).length + 2 ≤ U ^ 2 := by omega
    -- the stage's inner factor
    have hc1 : capC r.D L + 1 ≤ U := by omega
    have hc3 : (capC r.D L + 1) ^ 3 ≤ U ^ 3 := Nat.pow_le_pow_left hc1 3
    have h4L : (4 * L + 1) ^ 2 ≤ U ^ 2 := by
      have : 4 * L + 1 ≤ U := by omega
      exact Nat.pow_le_pow_left this 2
    have hQ : (8 * L + 2) ^ (3 * listBound r.D) ≤ U := by
      have h1 : (8 * L + 2) ^ (3 * listBound r.D) ≤ (8 * Lmax + 2) ^ (3 * lb) :=
        (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
      omega
    have p23 := pwL 2 3 (by norm_num)
    have p34 := pwL 3 4 (by norm_num)
    have p45 := pwL 4 5 (by norm_num)
    have hin : 118 * L + 10 + 50 * (capC r.D L + 1) ^ 3 + 2 * PrimAsm.FiltRec.labSum labs + 100 * (4 * L + 1) ^ 2 ≤
        U ^ 4 := by
      have : U ≤ U ^ 2 := by rw [← e2]; exact Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hQin : (8 * L + 2) ^ (3 * listBound r.D) * (118 * L + 10 + 50 * (capC r.D L + 1) ^ 3 +
        2 * PrimAsm.FiltRec.labSum labs + 100 * (4 * L + 1) ^ 2) ≤ U ^ 5 := by
      calc _ ≤ U * U ^ 4 := Nat.mul_le_mul hQ hin
        _ = U ^ 5 := by ring
    have p540 := pwL 5 40 (by norm_num)
    have p240 := pwL 2 40 (by norm_num)
    omega
  have hcs : ∀ k ∈ radCs r.D r.digs r.p r.b0, k < r.p := consFrom_lt _ _ _ (by omega) _ _
  refine ⟨hR, hcaps, le_rfl, ?_, ?_, ?_, ?_⟩
  · -- the scrub loop
    show 2 * r.digs.length * (r.D.M + 1) * (4 * U ^ 40 + 9) + 1 ≤ U ^ 45
    have h1 : 2 * r.digs.length * (r.D.M + 1) ≤ U ^ 2 := by
      rw [← e2]
      have : 2 * r.digs.length ≤ U := by omega
      exact Nat.mul_le_mul this (by omega)
    have h2 : 4 * U ^ 40 + 9 ≤ U ^ 41 := by
      have := pwL 40 41 (by norm_num); have : 1 ≤ U ^ 40 := Nat.one_le_pow _ _ (by omega); omega
    have h3 : 2 * r.digs.length * (r.D.M + 1) * (4 * U ^ 40 + 9) ≤ U ^ 43 := by
      calc _ ≤ U ^ 2 * U ^ 41 := Nat.mul_le_mul h1 h2
        _ = U ^ 43 := by ring
    have := pwL 43 45 (by norm_num)
    have : 1 ≤ U ^ 43 := Nat.one_le_pow _ _ (by omega)
    omega
  · -- the residue loop
    show resLoopCost (radCs r.D r.digs r.p r.b0) + 3 ≤ U ^ 45
    unfold resLoopCost
    have hs := PrimAsm.BShape.sum_map_le_card (radCs r.D r.digs r.p r.b0) (fun k => 5 * k + 10) (5 * r.p + 10)
      (fun k hk => by have := hcs k hk; omega)
    have hl : (radCs r.D r.digs r.p r.b0).length = 2 * r.digs.length * (r.D.M + 1) := by
      unfold radCs; exact consFrom_length _ _ _ _ _
    rw [hl] at hs
    have h1 : 2 * r.digs.length * (r.D.M + 1) ≤ U ^ 2 := by
      rw [← e2]
      have : 2 * r.digs.length ≤ U := by omega
      exact Nat.mul_le_mul this (by omega)
    have h2 : 2 * r.digs.length * (r.D.M + 1) * (5 * r.p + 10) ≤ U ^ 3 := by
      calc _ ≤ U ^ 2 * U := Nat.mul_le_mul h1 (by omega)
        _ = U ^ 3 := by ring
    have := pwL 3 45 (by norm_num)
    have : 1 ≤ U ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  · -- the masked selection
    show mselCost (radFs r.D r.digs) ≤ U ^ 45
    unfold mselCost
    have hpw := storeFrom_getD_pw r.D r.digs Lmax Mlab lb hlb (fun dg h => ⟨(hdg dg h).1, (hdg dg h).2.2⟩)
    have hs := PrimAsm.BShape.sum_map_le_card (List.range (radFs r.D r.digs).length)
      (fun j => mselPass (radFs r.D r.digs) j + 2)
      ((8 * Lmax + 2) ^ (3 * lb) * (2 * (3 * lb) * (Mlab + 1) + 2) + 1 + 10) (fun j _ => by
        have := hpw j; unfold mselPass; omega)
    rw [List.length_range] at hs
    have hl : (radFs r.D r.digs).length = 2 * r.digs.length * (r.D.M + 1) := by
      unfold radFs; exact storeFrom_length _ _ _ _ _
    rw [hl] at hs
    rw [hl]
    have h1 : 2 * r.digs.length * (r.D.M + 1) ≤ U ^ 2 := by
      rw [← e2]
      have : 2 * r.digs.length ≤ U := by omega
      exact Nat.mul_le_mul this (by omega)
    have h2 : (8 * Lmax + 2) ^ (3 * lb) * (2 * (3 * lb) * (Mlab + 1) + 2) + 1 + 10 ≤ U ^ 4 := by
      have hq : (8 * Lmax + 2) ^ (3 * lb) ≤ U := by omega
      have hd : 2 * (3 * lb) * (Mlab + 1) + 2 ≤ U ^ 2 := by
        rw [← e2]
        have : 2 * (3 * lb) * (Mlab + 1) = 6 * lb * (Mlab + 1) := by ring
        have h5 : 6 * lb * (Mlab + 1) ≤ (6 * X) * (X + 1) := Nat.mul_le_mul (by omega) (by omega)
        have h6 : (6 * X) * (X + 1) + 2 ≤ U * U := by
          have h7 : (6 * X) * (X + 1) + 2 ≤ (1048576 * X) * (1048576 * X) := by nlinarith
          exact h7.trans (Nat.mul_le_mul hXU hXU)
        omega
      have h8 : (8 * Lmax + 2) ^ (3 * lb) * (2 * (3 * lb) * (Mlab + 1) + 2) ≤ U * U ^ 2 := Nat.mul_le_mul hq hd
      have e9 : U * U ^ 2 = U ^ 3 := by ring
      have := pwL 3 4 (by norm_num)
      have : 1 ≤ U ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have h4 : 2 * r.digs.length * (r.D.M + 1) * ((8 * Lmax + 2) ^ (3 * lb) * (2 * (3 * lb) * (Mlab + 1) + 2) + 1 + 10)
        ≤ U ^ 6 := by
      calc _ ≤ U ^ 2 * U ^ 4 := Nat.mul_le_mul h1 h2
        _ = U ^ 6 := by ring
    have := pwL 6 45 (by norm_num)
    have : 1 ≤ U ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  · -- the odometer
    show incCost r.D.M (2 * r.digs.length) ≤ U ^ 45
    unfold incCost incBlk
    have h1 : 2 * r.digs.length * (r.D.M + 1) ≤ U ^ 2 := by
      rw [← e2]
      have : 2 * r.digs.length ≤ U := by omega
      exact Nat.mul_le_mul this (by omega)
    have h2 : 2 * r.digs.length * (10 * r.D.M + 45) ≤ U ^ 2 := by
      rw [← e2]
      have : 2 * r.digs.length ≤ U := by omega
      exact Nat.mul_le_mul this (by omega)
    have := pwL 2 45 (by norm_num)
    have h0 := pwL 0 2 (by norm_num)
    have e0 : U ^ 0 = 1 := pow_zero U
    have e : 9 * (2 * r.digs.length * (r.D.M + 1)) + 2 * r.digs.length * (10 * r.D.M + 45) + 20 ≤ 11 * U ^ 2 := by
      omega
    omega

/-- **The RADIX row's Route-B capacities** (`RadCapsStmt`). -/
theorem radCaps : RadCapsStmt := by
  intro r Lmax Mlab lb lw hPre hlb hdg hlw
  have hQX : (8 * Lmax + 2) ^ (3 * lb) ≤ radX r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0 := by
    have h1 : (8 * Lmax + 2) ^ (3 * lb) ≤ (8 * Lmax + 2) ^ (3 * lb + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    unfold radX; omega
  exact caps_of r Lmax Mlab lb lw (radX r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0)
    (radU r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0) rfl hPre hlb hdg hlw hQX
    (by unfold radX; omega) (by unfold radX; omega) (by unfold radX; omega) (by unfold radX; omega)
    (by unfold radX; omega) (by unfold radX; omega) (by unfold radX; omega) (by unfold radX; omega)

end NearCubicWires.WireExponent3_5.FinalPass.RadB
