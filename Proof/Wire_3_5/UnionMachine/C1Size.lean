import Proof.Wire_3_5.UnionMachine.C1Ref

/-! # C6 front, the C1 dock: the size of C1's request (C1's `c1sized` precondition; P3:1335, 3669-3671)

C1's contract `c1sized d` takes requests with `|selWord R| ≤ (R.n+1)^d`. At the union's request `selReqOf g` every
piece is bounded by one number `M` dominating `q`, the variables' count, the grid size, every atom's and parity's
description bits, `2^{cb+1}` and `r`:
* `gates_len_le` (a circuit charges at most its description bits' many gates), `gate_enc_le` (each charged gate's
  encoding bits are at most the circuit's description bits), `selGate_len` (`|selGate g| = 2·encodingBits + 2q + 2`);
* `carrier_len`, `carrier_enc`;
* **`selWord_len_le`**: `|selWord (selReqOf g)| ≤ 100·M^6`.

Paper quantity of the main type: the length of `star:selection`'s request at the union's weighted carriers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Size
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord natListWord intWord)

/-! ## Lists -/

theorem len_flatMap_le {α β : Type} (l : List α) (f : α → List β) (B : ℕ) (h : ∀ a ∈ l, (f a).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    omega

theorem len_flatten_le {β : Type} (L : List (List β)) (B : ℕ) (h : ∀ l ∈ L, l.length ≤ B) :
    L.flatten.length ≤ L.length * B := by
  have e : L.flatten = L.flatMap id := by simp
  rw [e]
  exact len_flatMap_le L id B h

/-! ## Circuits -/

theorem gates_len_le (m : Mode) {n : ℕ} (C : m.Circuit n) : (m.gates C).length ≤ m.descriptionBits C := by
  cases m
  · show (Stars.thrGates C).length ≤ C.top.descriptionBits + ∑ j, (C.bottom j).descriptionBits
    have h1 : C.bottomCount ≤ C.top.descriptionBits := by
      unfold SupportedNormalizedGate.descriptionBits; omega
    unfold Stars.thrGates
    rw [List.length_map]
    have h2 := List.length_filter_le (fun i => decide (i ∈ C.top.support)) (List.finRange C.bottomCount)
    rw [List.length_finRange] at h2
    omega
  · show (Stars.symGates C).length ≤ C.bottomCount + 1 + ∑ j, (C.bottom j).descriptionBits
    unfold Stars.symGates
    rw [List.length_map, List.length_finRange]
    omega

theorem gate_enc_le (m : Mode) {n : ℕ} (C : m.Circuit n) :
    ∀ g ∈ m.gates C, g.encodingBits ≤ m.descriptionBits C := by
  cases m
  · intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    show (C.bottom i).gate.encodingBits ≤ C.top.descriptionBits + ∑ j, (C.bottom j).descriptionBits
    have h1 : (C.bottom i).gate.encodingBits ≤ (C.bottom i).descriptionBits := Nat.le_add_right _ _
    have h2 : (C.bottom i).descriptionBits ≤ ∑ j, (C.bottom j).descriptionBits :=
      Finset.single_le_sum (f := fun j => (C.bottom j).descriptionBits) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  · intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    show (C.bottom i).gate.encodingBits ≤ C.bottomCount + 1 + ∑ j, (C.bottom j).descriptionBits
    have h1 : (C.bottom i).gate.encodingBits ≤ (C.bottom i).descriptionBits := Nat.le_add_right _ _
    have h2 : (C.bottom i).descriptionBits ≤ ∑ j, (C.bottom j).descriptionBits :=
      Finset.single_le_sum (f := fun j => (C.bottom j).descriptionBits) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega

theorem selGate_len {q : ℕ} (g : NormalizedThresholdGate q) :
    (GateConv.selGate g).length = 2 * g.encodingBits + 2 * q + 2 := by
  unfold GateConv.selGate NormalizedThresholdGate.encodingBits
  rw [List.length_append, List.length_flatMap, GateConv.intWord_len', List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp, GateConv.intWord_len', intBitLength]
  simp only [natBitLength, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_add]
  ring

/-! ## Carriers -/

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} (g : UnionGuess S z) (M : ℕ)

theorem carrier_len (hL : ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ M)
    (hP : ∀ X, g.mode.descriptionBits (g.parity X) ≤ M) (X : PcppVar g.pcpp) :
    (g.carrier X).length ≤ g.s * M + M := by
  unfold UnionGuess.carrier
  rw [List.length_append]
  have h1 : (List.ofFn fun a => g.mode.gates (g.atom X a)).flatten.length ≤ g.s * M := by
    have := len_flatten_le (List.ofFn fun a => g.mode.gates (g.atom X a)) M (by
      intro l hl
      obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hl
      exact (gates_len_le g.mode _).trans (hL X a))
    rwa [List.length_ofFn] at this
  have h2 : (if g.sysBit X then g.mode.gates (g.parity X) else []).length ≤ M := by
    split_ifs
    · exact (gates_len_le g.mode _).trans (hP X)
    · simp
  omega

theorem carrier_enc (hL : ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ M)
    (hP : ∀ X, g.mode.descriptionBits (g.parity X) ≤ M) (X : PcppVar g.pcpp) :
    ∀ gt ∈ g.carrier X, gt.encodingBits ≤ M := by
  intro gt hgt
  unfold UnionGuess.carrier at hgt
  rcases List.mem_append.1 hgt with h | h
  · obtain ⟨l, hl, hgl⟩ := List.mem_flatten.1 h
    obtain ⟨a, rfl⟩ := (List.mem_ofFn' _ _).1 hl
    exact (gate_enc_le g.mode _ gt hgl).trans (hL X a)
  · split_ifs at h
    · exact (gate_enc_le g.mode _ gt h).trans (hP X)
    · simp at h

theorem segStart_le {α β : Type} (f : α → List β) (l : List α) (i : ℕ) :
    FrontSelReq.segStart f l i ≤ (l.flatMap f).length := by
  unfold FrontSelReq.segStart
  rw [List.length_flatMap]
  have e : l.map (fun a => (f a).length) = (l.take i).map (fun a => (f a).length) ++
      (l.drop i).map (fun a => (f a).length) := by
    rw [← List.map_append, List.take_append_drop]
  rw [e, List.sum_append]
  omega

theorem nw_le (x : ℕ) : (natWord x).length ≤ 2 * x + 3 := by
  rw [PrimAsm.ParseNat.natWord_length]
  have := PrimAsm.CopyNat.natBitLength_le_self_succ x
  omega

theorem cnt_le (x : ℕ) : C1Cnt.cntOf x (C1Ref.litsG g) ≤ 2 ^ (g.pcpp.clauseBits + 1) := by
  unfold C1Cnt.cntOf
  refine (List.length_filter_le _ _).trans ?_
  unfold C1Ref.litsG
  rw [FrontTW.pairsOf_length, pow_succ]
  omega

/-- One population's words. -/
theorem pop_len (vs : List (PcppVar g.pcpp)) (P : List ℕ × ℚ)
    (hP : P ∈ vs.mapIdx fun i X => (List.range' (FrontSelReq.segStart g.carrier vs i) (g.carrier X).length,
      g.weight X)) (T b : ℕ) (hT : (vs.flatMap g.carrier).length ≤ T) (hb : ∀ X, (g.carrier X).length ≤ b)
    (hcb : 2 ^ (g.pcpp.clauseBits + 1) ≤ M) :
    (natListWord P.1 ++ ratWord P.2).length ≤ (2 * b + 3) + b * (2 * (T + b) + 3) + (4 * M + 7) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hP
  rw [List.length_mapIdx] at hi
  simp only [List.getElem_mapIdx]
  set a := FrontSelReq.segStart g.carrier vs i with ha
  set X := vs[i] with hX
  have haT : a ≤ T := (segStart_le g.carrier vs i).trans hT
  have hbX := hb X
  rw [List.length_append]
  -- the range
  have h1 : (natListWord (List.range' a (g.carrier X).length)).length ≤
      (2 * b + 3) + b * (2 * (T + b) + 3) := by
    rw [PrimAsm.CopyNat.natListWord_eq, List.length_append, List.length_range']
    have e1 := nw_le (g.carrier X).length
    have e2 := len_flatMap_le (List.range' a (g.carrier X).length) natWord (2 * (T + b) + 3) (by
      intro j hj
      rw [List.mem_range'_1] at hj
      exact (nw_le j).trans (by omega))
    rw [List.length_range'] at e2
    have e3 : (g.carrier X).length * (2 * (T + b) + 3) ≤ b * (2 * (T + b) + 3) := Nat.mul_le_mul_right _ hbX
    omega
  -- the weight
  have h2 : (ratWord (g.weight X)).length ≤ 4 * M + 7 := by
    rw [C1Ref.weight_eq, C1Rat.ratWord_dyadic, List.length_append, GateConv.intWord_len']
    have hc := cnt_le g X.val
    have hc1 := C1Rat.rstepN_le (C1Cnt.cntOf X.val (C1Ref.litsG g)) (g.pcpp.clauseBits + 1)
    have hd := C1Rat.rstepN_d (C1Cnt.cntOf X.val (C1Ref.litsG g)) (g.pcpp.clauseBits + 1)
    have hp : 2 ^ (C1Rat.rstepN (g.pcpp.clauseBits + 1) (C1Cnt.cntOf X.val (C1Ref.litsG g), false, 0)).2.2 ≤
        2 ^ (g.pcpp.clauseBits + 1) := Nat.pow_le_pow_right (by norm_num) hd
    have e1 := nw_le (2 ^ (C1Rat.rstepN (g.pcpp.clauseBits + 1) (C1Cnt.cntOf X.val (C1Ref.litsG g), false, 0)).2.2)
    have e2 := PrimAsm.CopyNat.natBitLength_le_self_succ
      ((C1Rat.rstepN (g.pcpp.clauseBits + 1) (C1Cnt.cntOf X.val (C1Ref.litsG g), false, 0)).1 : ℤ).natAbs
    simp only [Int.natAbs_natCast] at e2 ⊢
    omega
  omega

/-- **The size of C1's request at the union's carriers.** -/
theorem selWord_len_le (hM : 1 ≤ M) (hq : g.q ≤ M) (hV : C1Ref.VG g ≤ M) (hs : g.s ≤ M)
    (hL : ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ M) (hP : ∀ X, g.mode.descriptionBits (g.parity X) ≤ M)
    (hcb : 2 ^ (g.pcpp.clauseBits + 1) ≤ M) (hr : B.rOf g.q ≤ M) :
    (Plan.selWord (FrontSelReq.selReqOf g)).length ≤ 100 * M ^ 6 := by
  set vs := FrontSelReq.vsPos g with hvs
  set gl := vs.flatMap g.carrier with hgl
  have hvp : vs.length ≤ M := by
    rw [hvs]; unfold FrontSelReq.vsPos
    exact (List.length_filter_le _ _).trans (by rw [List.length_finRange]; exact hV)
  have hMM : M ≤ M * M := Nat.le_mul_of_pos_left M hM
  have hcar : ∀ X, (g.carrier X).length ≤ 2 * (M * M) := fun X => by
    have := carrier_len g M hL hP X
    have h2 : g.s * M ≤ M * M := Nat.mul_le_mul_right _ hs
    omega
  have hT : gl.length ≤ 2 * (M * (M * M)) := by
    have h1 : gl.length ≤ vs.length * (2 * (M * M)) := len_flatMap_le vs g.carrier _ (fun X _ => hcar X)
    have h2 : vs.length * (2 * (M * M)) ≤ M * (2 * (M * M)) := Nat.mul_le_mul_right _ hvp
    have h3 : M * (2 * (M * M)) = 2 * (M * (M * M)) := by ring
    omega
  have hsg : ∀ gt ∈ gl, (GateConv.selGate gt).length ≤ 6 * M := by
    intro gt hgt
    obtain ⟨X, -, hX⟩ := List.mem_flatMap.1 hgt
    rw [selGate_len]
    have := carrier_enc g M hL hP X gt hX
    omega
  have hG : (gl.flatMap GateConv.selGate).length ≤ gl.length * (6 * M) := len_flatMap_le gl _ _ hsg
  have hpops : ∀ P ∈ (FrontSelReq.selReqOf g).pops, (natListWord P.1 ++ ratWord P.2).length ≤
      (2 * (2 * (M * M)) + 3) + 2 * (M * M) * (2 * (2 * (M * (M * M)) + 2 * (M * M)) + 3) + (4 * M + 7) :=
    fun P hP => pop_len g M vs P hP _ _ hT hcar hcb
  have hPF := len_flatMap_le _ _ _ hpops
  have hpl : (FrontSelReq.selReqOf g).pops.length ≤ M := by
    simp only [FrontSelReq.selReqOf, FrontSelReq.selReqOn, List.length_mapIdx]; exact hvp
  have hgl' : (FrontSelReq.selReqOf g).gates.length = gl.length := by
    simp [FrontSelReq.selReqOf, FrontSelReq.selReqOn, hgl, hvs]
  have hgw : (FrontSelReq.selReqOf g).gates.flatMap (fun G => (List.ofFn fun i => intWord (G.weights i)).flatten ++
      intWord G.threshold) = gl.flatMap GateConv.selGate := by
    show ((vs.flatMap g.carrier).map FrontSelReq.toInt).flatMap _ = _
    exact GateConv.selGates_selWord _
  unfold Plan.selWord
  simp only [List.length_append]
  rw [hgw]
  have n1 := nw_le (FrontSelReq.selReqOf g).n
  have n2 := nw_le (FrontSelReq.selReqOf g).r
  have n3 := nw_le (FrontSelReq.selReqOf g).gates.length
  have n5 := nw_le (FrontSelReq.selReqOf g).pops.length
  have en : (FrontSelReq.selReqOf g).n = g.q := rfl
  have er : (FrontSelReq.selReqOf g).r = B.rOf g.q := rfl
  -- monomials
  obtain ⟨m2, hm2⟩ : ∃ x, x = M * M := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ x, x = M * (M * M) := ⟨_, rfl⟩
  -- gates part
  have hG2 : gl.length * (6 * M) ≤ 12 * (M * m3) := by
    have := Nat.mul_le_mul_right (6 * M) hT
    have e : 2 * (M * (M * M)) * (6 * M) = 12 * (M * m3) := by rw [hm3]; ring
    omega
  -- populations part
  have hP2 : (FrontSelReq.selReqOf g).pops.length * ((2 * (2 * (M * M)) + 3) +
      2 * (M * M) * (2 * (2 * (M * (M * M)) + 2 * (M * M)) + 3) + (4 * M + 7)) ≤ 40 * M ^ 6 := by
    refine (Nat.mul_le_mul_right _ hpl).trans ?_
    have e : M * ((2 * (2 * (M * M)) + 3) + 2 * (M * M) * (2 * (2 * (M * (M * M)) + 2 * (M * M)) + 3) +
        (4 * M + 7)) = 8 * M ^ 6 + 8 * M ^ 5 + 10 * M ^ 3 + 4 * M ^ 2 + 10 * M := by ring
    rw [e]
    have a5 : M ^ 5 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by norm_num)
    have a3 : M ^ 3 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by norm_num)
    have a2 : M ^ 2 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by norm_num)
    have a1 : M ^ 1 ≤ M ^ 6 := Nat.pow_le_pow_right hM (by norm_num)
    rw [pow_one] at a1
    omega
  have b4 : M * m3 ≤ M ^ 6 := by
    rw [hm3, show M * (M * (M * M)) = M ^ 4 by ring]; exact Nat.pow_le_pow_right hM (by norm_num)
  have b3 : M * (M * M) ≤ M ^ 6 := by
    rw [show M * (M * M) = M ^ 3 by ring]; exact Nat.pow_le_pow_right hM (by norm_num)
  have b1 : M ≤ M ^ 6 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 6 := Nat.pow_le_pow_right hM (by norm_num)
  have b0 : 1 ≤ M ^ 6 := Nat.one_le_pow _ _ hM
  obtain ⟨m6, hm6⟩ : ∃ x, x = M ^ 6 := ⟨_, rfl⟩
  rw [← hm6] at hP2 b4 b3 b1 b0 ⊢
  omega

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.C1Size
