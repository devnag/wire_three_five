import Proof.Wire_3_5.UnionMachine.FrontSemCap1

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
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (nvG twD)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEnt (esOf entOf)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1 (GEnv natWord_le natWord_bits frame_len flatMap_le)

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
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {g : UnionGuess S z} {Λ K : ℕ}

/-- **The table writer's data fits `BK K`.** -/
theorem bnd_of (hG : GEnv g Λ K) (hpA : S.parityAtom = unionParityAtom) (deg : ℕ) : (twD g deg).Bnd (BK K) := by
  have hp : (g.checkData g.translation).parityOf =
      unionParityAtom (g.checkData g.translation).mode (g.checkData g.translation).q := by
    show S.parityAtom g.mode g.q = unionParityAtom g.mode g.q; rw [hpA]
  have hnv := hG.nv
  have hq := hG.q
  have hs := hG.s
  have hnvD : (foldOf (g.checkData g.translation)).nv = nvG g := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans (frItems_le _ (2 * K + 15) ?_) ?_
    · intro w hw
      rw [List.mem_singleton] at hw
      subst hw
      show (natWord g.q ++ [_] ++ natWord 4).length ≤ _
      simp only [List.length_append, List.length_singleton]
      have := natWord_le g.q
      have := natWord_le 4
      omega
    · simp only [List.length_singleton, one_mul]; exact bk_hd K
  · refine le_trans (frItems_le _ K ?_) ?_
    · intro w hw; rw [List.mem_singleton] at hw; subst hw; exact hG.tr
    · simp only [List.length_singleton, one_mul]; exact bk_tl K
  · refine le_trans (frItems_le _ K ?_) ?_
    · intro w hw; rw [List.mem_singleton] at hw; subst hw; exact hG.cst
    · simp only [List.length_singleton, one_mul]; exact bk_tl K
  · refine le_trans (frItems_le _ K ?_) ?_
    · intro w hw
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hw
      have hX' : X < g.pcpp.systematicBits + g.pcpp.auxiliaryBits := List.mem_range.1 hX
      have e : (foldOf (g.checkData g.translation)).par X = (g.checkData g.translation).parity ⟨X, hX'⟩ :=
        FrontFoldSem.par_eq hp ⟨X, hX'⟩
      show (natWord (g.mode.code ((foldOf (g.checkData g.translation)).par X))).length ≤ K
      rw [e]
      exact hG.circ (Sum.inr (Sum.inr ⟨X, hX'⟩))
    · show ((List.range (foldOf (g.checkData g.translation)).nv).map _).length * _ ≤ _
      rw [List.length_map, List.length_range, hnvD]
      exact le_trans (Nat.mul_le_mul_right _ hnv) (bk_pc K)
  · refine le_trans (frItems_le _ (2 * K + 1) ?_) ?_
    · intro w hw
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hw
      have hX' : X < g.pcpp.systematicBits + g.pcpp.auxiliaryBits := List.mem_range.1 hX
      have e : (foldOf (g.checkData g.translation)).car X = (g.checkData g.translation).carrier ⟨X, hX'⟩ :=
        FrontFoldSem.car_eq hp ⟨X, hX'⟩
      show (natWord (Stars.Carrier.code ((foldOf (g.checkData g.translation)).car X))).length ≤ 2 * K + 1
      rw [e, natWord_bits]
      have hc : natBitLength (Stars.Carrier.code ((g.checkData g.translation).carrier ⟨X, hX'⟩)) ≤ K :=
        hG.car ⟨X, hX'⟩
      omega
    · show ((List.range (foldOf (g.checkData g.translation)).nv).map _).length * _ ≤ _
      rw [List.length_map, List.length_range, hnvD]
      exact le_trans (Nat.mul_le_mul_right _ hnv) (bk_cr K)
  · refine le_trans (entsW_le _ K ?_) ?_
    · intro e he
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      obtain ⟨X, a, rfl⟩ := (FrontDecode.mem_linE _ e').1 he'
      exact hG.circ (Sum.inr (Sum.inl (X, a)))
    · show (esOf g).length * _ ≤ _
      rw [FrontSemEnt.esOf_length]
      exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hnv hs)) (bk_es K)
  · show (List.replicate (nvG g * g.s) true).length ≤ _
    rw [List.length_replicate]
    exact le_trans (Nat.mul_le_mul hnv hs) (bk_df K)
  · show (List.replicate (nvG g) true).length ≤ _
    rw [List.length_replicate]
    exact le_trans hnv (le_trans (by omega) (bk_tl K))
  · show ((List.range (foldOf (g.checkData g.translation)).nv).map _).length ≤ _
    rw [List.length_map, List.length_range, hnvD]
    exact le_trans hnv (le_trans (by omega) (bk_tl K))

/-- **The PCPP output word fits `BK K`.** -/
theorem po_len (hG : GEnv g Λ K) : (pcppOutput (S.request z g.oracle) g.pcpp).length ≤ BK K := by
  have hnv : g.pcpp.systematicBits + g.pcpp.auxiliaryBits ≤ K := hG.nv
  have hq := hG.q
  have hcb := hG.cb
  have hcb' : g.pcpp.clauseBits ≤ K := le_trans (Nat.lt_two_pow_self (n := g.pcpp.clauseBits)).le hcb
  rw [FrontSemPO.pcppOutput_poWord, FrontSemPO.litsOf_eq]
  unfold C1Cnt.poWord
  simp only [List.length_append, FrontSemPO.sbOf_length]
  have hlen : (C1Ref.litsG g).length = 2 * 2 ^ g.pcpp.clauseBits := pairsOf_length _ _
  have hlt : ∀ x ∈ C1Ref.litsG g, x < 2 * (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) :=
    mem_pairsOf_lt _ _ (fun _ => literalIndex_lt _) (fun _ => literalIndex_lt _)
  have hfm := flatMap_le (C1Ref.litsG g) natWord (4 * K + 3) (fun x hx => by
    have := natWord_le x; have := hlt x hx; omega)
  have hfm' : (C1Ref.litsG g).length * (4 * K + 3) ≤ 8 * (K * K) + 6 * K := by
    rw [hlen]
    calc 2 * 2 ^ g.pcpp.clauseBits * (4 * K + 3) ≤ 2 * K * (4 * K + 3) := by gcongr
      _ = 8 * (K * K) + 6 * K := by ring
  have h3 : (natWord 3).length ≤ 9 := natWord_le 3
  have hs1 := natWord_le g.pcpp.systematicBits
  have hs2 := natWord_le g.pcpp.auxiliaryBits
  have hs3 := natWord_le g.pcpp.clauseBits
  have hs4 := natWord_le (C1Ref.litsG g).length
  have hsq : g.pcpp.systematicBits * (S.request z g.oracle).arity ≤ K * K := Nat.mul_le_mul (by omega) hq
  have hl2 : (C1Ref.litsG g).length ≤ 2 * K := by rw [hlen]; omega
  have := bk_po K
  omega

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
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {g : UnionGuess S z} {Λ K : ℕ} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The writer's cap facts at a guess** from its size envelope `GEnv g Λ K`, the width `W` above `PW K` and the
table's words, and the data bound `Kb (q+1)^{Db}` above `BK K` (the sparse bound and the tail's facts as given). -/
theorem endCaps_of (hG : GEnv g Λ K) (hpA : S.parityAtom = unionParityAtom)
    (hsg : (g.checkData g.translation).signsOk = true) {W Kb Db Cδ aV bV aT bT crT KT AT : ℕ}
    (hsS : g.s = Ledger.rowBSparse h0 h1 2 Cδ g.q) (hΛ : Λ = Ledger.rowBLambda h0 h1 2 g.q)
    (haV : aV ≤ K) (hbV : bV ≤ K) (haT : aT ≤ K) (hbT : bT ≤ K)
    (hsp : PrimAsm.SparseNum.sparseBound ζ Cδ (Ledger.Lq g.q) (Ledger.rowBt h0 h1 g.q - 1) ≤ 2 * W + 2)
    (hBK : BK K ≤ Kb * (g.q + 1) ^ Db) (hW1 : PW K ≤ W)
    (hW2 : FrontSemCap1.CN K * FrontSemCap1.EW K + 30 * (Kb * (g.q + 1) ^ Db) + 41 ≤ 2 * W + 2)
    (hW3 : Kb * (g.q + 1) ^ Db + Kb + (g.q + 1) ^ Db ≤ W)
    (hcr : 1 ≤ crT) (h4 : 4 * Ledger.rowBr crT g.q ≤ g.q) (hKT : 1 ≤ KT)
    (capW : KT * (g.q + 1) ^ AT + 1000 * (g.q + 7) + 2 * crT + 100 ≤ 2 * W + 2)
    (hpc : Ledger.Lq g.q ≤ FrontTail.capOf crT KT AT g.q)
    (hac : ∀ i, FrontOutRef.accStart S (g.checkData g.translation) (Ledger.Lq g.q) i ≤ FrontTail.capOf crT KT AT g.q)
    (haW : ∀ i, FrontOutRef.accStart S (g.checkData g.translation) (Ledger.Lq g.q) i ≤ 2 * W + 2) :
    FrontSemTW.EndCaps h0 h1 g W Kb Db Cδ aV bV aT bT crT KT AT := by
  have hnv : g.pcpp.systematicBits + g.pcpp.auxiliaryBits ≤ K := hG.nv
  have hq := hG.q
  have hs := hG.s
  have hl := hG.lam
  have hcb := hG.cb
  have hcb' : g.pcpp.clauseBits ≤ K := le_trans (Nat.lt_two_pow_self (n := g.pcpp.clauseBits)).le hcb
  have hsm := pw_small K
  have hbk := bk_po K
  have hLq : 2 ^ Ledger.Lq g.q ≤ 4 * (g.q + 1) := FrontCaps.two_pow_unionBits g.q
  have hLq' : Ledger.Lq g.q < 2 ^ Ledger.Lq g.q := Nat.lt_two_pow_self
  have hB := bnd_mono (bnd_of hG hpA I.carrierDeg) hBK
  have b1 := bits_le g.pcpp.systematicBits
  have b2 := bits_le g.pcpp.auxiliaryBits
  have b3 := bits_le g.pcpp.clauseBits
  have b4 := bits_le (2 * 2 ^ g.pcpp.clauseBits)
  have b0 : natBitLength 3 ≤ 8 := bits_le 3
  have hsq : g.pcpp.systematicBits * g.q ≤ K * K := Nat.mul_le_mul (by omega) hq
  have hvs : nvG g * g.s ≤ K * K := Nat.mul_le_mul hnv hs
  have hlit : 4 * nvG g * (g.s + 1) ≤ 4 * (K * K) + 4 * K := by
    calc 4 * nvG g * (g.s + 1) ≤ 4 * K * (K + 1) := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hnv) (by omega)
      _ = 4 * (K * K) + 4 * K := by ring
  refine
    { nv := FrontSemPath.nv_pos g
      bnd := hB
      hB := ?_
      hK := by omega
      hq4 := by omega
      hPw := fun k hk => le_trans (Nat.pow_le_pow_right (by omega) hk) (by omega)
      hB1 := by omega
      hB2 := ?_
      cq := le_trans (pow2_bits g.q) (by omega)
      c3 := le_trans (pow2_bits 3) (by omega)
      cs := le_trans (pow2_bits _) (by omega)
      ca := le_trans (pow2_bits _) (by omega)
      cc := le_trans (pow2_bits _) (by omega)
      hsp := hsp
      hc := ?_
      hthr := ?_
      po1 := by omega
      po2 := le_trans (po_len hG) hBK
      po3 := le_trans (by omega) (Nat.add_le_add_right (Nat.mul_le_mul_right 40 hBK) 200)
      var := by omega
      lit := by omega
      rdc := ?_
      mc := by omega
      tw := le_trans (Nat.add_le_add_right (Nat.add_le_add_right (FrontSemCap1.twWords_le hG hsg) _) _) hW2
      hcr := hcr
      h4 := h4
      hKT := hKT
      capW := capW
      hpc := hpc
      hac := hac
      hpW := by omega
      haW := haW }
  · have := natWord_le g.q
    omega
  · have := natWord_le 3
    have := natWord_le g.pcpp.systematicBits
    have := natWord_le g.pcpp.auxiliaryBits
    have := natWord_le g.pcpp.clauseBits
    omega
  · rw [← hsS, ← hΛ]
    exact le_trans (numCap_le _ _ _ _ _ _ K hs hl hq (by omega) (by omega) hcb' hcb) (by omega)
  · rw [← hsS, ← hΛ]
    have hS4 : g.s * g.s * g.s * g.s ≤ K * K * K * K := by gcongr
    exact le_trans (thrCap_le _ _ _ _ _ _ _ _ K hS4 (by omega) hcb hl haV hbV haT hbT) (by omega)
  · intro x hx
    have hx' : x < 2 * (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) :=
      mem_pairsOf_lt _ _ (fun _ => literalIndex_lt _) (fun _ => literalIndex_lt _) x hx
    exact le_trans (pow2_bits x) (by omega)

end Caps

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap2
