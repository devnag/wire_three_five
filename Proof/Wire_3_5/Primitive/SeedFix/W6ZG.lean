import Proof.Wire_3_5.Primitive.SeedFix.W6ZF

/-! # W6, part 33: one polynomial capacity discharges the numbers machine's hypotheses

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231 (the THR call's numbers, `NumsPort4`'s "`need (n + cap_T) ≤ V`"): the
numbers machine keeps its values in word registers of width `2V+2`, so `V` must dominate every register value. With
`N = thrN alg P cap_T` and **`N^{48D+700} ≤ 2V+2`** every capacity hypothesis of `nums_run` holds:
* `clogS`, `pow_nbl` (`2^{bits(v)+1} ≤ 4v+4`), `ul_len` (`|unary list| = Σ + length`), `pl_len`, `pl_sum`;
* **`midB_of`** (`MidBounds` from `X^5 + 15 ≤ cap` and atoms `≤ X`), **`midA_of`** (`MidBoundsA` from `N^{4D+50} ≤ cap`);
* **`nums_run2`**: `nums_run` under `N^{48D+700} ≤ 2V+2` alone.

Paper quantities of the main type: the THR numbers `thrNumVals` on the out-ports, the count `V`, the call's base
`N`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

theorem clogS (x : ℕ) : Nat.clog 2 (x + 1) ≤ x + 1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

theorem pow_nbl (v : ℕ) : 2 ^ (natBitLength v + 1) ≤ 4 * v + 4 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with h | h
  · subst h; simp
  · have h1 := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h)
    rw [pow_succ, pow_succ]
    omega

theorem ul_len (cs : List ℕ) : (PrimAsm.Data.unaryList cs).length = cs.sum + cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [PrimAsm.Data.unaryList, List.flatMap_cons, List.length_append, List.length_replicate,
      List.length_singleton, List.sum_cons, List.length_cons, List.length_nil] at ih ⊢
    omega

theorem pl_len (c : ℕ) : (PrimThrW.Joins.primesList c).length ≤ c + 1 := by
  unfold PrimThrW.Joins.primesList
  exact (List.length_filter_le _ _).trans (by simp)

theorem pl_sum (c : ℕ) : (PrimThrW.Joins.primesList c).sum ≤ (c + 1) * c := by
  have h : ∀ x ∈ PrimThrW.Joins.primesList c, x ≤ c := by
    intro x hx
    unfold PrimThrW.Joins.primesList at hx
    have := List.mem_range.mp (List.mem_of_mem_filter hx)
    omega
  have h2 := List.sum_le_card_nsmul _ _ h
  rw [smul_eq_mul] at h2
  exact h2.trans (Nat.mul_le_mul_right _ (pl_len c))

/-- **`MidBounds` from one power**: every atom at most `X`, and `X^5 + 15 ≤ cap`. -/
theorem midB_of {cap X g pr d a nc ct K A B J M : ℕ} (hX : 4096 ≤ X) (hcap : X ^ 5 + 15 ≤ cap)
    (hg0 : g ≤ X) (hpr0 : pr ≤ X) (hd0 : d ≤ X) (ha0 : a ≤ X) (hnc0 : nc + 1 ≤ X) (hct0 : ct ≤ X) (hK0 : K ≤ X)
    (hA0 : A ≤ X) (hB0 : B ≤ X) (hJ0 : J ≤ X) (hM0 : M + 2 ≤ X) :
    MidBounds cap g pr d a nc ct K A B J M := by
  have p1 : ∀ {x : ℕ}, x ≤ X → x ≤ X ^ 1 := fun h => by rw [pow_one]; exact h
  have hg := p1 hg0; have hpr := p1 hpr0; have hd := p1 hd0; have ha := p1 ha0; have hnc := p1 hnc0
  have hct := p1 hct0; have hK := p1 hK0; have hA := p1 hA0; have hB := p1 hB0; have hJ := p1 hJ0; have hM := p1 hM0
  have c2 : 2 ≤ X ^ 1 := p1 (by omega)
  have c8 : 8 ≤ X ^ 1 := p1 (by omega)
  have c4096 : 4096 ≤ X ^ 1 := p1 (by omega)
  have lc : ∀ {x e : ℕ}, x ≤ X ^ e → e ≤ 5 → x + 15 ≤ cap := fun hx he => by
    have := pw_mono (by omega) hx he; omega
  constructor
  · have := lc (hd) (by norm_num); omega
  · have := lc (c2) (by norm_num); omega
  · have := lc (pw_mul hd c2) (by norm_num); omega
  · have := lc (hpr) (by norm_num); omega
  · have := lc (pw_mul hd c2) (by norm_num); omega
  · have := lc (pw_mul hpr (pw_mul hd c2)) (by norm_num); omega
  · have := lc (hg) (by norm_num); omega
  · have := lc (pw_mul hpr (pw_mul hd c2)) (by norm_num); omega
  · have := lc (pw_mul hg (pw_mul hpr (pw_mul hd c2))) (by norm_num); omega
  · have := lc (hct) (by norm_num); omega
  · have := lc (c4096) (by norm_num); omega
  · have := lc (pw_mul c4096 hct) (by norm_num); omega
  · have := lc (hnc) (by norm_num); omega
  · have := lc (hnc) (by norm_num); omega
  · have := lc (pw_mul c4096 hct) (by norm_num); omega
  · have := lc (pw_mul hnc (pw_mul c4096 hct)) (by norm_num); omega
  · have := lc (pw_mul c4096 (pw_mul hnc (pw_mul c4096 hct))) (by norm_num); omega
  · have := lc (ha) (by norm_num); omega
  · have := lc (pw_mul c4096 (pw_mul hnc (pw_mul c4096 hct))) (by norm_num); omega
  · have := lc (pw_mul ha (pw_mul c4096 (pw_mul hnc (pw_mul c4096 hct)))) (by norm_num); omega
  · have := lc (hK) (by norm_num); omega
  · have := lc (c8) (by norm_num); omega
  · have := lc (pw_mul c8 hK) (by norm_num); omega
  · have := lc (hA) (by norm_num); omega
  · have := lc (pw_mul c8 hK) (by norm_num); omega
  · have := lc (pw_mul (pw_mul c8 hK) hA) (by norm_num); omega
  · have := lc (hB) (by norm_num); omega
  · have := lc (pw_mul (pw_mul c8 hK) hA) (by norm_num); omega
  · have := lc (pw_mul (pw_mul (pw_mul c8 hK) hA) hB) (by norm_num); omega
  · have := lc (pw_mul (pw_mul (pw_mul c8 hK) hA) hB) (by norm_num); omega
  · have := lc (pw_mul (pw_mul (pw_mul c8 hK) hA) hB) (by norm_num); omega
  · have := lc (hK) (by norm_num); omega
  · have := lc (c8) (by norm_num); omega
  · have := lc (pw_mul c8 hK) (by norm_num); omega
  · have := lc (hA) (by norm_num); omega
  · have := lc (pw_mul c8 hK) (by norm_num); omega
  · have := lc (pw_mul (pw_mul c8 hK) hA) (by norm_num); omega
  · have := lc (hJ) (by norm_num); omega
  · have := lc (pw_mul (pw_mul c8 hK) hA) (by norm_num); omega
  · have := lc (pw_mul (pw_mul (pw_mul c8 hK) hA) hJ) (by norm_num); omega
  · have := lc (pw_mul (pw_mul (pw_mul c8 hK) hA) hJ) (by norm_num); omega
  · have := lc (pw_mul (pw_mul (pw_mul c8 hK) hA) hJ) (by norm_num); omega
  · have := lc (pw_mul (pw_mul (pw_mul c8 hK) hA) hJ) (by norm_num); have hc := clogS (8 * K * A * J); omega
  · have := lc (hJ) (by norm_num); omega
  · have := lc (hJ) (by norm_num); omega
  · have := lc (hM) (by norm_num); omega
  · have := lc (hM) (by norm_num); have hc : Nat.clog 2 M ≤ M := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le; omega
  · have := lc (hM) (by norm_num); have hc : Nat.clog 2 M ≤ M := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le; omega
  · have := lc hJ (by norm_num); have := lc hM (by norm_num); have hc : Nat.clog 2 M ≤ M := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le; omega

/-- **`MidBoundsA` from one power** `N^{4D+50} ≤ cap`. -/
theorem midA_of {N cap n g E D cut : ℕ} (hN : 16 ≤ N) (hcap : N ^ (4 * D + 50) ≤ cap) (hn : n ≤ N) (hg : g ≤ N ^ 4)
    (hE : E ≤ N ^ 2) (hcut : cut ≤ N ^ (2 * D + 24)) : MidBoundsA cap n g E D cut := by
  have lc : ∀ {x e : ℕ}, x ≤ N ^ e → e ≤ 4 * D + 50 → x ≤ cap := fun hx he => (pw_mono (by omega) hx he).trans hcap
  have hn1 : n ≤ N ^ 1 := by rw [pow_one]; exact hn
  have hK := bK hN g n D hg hn
  have hK' : 8 * ((g + 1) * n ^ D) ≤ N ^ (D + 6) := by rw [← mul_assoc]; exact hK
  have hc1 := pw_succ hN hcut 2 (by omega)
  have hpl := pl_len cut
  have hps := pl_sum cut
  have hul := ul_len (PrimThrW.Joins.primesList cut)
  have hcc : (cut + 1) * cut ≤ N ^ (2 * D + 24 + 1 + (2 * D + 24)) := pw_mul (pw_succ hN hcut 1 (by omega)) hcut
  have hsum : (cut + 1) * cut + (cut + 1) + cut + 3 ≤ N ^ (2 * D + 24 + 1 + (2 * D + 24) + 1) := by
    have h1 : cut ≤ N ^ (2 * D + 24 + 1 + (2 * D + 24)) := pw_mono (by omega) hcut (by omega)
    have h0 : 1 ≤ N ^ (2 * D + 24 + 1 + (2 * D + 24)) := Nat.one_le_pow _ _ (by omega)
    have hq1 := Nat.mul_le_mul_right (N ^ (2 * D + 24 + 1 + (2 * D + 24))) hN
    have hq2 := pow_succ' N (2 * D + 24 + 1 + (2 * D + 24))
    omega
  refine ⟨lc (pw_mono (by omega) hg (le_refl 4)) (by omega), lc hE (by omega), ?_, fun k hk => ?_, ?_, lc hn1 (by omega),
    lc (pw_succ hN hg 1 (by omega)) (by omega), lc hcut (by omega), lc hc1 (by omega), ?_, ?_⟩
  · have := lc (pw_succ hN hcut 1 (by omega)) (by omega); omega
  · exact lc ((Nat.pow_le_pow_left hn k).trans (Nat.pow_le_pow_right (by omega) hk)) (by omega)
  · exact lc (pw_succ hN hK' 8 (by omega)) (by omega)
  · have := lc hsum (by omega); omega
  · have := lc hsum (by omega); omega

variable (alg : DecompositionAlgorithm)

theorem fnw_len : fnw.length = 25 := by simp [fnw, PrimThrW.W6Meta.nw0_len]

/-- **The numbers machine under one polynomial capacity**: `nums_run` with every capacity hypothesis discharged from
`N^{48D+700} ≤ 2V+2`, `N` the call's base. -/
theorem nums_run2 (Dexp : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (codes : List ℕ) (tl : List Bool) (ncar capT V T : ℕ) (hn1 : 1 ≤ P.n) (ha : a' ≤ 4)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hok : PrimThrW.TopFront2.TF2Ok Cs codes V) (hnc : ncar ≤ 2)
    (hV : (thrN alg P capT) ^ (48 * Dexp + 700) ≤ 2 * V + 2)
    (hT : (tf alg).cost V + 1 + (11 * V + 20 + 1 + 1) + 1 + bodyB alg Dexp P Cs ncar capT V ≤ T) :
    ∃ J : Fin (TI alg + 1) → List Bool, (∀ j, (J j).length ≤ 2 * T + 3) ∧
      Step (numsM6 alg Dexp) (2 * T + 2) (fun _ => 0)
        (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool)
          (PrimThrW.Nums3.nums3InPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool)
          (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT)) J) := by
  have hN := thrN16 alg P capT
  have tb := (thr_basic alg P Cs capT ha hd)
  have cp : ∀ {x e : ℕ}, x ≤ (thrN alg P capT) ^ e → e ≤ 48 * Dexp + 700 → x ≤ 2 * V + 2 :=
    fun hx he => (pw_mono (by omega) hx he).trans hV
  have hn : P.n ≤ (thrN alg P capT) ^ 1 := by rw [pow_one]; exact tb.2.2.2.2.2.1
  have hct : capT ≤ (thrN alg P capT) ^ 1 := by rw [pow_one]; exact tb.2.2.2.2.2.2.1
  have c1 : 2 ^ (natBitLength P.n + 1) ≤ 2 * V + 2 := by
    have h := pow_nbl P.n
    have h2 := cp (pw_succ hN (pw_mul (show 4 ≤ (thrN alg P capT) ^ 1 by rw [pow_one]; omega) hn) 4 (by omega)) (by omega)
    omega
  have c2 : 2 ^ (natBitLength a' + 1) ≤ 2 * V + 2 := by
    have h := pow_nbl a'
    have h2 := cp (show 20 ≤ (thrN alg P capT) ^ 2 by nlinarith [pow_two (thrN alg P capT)]) (by omega)
    omega
  have c3 : 2 * (payF alg Cs 0 ++ payF alg Cs 1 ++ payF alg Cs 2 ++ payF alg Cs 3).length + 4 ≤ 2 * V + 2 :=
    cp (pw_two hN tb.2.2.2.2.1) (by omega)
  have c4 : 4 ≤ 2 * V + 2 := cp (show 4 ≤ (thrN alg P capT) ^ 1 by rw [pow_one]; omega) (by omega)
  have c5 : fnw.length ≤ 2 * V + 2 := by
    rw [fnw_len]; exact cp (show 25 ≤ (thrN alg P capT) ^ 2 by nlinarith [pow_two (thrN alg P capT)]) (by omega)
  have c6 : ∀ j, 2 ^ (natBitLength (szOf Cs j) + 1) + (Primitive.thrOccs P Cs).length ≤ 2 * V + 2 := by
    intro j
    have h := pow_nbl (szOf Cs j)
    have hs : szOf Cs j ≤ (thrN alg P capT) ^ 1 := by rw [pow_one]; exact tb.2.2.2.1 j
    have h4 := pw_mul (show 4 ≤ (thrN alg P capT) ^ 1 by rw [pow_one]; omega) hs
    have h5 := pw_add (by omega) (pw_succ hN h4 4 (by omega)) tb.2.2.1
    have h6 := cp h5 (by omega)
    omega
  have c7 : ncar ≤ 2 * V + 2 := by have := c4; omega
  have c8 : capT ≤ 2 * V + 2 := cp hct (by omega)
  have hX : 4096 ≤ (thrN alg P capT) ^ (5 * Dexp + 71) := by
    have h1 : 16 ^ 3 ≤ (thrN alg P capT) ^ 3 := Nat.pow_le_pow_left hN 3
    have h2 : (thrN alg P capT) ^ 3 ≤ (thrN alg P capT) ^ (5 * Dexp + 71) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (16 : ℕ) ^ 3 = 4096 := by norm_num
    omega
  have hcap5 : ((thrN alg P capT) ^ (5 * Dexp + 71)) ^ 5 + 15 ≤ 2 * V + 2 := by
    have h1 : ((thrN alg P capT) ^ (5 * Dexp + 71)) ^ 5 = (thrN alg P capT) ^ ((5 * Dexp + 71) * 5) := (pow_mul (thrN alg P capT) _ _).symm
    have h2 := cp (pw_succ hN (le_refl ((thrN alg P capT) ^ ((5 * Dexp + 71) * 5))) 15 (by omega)) (by omega)
    omega
  have X : ∀ {x e : ℕ}, x ≤ (thrN alg P capT) ^ e → e ≤ 5 * Dexp + 71 → x ≤ (thrN alg P capT) ^ (5 * Dexp + 71) :=
    fun hx he => pw_mono (by omega) hx he
  have hbC : MidBounds (2 * V + 2) (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).dig a' ncar capT (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M :=
    midB_of hX hcap5 (X (vb_nG alg Dexp P Cs ncar capT ha hd) (by omega)) (X (vb_nPr alg Dexp P Cs ncar capT ha hd) (by omega)) (X (vb_dig alg Dexp P Cs ncar capT ha hd) (by omega))
      (X (show a' ≤ (thrN alg P capT) ^ 1 by rw [pow_one]; omega) (by omega)) (X (show ncar + 1 ≤ (thrN alg P capT) ^ 1 by rw [pow_one]; omega) (by omega))
      (X hct (by omega)) (X (vb_den alg Dexp P Cs ncar capT ha hd) (by omega)) (X (vb_A alg Dexp P Cs ncar capT ha hd) (by omega)) (X (vb_Bs alg Dexp P Cs ncar capT ha hd hnc) (by omega))
      (X (vb_J alg Dexp P Cs ncar capT ha hd hnc) (by omega)) (X (pw_succ hN (vb_M alg Dexp P Cs ncar capT ha hd) 2 (by omega)) (by omega))
  have hbA : MidBoundsA (2 * V + 2) P.n (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG (familyMagnitudeExponent (Primitive.thrRealize P Cs alg)) Dexp (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut :=
    midA_of hN ((Nat.pow_le_pow_right (by omega) (by omega)).trans hV) tb.2.2.2.2.2.1 (vb_nG alg Dexp P Cs ncar capT ha hd) tb.2.1 (vb_cut alg Dexp P Cs ncar capT ha hd)
  have bE : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ee ≤ 2 * V + 2 := cp (vb_ee alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  have hneed : UnionMachine.EwSize.ewNeed ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den) ≤ 2 * V + 2 := by
    have Y : ∀ {x e : ℕ}, x ≤ (thrN alg P capT) ^ e → e ≤ 4 * Dexp + 54 → x ≤ (thrN alg P capT) ^ (4 * Dexp + 54) :=
      fun hx he => pw_mono (by omega) hx he
    exact cp (bEw hN _ _ _ _ _ (Y (vb_M alg Dexp P Cs ncar capT ha hd) (by omega)) (Y (vb_A alg Dexp P Cs ncar capT ha hd) (by omega)) (Y (vb_Bs alg Dexp P Cs ncar capT ha hd hnc) (by omega))
      (Y (vb_den alg Dexp P Cs ncar capT ha hd) (by omega))) (by omega)
  have hbg : 2 ^ ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 1) + 2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 4 ≤ 2 * V + 2 := by
    have h1 := vb_2ell alg Dexp P Cs ncar capT ha hd hnc
    have h2 := pw_two hN (vb_ell0 alg Dexp P Cs ncar capT ha hd hnc)
    have h3 := pw_add (by omega) h1 h2
    have h4 := cp h3 (by omega)
    omega
  have hbv : ∀ k, 2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get k + 4 ≤ 2 * V + 2 := fun k => cp (pw_two hN (vb_get alg Dexp P Cs ncar capT ha hd hnc k)) (by omega)
  exact nums_run alg Dexp P Cs codes tl ncar capT V T hn1 ha hd hok c1 c2 c3 c4 c5 c6 c7 c8 hbA hbC bE hneed hbg hbv hT

end NearCubicWires.WireExponent3_5.PrimT.W6
