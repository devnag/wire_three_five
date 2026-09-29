import Proof.Wire_3_5.Primitive.Writers.PopSetupMath

/-! # PA POP setup, part 2: every capacity of `PopReady` below the need `U^40`

From `popNeed Pl L r4 G off ≤ cap` (`PopSetupMath.popNeed = U^40`), every capacity field `UnitReady.PopReady` reads at
the setup's explicit parameters (`popMlab`, `popLw`, `popCAP`, `popLL`, `popR`, `popCp`):
* **`numOps_eq`**, **`numF_le`**: the POP numbers program's forty registers, explicit (`numF`), and each below any `B`
  above the inputs and the log capacity; hence **`popHnum`** (`PopReady.hnum`);
* **`route_le`**: Route B's block bound `≤ U^9`, scrub capacity `popR ≤ U^30`, print bound `≤ U^5`, log capacity
  `popCp ≤ U^33`;
* **`fields_le`**, **`popRec_le`**: the POP row record's setup fields and states (at most `M + 1` states of `2t`
  blocks); hence **`popHbig`** (`PopReady.hbig`);
* **`PopCapFacts`** / **`popCapFacts`**: the twenty numeric capacity fields (`hcapC`, `hO`, `hcap`, `hdc`, …, `hcpc`).

Every capacity is a fixed power of `U = 2^20·popX`: none is super-polynomial in the need's measure.

Paper quantity of the main type: C2's POP row capacities (Route B, `PopCap.popKc`, `popPW`, `popCapB`) and the POP row
record's length, against the setup's need. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopSetupNeed
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.PopSetupMath

section NumF
open NearCubicWires.WireExponent3_5.PrimAsm.Arith NearCubicWires.WireExponent3_5.PrimAsm.PopNums

/-- The POP numbers' `Y`. -/
def numY (L c CAP : ℕ) : ℕ := 118 * L + 10 + 50 * (c + 1) ^ 3 + 2 * CAP + 100 * (4 * L + 1) ^ 2

/-- The POP numbers' `R`. -/
def numR (L d c CAP LL M lw Q : ℕ) : ℕ := 2 * blF L d c CAP LL lw M + Q * numY L c CAP + 7

/-- The POP numbers' `PW`. -/
def numPW (d Mlab Q : ℕ) : ℕ := Q * (2 * d * (Mlab + 1) + 2) + 1

/-- The POP numbers program's final registers, explicit. -/
def numF (L d c CAP LL M Mlab n lw Q : ℕ) : Fin 40 → ℕ :=
  ![L, d, c, CAP, LL, M, Mlab, n, lw, Q, blF L d c CAP LL lw M, numY L c CAP, numR L d c CAP LL M lw Q,
    numPW d Mlab Q, n * (8 * numR L d c CAP LL M lw Q + 2 * numPW d Mlab Q + 33) + 20, c + 1, (c + 1) * (c + 1),
    (c + 1) * (c + 1) * (c + 1), 4 * L + 1, (4 * L + 1) * (4 * L + 1), Mlab + 1, d * (Mlab + 1),
    numR L d c CAP LL M lw Q + 1, 2 * (d * (Mlab + 1)) + 2,
    8 * numR L d c CAP LL M lw Q + 2 * numPW d Mlab Q + 33, 0, 0, 0, 0, 0, 2, 4, 8, 50, 64, 100, 118, 128, 0, 0]

theorem numOps_eq (v : Fin 40 → ℕ) (hz : ∀ i : Fin 40, 10 ≤ i.val → v i = 0) :
    evalL v numOps = numF (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) := by
  have z10 : v 10 = 0 := hz 10 (by decide)
  have z11 : v 11 = 0 := hz 11 (by decide)
  have z12 : v 12 = 0 := hz 12 (by decide)
  have z13 : v 13 = 0 := hz 13 (by decide)
  have z14 : v 14 = 0 := hz 14 (by decide)
  have z15 : v 15 = 0 := hz 15 (by decide)
  have z16 : v 16 = 0 := hz 16 (by decide)
  have z17 : v 17 = 0 := hz 17 (by decide)
  have z18 : v 18 = 0 := hz 18 (by decide)
  have z19 : v 19 = 0 := hz 19 (by decide)
  have z20 : v 20 = 0 := hz 20 (by decide)
  have z21 : v 21 = 0 := hz 21 (by decide)
  have z22 : v 22 = 0 := hz 22 (by decide)
  have z23 : v 23 = 0 := hz 23 (by decide)
  have z24 : v 24 = 0 := hz 24 (by decide)
  have z25 : v 25 = 0 := hz 25 (by decide)
  have z26 : v 26 = 0 := hz 26 (by decide)
  have z27 : v 27 = 0 := hz 27 (by decide)
  have z28 : v 28 = 0 := hz 28 (by decide)
  have z29 : v 29 = 0 := hz 29 (by decide)
  have z30 : v 30 = 0 := hz 30 (by decide)
  have z31 : v 31 = 0 := hz 31 (by decide)
  have z32 : v 32 = 0 := hz 32 (by decide)
  have z33 : v 33 = 0 := hz 33 (by decide)
  have z34 : v 34 = 0 := hz 34 (by decide)
  have z35 : v 35 = 0 := hz 35 (by decide)
  have z36 : v 36 = 0 := hz 36 (by decide)
  have z37 : v 37 = 0 := hz 37 (by decide)
  have z38 : v 38 = 0 := hz 38 (by decide)
  have z39 : v 39 = 0 := hz 39 (by decide)
  funext i
  simp only [numOps, constOps, blOps, rOps, pwOps, List.cons_append, List.nil_append, evalL, AOp.eval,
    Function.update_apply]
  fin_cases i <;> simp (config := { decide := true }) only [↓reduceIte, Fin.isValue] <;>
    simp only [numF, numY, numR, numPW, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19, z20, z21, z22, z23, z24,
      z25, z26, z27, z28, z29, z30, z31, z32, z33, z34, z35, z36, z37, z38, z39, blF, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- **Every register of the POP numbers program is at most `B`**, from the inputs, `Mlab + 1`, `8R + 2PW + 33` and
the log capacity at most `B` (and `1 ≤ Q`). -/
theorem numF_le (L d c CAP LL M Mlab n lw Q B : ℕ) (hB : 128 ≤ B) (hL : L ≤ B) (hd : d ≤ B) (hc : c ≤ B)
    (hCAP : CAP ≤ B) (hLL : LL ≤ B) (hM : M ≤ B) (hMl : Mlab + 1 ≤ B) (hn : n ≤ B) (hlw : lw ≤ B) (hQ : Q ≤ B)
    (hQ1 : 1 ≤ Q) (h24 : 8 * numR L d c CAP LL M lw Q + 2 * numPW d Mlab Q + 33 ≤ B)
    (h14 : n * (8 * numR L d c CAP LL M lw Q + 2 * numPW d Mlab Q + 33) + 20 ≤ B) :
    ∀ i, numF L d c CAP LL M Mlab n lw Q i ≤ B := by
  have eR : numR L d c CAP LL M lw Q = 2 * blF L d c CAP LL lw M + Q * numY L c CAP + 7 := rfl
  have eP : numPW d Mlab Q = Q * (2 * d * (Mlab + 1) + 2) + 1 := rfl
  have eY : numY L c CAP = 118 * L + 10 + 50 * (c + 1) ^ 3 + 2 * CAP + 100 * (4 * L + 1) ^ 2 := rfl
  have hQY : numY L c CAP ≤ Q * numY L c CAP := Nat.le_mul_of_pos_left _ hQ1
  have hQP : 2 * d * (Mlab + 1) + 2 ≤ Q * (2 * d * (Mlab + 1) + 2) := Nat.le_mul_of_pos_left _ hQ1
  have e3 : (c + 1) ^ 3 = (c + 1) * (c + 1) * (c + 1) := by ring
  have e2 : (4 * L + 1) ^ 2 = (4 * L + 1) * (4 * L + 1) := by ring
  have em : 2 * d * (Mlab + 1) = 2 * (d * (Mlab + 1)) := by ring
  have c1 : c + 1 ≤ (c + 1) * (c + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have c2 : (c + 1) * (c + 1) ≤ (c + 1) * (c + 1) * (c + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have l1 : 4 * L + 1 ≤ (4 * L + 1) * (4 * L + 1) := Nat.le_mul_of_pos_left _ (by omega)
  intro i
  fin_cases i <;>
    simp only [numF, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue] <;> omega

end NumF


/-! ## Route B's capacities and the record's length as powers of `U` -/

section Caps
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
variable (Pl : FlatListParams) (L r4 G off : ℕ)

theorem popR_eq : popR Pl r4 G off L = numR L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
    (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) := by
  unfold popR PopCap.popKc numR numY; ring

theorem popPW_eq : PopCap.popPW L (3 * lbP Pl) (popMlab r4 G off L) =
    numPW (3 * lbP Pl) (popMlab r4 G off L) ((8 * L + 2) ^ (3 * lbP Pl)) := by
  unfold PopCap.popPW numPW; ring

theorem popCp_eq : popCp Pl r4 G off L = Pl.walkLen * (8 * popR Pl r4 G off L +
    2 * PopCap.popPW L (3 * lbP Pl) (popMlab r4 G off L) + 33) + 20 := by
  unfold popCp PopCap.popCapB; ring

/-- **The block bound, the scrub capacity, the print bound and the log capacity as powers of `U`.** -/
theorem route_le :
    PopNums.blF L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) (popLw Pl L) Pl.M ≤
      popU Pl L r4 G off ^ 9 ∧
    popR Pl r4 G off L ≤ popU Pl L r4 G off ^ 30 ∧
    PopCap.popPW L (3 * lbP Pl) (popMlab r4 G off L) ≤ popU Pl L r4 G off ^ 5 ∧
    8 * popR Pl r4 G off L + 2 * PopCap.popPW L (3 * lbP Pl) (popMlab r4 G off L) + 33 ≤ popU Pl L r4 G off ^ 31 ∧
    popCp Pl r4 G off L ≤ popU Pl L r4 G off ^ 33 := by
  obtain ⟨h1, h2, h3, h4, -, h6, -, -, -, -, -, -, -, h14, h15, h16, h17, h18, hU⟩ := basic Pl L r4 G off
  rw [popCp_eq, popR_eq, popPW_eq]
  unfold numR numY numPW
  generalize (8 * L + 2) ^ (3 * lbP Pl) = Q at *
  generalize capP Pl L = c at *
  generalize popMlab r4 G off L = Ml at *
  generalize 3 * lbP Pl = d at *
  generalize popU Pl L r4 G off = U at *
  have e1 : U ^ 1 = U := pow_one U
  have p13 := pw_lt hU (show 1 < 3 by norm_num)
  have p37 := pw_lt hU (show 3 < 7 by norm_num)
  have p78 := pw_lt hU (show 7 < 8 by norm_num)
  have p89 := pw_lt hU (show 8 < 9 by norm_num)
  have hBL : PopNums.blF L d c (popCAP r4 G off L) (popLL r4 G off L) (popLw Pl L) Pl.M ≤ U ^ 9 := by
    unfold PopNums.blF; omega
  have hc1 : c + 1 ≤ U ^ 9 := by omega
  have hc3 : (c + 1) ^ 3 ≤ U ^ 27 := by
    calc (c + 1) ^ 3 ≤ (U ^ 9) ^ 3 := Nat.pow_le_pow_left hc1 3
      _ = U ^ 27 := by ring
  have hL4 : (4 * L + 1) ^ 2 ≤ (4 * U) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e16 : (4 * U) ^ 2 = 16 * U ^ 2 := by ring
  have p23 := pw_lt hU (show 2 < 3 by norm_num)
  have p327 := pw_lt hU (show 3 < 27 by norm_num)
  have p2728 := pw_lt hU (show 27 < 28 by norm_num)
  have p12 := pw_lt hU (show 1 < 2 by norm_num)
  have hY : 118 * L + 10 + 50 * (c + 1) ^ 3 + 2 * popCAP r4 G off L + 100 * (4 * L + 1) ^ 2 ≤ U ^ 28 := by omega
  have hQY : Q * (118 * L + 10 + 50 * (c + 1) ^ 3 + 2 * popCAP r4 G off L + 100 * (4 * L + 1) ^ 2) ≤ U ^ 29 := by
    calc _ ≤ U * U ^ 28 := Nat.mul_le_mul (by omega) hY
      _ = U ^ 29 := by ring
  have p929 := pw_lt hU (show 9 < 29 by norm_num)
  have p2930 := pw_lt hU (show 29 < 30 by norm_num)
  have hR : 2 * PopNums.blF L d c (popCAP r4 G off L) (popLL r4 G off L) (popLw Pl L) Pl.M +
      Q * (118 * L + 10 + 50 * (c + 1) ^ 3 + 2 * popCAP r4 G off L + 100 * (4 * L + 1) ^ 2) + 7 ≤ U ^ 30 := by omega
  have hdm : d * (Ml + 1) ≤ U * U := Nat.mul_le_mul (by omega) h6
  have e2 : U * U = U ^ 2 := by ring
  have hin : 2 * d * (Ml + 1) + 2 ≤ U ^ 3 := by
    have : 2 * d * (Ml + 1) = 2 * (d * (Ml + 1)) := by ring
    omega
  have hQP : Q * (2 * d * (Ml + 1) + 2) ≤ U ^ 4 := by
    calc _ ≤ U * U ^ 3 := Nat.mul_le_mul (by omega) hin
      _ = U ^ 4 := by ring
  have p45 := pw_lt hU (show 4 < 5 by norm_num)
  have p531 := pw_lt hU (show 5 < 31 by norm_num)
  have p3031 := pw_lt hU (show 30 < 31 by norm_num)
  have hT : 8 * (2 * PopNums.blF L d c (popCAP r4 G off L) (popLL r4 G off L) (popLw Pl L) Pl.M +
      Q * (118 * L + 10 + 50 * (c + 1) ^ 3 + 2 * popCAP r4 G off L + 100 * (4 * L + 1) ^ 2) + 7) +
      2 * (Q * (2 * d * (Ml + 1) + 2) + 1) + 33 ≤ U ^ 31 := by omega
  have p3233 := pw_lt hU (show 32 < 33 by norm_num)
  have hcp := Nat.mul_le_mul h4 hT
  have e32 : U * U ^ 31 = U ^ 32 := by ring
  have q4 : 1 ≤ U ^ 4 := Nat.one_le_pow _ _ (by omega)
  have q32 : 1 ≤ U ^ 32 := Nat.one_le_pow _ _ (by omega)
  refine ⟨hBL, hR, by omega, hT, by omega⟩

end Caps

section Big
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord polyWord recW monoBits recW_length)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

theorem flatMap_len_le {α β : Type} (l : List α) (f : α → List β) (K : ℕ) (h : ∀ a ∈ l, (f a).length ≤ K) :
    (l.flatMap f).length ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, add_mul, one_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    omega

theorem setupF_le (u n θ R Lg cp : ℕ) :
    ∀ i, (setupF u n θ R Lg cp i).length ≤ R + Lg + 4 * n + θ + cp + 4 := by
  intro i
  unfold setupF
  split_ifs <;> simp only [List.length_replicate, frame_len, binary_length, List.length_append, List.length_cons,
    List.length_nil] <;> omega

theorem fields_le (u n θ R Lg cp : ℕ) :
    (fieldsWord (setupFields u n θ R Lg cp)).length ≤ 9 * (2 * (R + Lg + 4 * n + θ + cp + 4) + 1) := by
  unfold fieldsWord setupFields
  rw [List.flatMap_map]
  have h := flatMap_len_le (targetsQ u) (fun a => frame (setupF u n θ R Lg cp a)) (2 * (R + Lg + 4 * n + θ + cp + 4) + 1)
    (fun a _ => by rw [frame_len]; have := setupF_le u n θ R Lg cp a; omega)
  have h9 : (targetsQ u).length = 9 := rfl
  rw [h9] at h
  exact h

theorem oneWC_le (P : FlatListParams) (s : Fin (P.M + 1)) : (oneWC P s).length ≤ 4 * P.walkLen + 7 := by
  unfold oneWC popOne
  have hc : (coefWord 1).length = 5 := by decide
  split_ifs
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_cons, termWord, List.length_append,
      hc, List.length_flatMap, List.map_replicate, List.sum_replicate, polyWord, recW_length,
      smul_eq_mul, List.length_nil, List.flatMap_nil]
    simp [monoBits]
    omega
  · simp

theorem statesC_len (P : FlatListParams) (s : Fin (P.M + 1)) : (statesC P s).length ≤ P.M + 1 := by
  unfold statesC; split_ifs <;> simp

theorem statesC_coef (P : FlatListParams) (s : Fin (P.M + 1)) : ∀ st ∈ statesC P s, (coefWord st.1).length = 5 := by
  intro st hst
  unfold statesC at hst
  split_ifs at hst
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hst
    show (coefWord (-1)).length = 5
    decide
  · rw [List.mem_singleton] at hst
    subst hst
    show (coefWord 1).length = 5
    decide

theorem blocksC_len (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ) (s' : Fin (P.M + 1)) :
    (blocksC P e L sgn labs s').length = 2 * P.walkLen := by
  simp [blocksC, List.length_flatMap, mul_comm]

theorem mem_blocksC (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ) (s' : Fin (P.M + 1))
    (b : List Bool) (hb : b ∈ blocksC P e L sgn labs s') :
    ∃ k : Fin P.walkLen, ∃ neg : Bool, b = blockC (visitData P e k) L s'.val sgn neg labs := by
  unfold blocksC at hb
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · exact ⟨k, true, rfl⟩
  · exact ⟨k, false, rfl⟩

theorem popRec_le (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ)
    (hlabs : 4 * L ≤ labs.length) (s : Fin (P.M + 1)) (BL : ℕ)
    (hBL : ∀ (s' : Fin (P.M + 1)) (k : Fin P.walkLen) (neg : Bool),
      2 * (blockC (visitData P e k) L s'.val sgn neg labs).length + 2 ≤ BL) :
    (popRec (oneWC P s) (popStates P e L sgn labs hlabs s)).length ≤
      2 * (4 * P.walkLen + 7) + 1 + (P.M + 1) * (2 * P.walkLen * BL + 13) + 1 := by
  unfold popRec
  rw [popStates_eq, List.flatMap_map, List.length_append, List.length_append, frame_len]
  have hst : ∀ st ∈ statesC P s, (srec (st.1, visitFs P e L sgn labs hlabs st.2)).length ≤ 2 * P.walkLen * BL + 13 := by
    intro st hmem
    simp only [srec, stateRec, List.length_cons, List.length_append, frame_len, statesC_coef P s st hmem]
    rw [storeRec_visitFs, List.length_append, List.length_singleton]
    have h := flatMap_len_le (blocksC P e L sgn labs st.2) (fun b => true :: b) BL (fun b hb => by
      obtain ⟨k, neg, rfl⟩ := mem_blocksC P e L sgn labs st.2 b hb
      have := hBL st.2 k neg
      simp only [List.length_cons]
      omega)
    rw [blocksC_len] at h
    omega
  have h1 := flatMap_len_le (statesC P s) (fun st => srec (st.1, visitFs P e L sgn labs hlabs st.2)) _ hst
  have h2 := statesC_len P s
  have h3 := oneWC_le P s
  have h4 : (statesC P s).length * (2 * P.walkLen * BL + 13) ≤ (P.M + 1) * (2 * P.walkLen * BL + 13) :=
    Nat.mul_le_mul_right _ h2
  simp only [List.length_singleton]
  omega

end Big


/-! ## Every capacity field of `PopReady` from `popNeed ≤ cap` -/

section Fields
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
open NearCubicWires.WireExponent3_5.PrimAsm.Arith
variable (Pl : FlatListParams) (L r4 G off cap : ℕ)

theorem need_pow (hcap : popNeed Pl L r4 G off ≤ cap) {a i : ℕ} (hi : i ≤ 40) (ha : a ≤ popU Pl L r4 G off ^ i) :
    a ≤ cap := by
  have hU := u_ge Pl L r4 G off
  exact le_trans (u_mono (by omega) ha hi) hcap

/-- The numeric capacity fields of `PopReady` (all but `hnum`, `hbig`). -/
structure PopCapFacts : Prop where
  hcapC : 8 * Flat.sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ cap
  hO : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < cap
  hcap : LevelW.lvCap (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) Pl.base.J Pl.base.J ≤ cap
  hdc : 3 * lbP Pl ≤ cap
  hJc : Pl.base.J + 1 ≤ cap
  hSc : CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) ≤ cap
  hlwc : popLw Pl L ≤ cap
  hMc : Pl.M ≤ cap
  hcL : 4 * L ≤ cap
  hcap3 : L * (4 * (4 * popMlab r4 G off L + 4)) + 5 + L * (4 * (2 * popMlab r4 G off L + 10)) +
    4 * (4 * popMlab r4 G off L + 4) + 4 * (2 * popMlab r4 G off L + 10) + 7 * popMlab r4 G off L + r4 + G + off +
    L + 20 ≤ cap
  hac3 : popCAP r4 G off L + popLL r4 G off L ≤ cap
  hQc : (8 * L + 2) ^ (3 * lbP Pl) * (8 * L + 2) + 2 ≤ cap
  hc4 : capP Pl L + 8 ≤ cap
  hin2 : L + capP Pl L + Pl.M + popMlab r4 G off L + Pl.walkLen ≤ cap
  h2c : 2 ≤ cap
  hcV : (Pl.base.J + 1) * (2 * L + 1) + 1 ≤ cap
  hcT : Pl.walkLen * ((Pl.base.J + 1) * (2 * L + 1) + 1) ≤ cap
  hθc : SupplierWalk.majorityThreshold Pl.walkLen ≤ cap
  hRc1 : popR Pl r4 G off L + 1 ≤ cap
  hcpc : popCp Pl r4 G off L ≤ cap

theorem popCapFacts (hcap : popNeed Pl L r4 G off ≤ cap) : PopCapFacts Pl L r4 G off cap := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hU⟩ :=
    basic Pl L r4 G off
  obtain ⟨-, hR, -, -, hcp⟩ := route_le Pl L r4 G off
  have htJ := twoJ_le Pl L r4 G off
  have hN := popNeed_le Pl L r4 G off
  unfold popNeed at hcap
  generalize popU Pl L r4 G off = U at *
  have e1 : U ^ 1 = U := pow_one U
  have p140 := pw_lt hU (show 1 < 40 by norm_num)
  have p340 := pw_lt hU (show 3 < 40 by norm_num)
  have p740 := pw_lt hU (show 7 < 40 by norm_num)
  have p840 := pw_lt hU (show 8 < 40 by norm_num)
  have p3040 := pw_lt hU (show 30 < 40 by norm_num)
  have p3340 := pw_lt hU (show 33 < 40 by norm_num)
  have p240 := pw_lt hU (show 2 < 40 by norm_num)
  have p440 := pw_lt hU (show 4 < 40 by norm_num)
  have e2 : U * U = U ^ 2 := by ring
  have e3 : U * U ^ 2 = U ^ 3 := by ring
  have hJL : (Pl.base.J + 1) * (2 * L + 1) ≤ U * (2 * U) := Nat.mul_le_mul h8 (by omega)
  have eJL : U * (2 * U) = 2 * U ^ 2 := by ring
  have hE : 2 * (Pl.errExp / 4) + 1 ≤ U := by omega
  have hOm : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) ≤ U * (1 + 2 * U ^ 2) :=
    Nat.mul_le_mul hE (by omega)
  have eO : U * (1 + 2 * U ^ 2) = U + 2 * U ^ 3 := by ring
  have hTm : Pl.walkLen * ((Pl.base.J + 1) * (2 * L + 1) + 1) ≤ U * (2 * U ^ 2 + 1) := Nat.mul_le_mul h4 (by omega)
  have eT : U * (2 * U ^ 2 + 1) = 2 * U ^ 3 + U := by ring
  have hj3 : 2 ^ (Pl.base.J / 3) ≤ 2 ^ Pl.base.J := Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)
  have hA : L * (4 * (4 * popMlab r4 G off L + 4)) ≤ U * (16 * U) := Nat.mul_le_mul (by omega) (by omega)
  have hB : L * (4 * (2 * popMlab r4 G off L + 10)) ≤ U * (8 * U + 40) := Nat.mul_le_mul (by omega) (by omega)
  have eA : U * (16 * U) = 16 * U ^ 2 := by ring
  have eB : U * (8 * U + 40) = 8 * U ^ 2 + 40 * U := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (try unfold LevelW.lvCap)
  all_goals omega

/-- **`PopReady.hnum`**: every register of the POP numbers program is within the capacity. -/
theorem popHnum (hcap : popNeed Pl L r4 G off ≤ cap) :
    ∀ i, evalL (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl))) PopNums.numOps i ≤ cap := by
  rw [numOps_eq _ (PopCellNum.vIn_zero _ _ _ _ _ _ _ _ _ _)]
  have ev : numF (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 0)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 1)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 2)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 3)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 4)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 5)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 6)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 7)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 8)
      (PopCellNum.vIn L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) 9) =
      numF L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) Pl.M
      (popMlab r4 G off L) Pl.walkLen (popLw Pl L) ((8 * L + 2) ^ (3 * lbP Pl)) := rfl
  rw [ev]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hU⟩ :=
    basic Pl L r4 G off
  obtain ⟨-, -, -, hT, hcp⟩ := route_le Pl L r4 G off
  rw [popR_eq, popPW_eq] at hT
  rw [popCp_eq, popR_eq, popPW_eq] at hcp
  have hQ1 : 1 ≤ (8 * L + 2) ^ (3 * lbP Pl) := Nat.one_le_pow _ _ (by omega)
  have g : ∀ {a i : ℕ}, i ≤ 40 → a ≤ popU Pl L r4 G off ^ i → a ≤ cap := fun hi ha =>
    need_pow Pl L r4 G off cap hcap hi ha
  have hU1 : popU Pl L r4 G off ≤ popU Pl L r4 G off ^ 1 := by rw [pow_one]
  have hB : popU Pl L r4 G off ≤ cap := g (by norm_num) hU1
  exact numF_le _ _ _ _ _ _ _ _ _ _ cap (by omega) (by omega) (by omega) (g (by norm_num) h16) (g (by norm_num) h17)
    (g (by norm_num) h18) (by omega) (by omega) (by omega) (g (by norm_num) h15) (by omega) hQ1
    (g (by norm_num) hT) (g (by norm_num) hcp)

end Fields


section Hbig
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
variable (Pl : FlatListParams) (L r4 G off cap : ℕ)

/-- **`PopReady.hbig`**: the POP row record, the FILTER bank's first fields and the label fields fit the capacity. -/
theorem popHbig (hcap : popNeed Pl L r4 G off ≤ cap) (e : Pl.FlatSeed) (sgn : Bool) (s : Fin (Pl.M + 1))
    (hlabs : 4 * L ≤ (Emit.sliceLabs r4 G off L).length) :
    (frame (popRowRec Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) (popR Pl r4 G off L)
      (popR Pl r4 G off L + 1) (popCp Pl r4 G off L) (oneWC Pl s)
      (popStates Pl e L sgn (Emit.sliceLabs r4 G off L) hlabs s))).length + 2 +
      PopBlockW.labCapA (4 * L) (3 * lbP Pl) + (FiltRecW.pieceA (4 * L) (3 * lbP Pl)).length +
      PopBlockW.labCapB r4 G off L (popMlab r4 G off L) ≤ cap := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hU⟩ :=
    basic Pl L r4 G off
  obtain ⟨hBL, hR, -, -, hcp⟩ := route_le Pl L r4 G off
  have hrec := popRec_le Pl e L sgn (Emit.sliceLabs r4 G off L) hlabs s
    (PopNums.blF L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) (popLw Pl L) Pl.M)
    (fun s' k neg => blockC_le Pl e L k s'.val (Nat.le_of_lt_succ s'.isLt) sgn neg _ (sliceLabs_length r4 G off L))
  have hf := fields_le (negFam F35).t Pl.walkLen (SupplierWalk.majorityThreshold Pl.walkLen) (popR Pl r4 G off L)
    (popR Pl r4 G off L + 1) (popCp Pl r4 G off L)
  unfold popRowRec
  rw [frame_len, List.length_append, FiltRecW.A_len]
  unfold PopBlockW.labCapA PopBlockW.labCapB
  rw [show ((Emit.sliceLabs r4 G off L).flatMap labE).length = popLL r4 G off L from rfl,
    show labSum (Emit.sliceLabs r4 G off L) = popCAP r4 G off L from rfl]
  generalize PopNums.blF L (3 * lbP Pl) (capP Pl L) (popCAP r4 G off L) (popLL r4 G off L) (popLw Pl L) Pl.M =
    BL at hrec hBL
  unfold popNeed at hcap
  generalize popU Pl L r4 G off = U at *
  have e1 : U ^ 1 = U := pow_one U
  have hnB : Pl.walkLen * BL ≤ U * U ^ 9 := Nat.mul_le_mul h4 hBL
  have e10 : U * U ^ 9 = U ^ 10 := by ring
  have e2n : 2 * Pl.walkLen * BL = 2 * (Pl.walkLen * BL) := by ring
  have hMn : (Pl.M + 1) * (2 * Pl.walkLen * BL + 13) ≤ U * (2 * U ^ 10 + 13) :=
    Nat.mul_le_mul h3 (by omega)
  have eM : U * (2 * U ^ 10 + 13) = 2 * U ^ 11 + 13 * U := by ring
  have hA : L * (4 * (4 * popMlab r4 G off L + 4)) ≤ U * (16 * U) := Nat.mul_le_mul (by omega) (by omega)
  have hB : L * (4 * (2 * popMlab r4 G off L + 10)) ≤ U * (8 * U + 40) := Nat.mul_le_mul (by omega) (by omega)
  have eA : U * (16 * U) = 16 * U ^ 2 := by ring
  have eB : U * (8 * U + 40) = 8 * U ^ 2 + 40 * U := by ring
  have p12 := pw_lt hU (show 1 < 2 by norm_num)
  have p23 := pw_lt hU (show 2 < 3 by norm_num)
  have p311 := pw_lt hU (show 3 < 11 by norm_num)
  have p1130 := pw_lt hU (show 11 < 30 by norm_num)
  have p3033 := pw_lt hU (show 30 < 33 by norm_num)
  have p3340 := pw_lt hU (show 33 < 40 by norm_num)
  omega

end Hbig

end NearCubicWires.WireExponent3_5.PrimAsm.PopSetupNeed
