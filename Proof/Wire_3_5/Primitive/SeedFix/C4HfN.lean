import Proof.Wire_3_5.Primitive.SeedFix.C4HfM

/-! # The HASH child family, part 14: the family and C4H-a's interface

`filt:soft`, P3:2331-2335: **`chFamH`**, the HASH call's child family (`C4Loop.ChildFam`): one child machine per
candidate bit (the HASH child under base's masked reset), whose sum port holds the recovered child sum
`chValH (p ++ [b])` below `2^W`, the kept tapes unchanged, within `2·Kch + 2` steps, at every prefix shorter than
`s_h`; the side conditions are C4H's `HashEAt` and the capacity `2t·ℓ₀ ≤ cC` (`caps_ge`).
**`hashFamAt2`**: the family at C4H-a's interface (`HashFamAt2`), given the loop's decisions.

Paper quantity of the main types: the HASH decision's children, their recovered sums, and the loop's decisions. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairRepresentation

noncomputable section

theorem hAddL {α : Type} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) (v : ℕ) (h : v < m + n) (hv : v < m) :
    Fin.addCases (motive := fun _ => α) f g ⟨v, h⟩ = f ⟨v, hv⟩ := by
  have e : (⟨v, h⟩ : Fin (m + n)) = Fin.castAdd n ⟨v, hv⟩ := rfl
  rw [e, Fin.addCases_left]

theorem hAddR {α : Type} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) (v : ℕ) (h : v < m + n) (hv : m ≤ v) :
    Fin.addCases (motive := fun _ => α) f g ⟨v, h⟩ = g ⟨v - m, by omega⟩ := by
  have e : (⟨v, h⟩ : Fin (m + n)) = Fin.natAdd m ⟨v - m, by omega⟩ := Fin.ext (by simp; omega)
  rw [e, Fin.addCases_right]

section Fam
variable (A : C4Iface.AsmStage) (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm)
  (R0 : CompilerMachine.Req.C3Req) (D : HashData) (c : HbCaps)

/-- **One HASH child's run** under base's masked reset: the sum port holds `frame (binary W (chValH (p ++ [b])))`,
the kept tapes unchanged, within `2·Kch + 2` steps. -/
theorem ch_runH (E : Cost.Envelope) (Kc Kch : ℕ) (b : Bool) (p : List Bool)
    (hplen : p.length + 1 ≤ 2 * D.MP.t * D.MP.ell0) (hcC : 2 * D.MP.t * D.MP.ell0 ≤ c.cC)
    (hok : (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).HbOk)
    (hcell : ∀ cc < (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).n,
      (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).CellOk cc ∧
      (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).cellCost cc ≤ Kc)
    (hRp : (hR R0 D (p ++ [b])).Pre a) (hQp : R0.P.Q ≤ R0.p)
    (hcost : ∀ r : MatrixScoreBatch.Request,
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
        (CompilerMachine.Req.c3v2Ref a (hR R0 D (p ++ [b]))) →
      hCoreCost wa a R0 D c Kc (p ++ [b]) r ≤ Kch) :
    ∃ A'' : Fin (CTH A wa + 1) → List Bool,
      Step (chMH A wa b) (2 * Kch + 2) (fun _ => 0)
        (C4Loop.cin (hPfxT A wa) (hKeepF A wa) (hKF A wa a R0 D c) p) (fun _ => 0) A'' ∧
      A'' (hSumP A wa) = frame (binary (C4Child.chW R0) (chValH R0 D (p ++ [b]))) ∧
      chValH R0 D (p ++ [b]) < 2 ^ C4Child.chW R0 ∧
      ∀ i, hKeepF A wa i = true → A'' i = C4Loop.cin (hPfxT A wa) (hKeepF A wa) (hKF A wa a R0 D c) p i := by
  obtain ⟨r, hw, H', A', st, hS, hK'⟩ := core_stepH A wa a R0 D c E Kc b p hplen hcC hok
    (fun cc hc => (hcell cc hc).1) (fun cc hc => (hcell cc hc).2) hRp hQp
  obtain ⟨A'', st', hA''⟩ :=
    C4Child.mask_blank (st.enlarge ((coreSteps_le wa a R0 D c Kc p b r hplen hcC).trans (hcost r hw)))
  refine ⟨A'', ?_, ?_, chValH_lt R0 D (p ++ [b]), ?_⟩
  · rw [hcin_eq]
    exact st'
  · rw [hSumP, hA'', hS]
  · intro i hi
    rw [hcin_eq]
    refine Fin.addCases (motive := fun i => hKeepF A wa i = true → A'' i =
      Fin.addCases (hChInP A wa a R0 D c p) (fun _ : Fin 1 => []) i) (fun x hx => ?_)
      (fun y hy => ?_) i hi
    · rw [hA'', Fin.addCases_left]
      exact hK' x (by simpa [hKeepF] using hx)
    · simp [hKeepF] at hy

/-- **The HASH call's child family** (`C4Loop.ChildFam`): one child machine per candidate bit, whose sum port holds
the recovered child sum `chValH (p ++ [b])` below `2^W`, the kept tapes unchanged, within `2·Kch + 2` steps, at every
prefix shorter than `sh`. C4H's side conditions `he` and the capacity `hcC` are the hypotheses. -/
def chFamH (E : Cost.Envelope) (fr : Fin 7 → ℕ) (Kc Kch sh : ℕ) (hsh : sh ≤ 2 * D.MP.t * D.MP.ell0)
    (hcC : 2 * D.MP.t * D.MP.ell0 ≤ c.cC) (he : HashEAt wa a R0 D c fr Kc Kch sh) : C4Loop.ChildFam where
  t := CTH A wa + 1
  s := _
  M := chMHs A wa
  cost := 2 * Kch + 2
  PFX := hPfxT A wa
  SUM := hSumP A wa
  keep := hKeepF A wa
  hPFX := hKeepF_pfx A wa
  hSUM := hKeepF_sum A wa
  K := hKF A wa a R0 D c
  W := C4Child.chW R0
  bound := sh
  val := chValH R0 D
  run := by
    intro p b hp
    have hl : p.length + 1 ≤ 2 * D.MP.t * D.MP.ell0 := by omega
    cases b
    · exact ch_runH A wa a R0 D c E Kc Kch false p hl hcC (he.1 p false hp).1 (he.1 p false hp).2
        (he.2.1 p false hp) he.2.2.1 (fun r hw => he.2.2.2.1 p false r hp hw)
    · exact ch_runH A wa a R0 D c E Kc Kch true p hl hcC (he.1 p true hp).1 (he.1 p true hp).2
        (he.2.1 p true hp) he.2.2.1 (fun r hw => he.2.2.2.1 p true r hp hw)

/-- The family's prefix tape. -/
theorem hPfxT_val : (hPfxT A wa).val = A.t + 94 := by
  rw [hPfxT, Fin.val_castAdd, hUnSl_94]
  rfl

/-- The family's sum tape. -/
theorem hSumP_val : (hSumP A wa).val = A.t + (HU + (C4Pipe.childSum wa).val) := by
  rw [hSumP, Fin.val_castAdd, hSumT, hCmSl_val, if_neg (C4Child.childSum_ne wa)]

/-- The family's kept tapes are C4H's `hKeepN`. -/
theorem hKeepF_eq (v : ℕ) (h : v < CTH A wa + 1) : hKeepF A wa ⟨v, h⟩ = hKeepN A wa v := by
  unfold hKeepF hKeepN
  have hC : CTH A wa = A.t + (HU + C4Pipe.CN wa) := rfl
  by_cases hv : v < CTH A wa
  · have hv' : v < A.t + (HU + C4Pipe.CN wa) := hv
    rw [hAddL _ _ v h hv]
    unfold hKeepC
    by_cases h1 : v < A.t
    · rw [hAddL _ _ v hv h1, if_pos h1]
      simp only [Fin.ext_iff]
    · have h1' : A.t ≤ v := by omega
      have h3 : v - A.t < HU + C4Pipe.CN wa := by omega
      rw [hAddR _ _ v hv h1', if_neg h1]
      by_cases h2 : v < A.t + HU
      · have h4 : v - A.t < HU := by omega
        rw [hAddL _ _ (v - A.t) h3 h4, if_pos h2]
      · have h4 : HU ≤ v - A.t := by omega
        rw [hAddR _ _ (v - A.t) h3 h4, if_neg h2, if_pos hv]
        simp only [Fin.ext_iff, Nat.sub_sub]
  · have hge : CTH A wa ≤ v := by omega
    have hge' : A.t + (HU + C4Pipe.CN wa) ≤ v := hge
    have hn1 : ¬ v < A.t := by omega
    have hn2 : ¬ v < A.t + HU := by omega
    rw [hAddR _ _ v h hge, if_neg hn1, if_neg hn2, if_neg hv]

/-- The family's kept words are C4H-a's `hKN2` (the Hb unit's words framed). -/
theorem hKF_eq (v : ℕ) (h : v < CTH A wa + 1) :
    hKF A wa a R0 D c ⟨v, h⟩ = hKN2 A wa (C4Child.pre a R0) (C4Child.post a R0) (hb0 (hbX D c 0 0)) R0.P.Q
      (2 ^ R0.dRow * 2 ^ R0.dRow) v := by
  unfold hKF hKN2
  by_cases hp : v = A.t + 94
  · have e : (⟨v, h⟩ : Fin (CTH A wa + 1)) = hPfxT A wa := Fin.ext (by rw [hPfxT_val]; exact hp)
    rw [if_pos e, if_neg (by omega), dif_neg (by omega), if_pos (by rw [HU_eq]; omega)]
  · have e : (⟨v, h⟩ : Fin (CTH A wa + 1)) ≠ hPfxT A wa := fun e => hp (by rw [← hPfxT_val A wa, ← e])
    rw [if_neg e]
    have hC : CTH A wa = A.t + (HU + C4Pipe.CN wa) := rfl
    have hU : HU = 253 := HU_eq
    by_cases hv : v < CTH A wa
    · have hv' : v < A.t + (HU + C4Pipe.CN wa) := hv
      rw [hAddL _ _ v h hv]
      unfold hChInP hChIn
      by_cases h1 : v < A.t
      · rw [hAddL _ _ v hv h1, if_pos h1]
        simp only [C4Child.asmK, Fin.ext_iff]
      · have h1' : A.t ≤ v := by omega
        have h3 : v - A.t < HU + C4Pipe.CN wa := by omega
        rw [hAddR _ _ v hv h1', if_neg h1]
        by_cases h2 : v < A.t + HU
        · have h4 : v - A.t < HU := by omega
          rw [hAddL _ _ (v - A.t) h3 h4]
          simp only [uIn]
          by_cases h3 : v - A.t < 94
          · rw [dif_pos h3, dif_pos h3, if_pos h2]
          · have h5 : v - A.t ≠ 94 := by omega
            rw [dif_neg h3, dif_neg h3, if_neg h5, if_pos h2]
        · have h4 : HU ≤ v - A.t := by omega
          have h5 : ¬ v - A.t < 94 := by omega
          rw [hAddR _ _ (v - A.t) h3 h4, dif_neg h5, if_neg h2, if_pos hv]
          simp only [C4Pipe.childIn, C4Pipe.childQQ, C4Pipe.childUU, Nat.sub_sub]
          split_ifs <;> first | rfl | omega
    · have hge : CTH A wa ≤ v := by omega
      have hge' : A.t + (HU + C4Pipe.CN wa) ≤ v := hge
      have hn1 : ¬ v < A.t := by omega
      have hn2 : ¬ v - A.t < 94 := by omega
      have hn3 : ¬ v < A.t + HU := by omega
      rw [hAddR _ _ v h hge, if_neg hn1, dif_neg hn2, if_neg hn3, if_neg hv]

/-- **The HASH child family at C4H-a's interface** (`HashFamAt2`), the loop's decisions `bits` given. -/
def hashFamAt2 (E : Cost.Envelope) (fr : Fin 7 → ℕ) (Kc Kch sh : ℕ) (hsh : sh ≤ 2 * D.MP.t * D.MP.ell0)
    (hcC : 2 * D.MP.t * D.MP.ell0 ≤ c.cC) (he : HashEAt wa a R0 D c fr Kc Kch sh) (bits : List Bool)
    (hloop : SeedFix.greedyLoop sh (fun p => (chValH R0 D p : ℤ)) = bits) :
    HashFamAt2 A wa (C4Child.pre a R0) (C4Child.post a R0) (hb0 (hbX D c 0 0)) R0.P.Q (2 ^ R0.dRow * 2 ^ R0.dRow)
      (C4Child.chW R0) sh bits where
  F := chFamH A wa a R0 D c E fr Kc Kch sh hsh hcC he
  ht := rfl
  keep := hKeepF_eq A wa
  K := hKF_eq A wa a R0 D c
  pfx := hPfxT_val A wa
  sum := hSumP_val A wa
  hW := rfl
  bound := rfl
  loop := hloop

end Fam

end

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
