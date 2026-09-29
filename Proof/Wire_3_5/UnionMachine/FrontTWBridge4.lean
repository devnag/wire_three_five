import Proof.Wire_3_5.UnionMachine.FrontTWBridge3

/-! # C6 front, U5: the table writer's admissibility bit is the schedule's (P3:3083-3094, 3689-3691)

The flag strings hold one bit per circuit (the description envelope, `fD`) and per carrier (the carrier envelope,
`fE`) (**`TWFlags`**). Each call's `OK` conjunct is `fD` of its four circuits and `fE` of its named carriers
(**`callOkE_psi`**); over the three passes, `OK` is `schedule.all okR` for any `okR` agreeing with those conjuncts on
the scheduled calls (**`accB_all_eq`**). Paper quantity: the calls' admissibility (`lem:primitive`'s precondition). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef

/-- The flag strings hold the circuits' and carriers' envelope bits. -/
structure TWFlags (D : UnionCheckData) (d : TWData) (fD : D.mode.Circuit D.q → Bool)
    (fE : Stars.Carrier D.q → Bool) : Prop where
  pf : ∀ X : PcppVar D.pcpp, d.pf.getD X.val false = fD (D.parity X)
  df : ∀ (X : PcppVar D.pcpp) (a : Fin D.s), d.df.getD (X.val * D.s + a.val) false = fD (D.atom X a)
  ef : ∀ X : PcppVar D.pcpp, d.ef.getD X.val false = fE (D.carrier X)

theorem flagVE_psi (D : UnionCheckData) (d : TWData) (fD : D.mode.Circuit D.q → Bool) (fE : Stars.Carrier D.q → Bool)
    (hf : TWFlags D d fD fE) (v : Fin NR → ℕ) (hC : decide (v rCDF ≠ 0) = fD D.const) (X Y : PcppVar D.pcpp)
    (hX : v rX = X.val) (f : FK) (k : Fin 4) (a : D.AtomIx) (ha : a ∈ cand D X Y f) (E : Fin 4 → ℕ)
    (hE : E k = psi D a) : flagVE d v E f k = fD (D.circ a) := by
  cases f
  · simp only [cand, List.mem_singleton] at ha; subst ha
    simp only [flagVE, hC]; rfl
  · simp only [cand, List.mem_singleton] at ha; subst ha
    simp only [flagVE, hX, hf.pf X]; rfl
  all_goals
    obtain ⟨Z, b, rfl, -⟩ := mem_cand_psi D X Y _ a ha (by simp)
    simp only [flagVE, hE, psi, hf.df Z b]; rfl

/-- **A call's admissibility conjunct**: its four circuits' and its carriers' envelope bits. -/
theorem callOkE_psi (D : UnionCheckData) (d : TWData) (fD : D.mode.Circuit D.q → Bool) (fE : Stars.Carrier D.q → Bool)
    (hf : TWFlags D d fD fE) (v : Fin NR → ℕ) (hC : decide (v rCDF ≠ 0) = fD D.const) (X Y : PcppVar D.pcpp)
    (hX : v rX = X.val) (pat : Fin 4 → FK) (two : Bool) (hY : two = true → v rY = Y.val) (t : Fin 4 → D.AtomIx)
    (ht : ∀ k, t k ∈ cand D X Y (pat k)) :
    callOkE d v (fun k => psi D (t k)) pat two =
      (fD (D.circ (t 0)) && fD (D.circ (t 1)) && fD (D.circ (t 2)) && fD (D.circ (t 3)) && fE (D.carrier X) &&
        (!two || fE (D.carrier Y))) := by
  unfold callOkE
  rw [flagVE_psi D d fD fE hf v hC X Y hX _ 0 (t 0) (ht 0) _ rfl, flagVE_psi D d fD fE hf v hC X Y hX _ 1 (t 1) (ht 1) _ rfl,
    flagVE_psi D d fD fE hf v hC X Y hX _ 2 (t 2) (ht 2) _ rfl, flagVE_psi D d fD fE hf v hC X Y hX _ 3 (t 3) (ht 3) _ rfl,
    hX, hf.ef X]
  cases two
  · simp
  · rw [hY rfl, hf.ef Y]

/-- A call's admissibility conjunct from its tuple. -/
def okT (D : UnionCheckData) (fD : D.mode.Circuit D.q → Bool) (fE : Stars.Carrier D.q → Bool) (X Y : PcppVar D.pcpp)
    (two : Bool) (t : Fin 4 → D.AtomIx) : Bool :=
  fD (D.circ (t 0)) && fD (D.circ (t 1)) && fD (D.circ (t 2)) && fD (D.circ (t 3)) && fE (D.carrier X) &&
    (!two || fE (D.carrier Y))

/-- **A block's admissibility is its calls'.** -/
theorem blockOk_blk (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (fD : D.mode.Circuit D.q → Bool)
    (fE : Stars.Carrier D.q → Bool) (hf : TWFlags D d fD fE) (v : Fin NR → ℕ) (hC : decide (v rCDF ≠ 0) = fD D.const)
    (X Y : PcppVar D.pcpp) (hX : v rX = X.val) (pat : Fin 4 → FK)
    (hXS : ∀ k, pat k = .sx → v rXS = X.val * D.s) (hYS : ∀ k, pat k = .sy → v rYS = Y.val * D.s)
    (hSS : v rSS = D.s) (two : Bool) (hY : two = true → v rY = Y.val) (P : Poly4Q D.AtomIx) (j : Fin 4) (hκ : P.κ j ≠ 0)
    (call : (Fin 4 → D.AtomIx) → PrimRequest) (okR : PrimRequest → Bool)
    (hok : ∀ t : Fin 4 → D.AtomIx, (∀ k, t k ∈ cand D X Y (pat k)) → okR (call t) = okT D fD fE X Y two t) :
    blockOk d v pat two = (blk D P j X Y pat call).all fun p => okR p.2 := by
  rw [blockOk_eq D d hr v X Y pat hXS hYS hSS two (fun t => okR (call t))
    (fun t ht => by rw [callOkE_psi D d fD fE hf v hC X Y hX pat two hY t ht, hok t ht]; rfl)]
  unfold blk
  rw [if_neg hκ, List.all_map]
  rfl

theorem finRange4_all (f : Fin 4 → Bool) : (List.finRange 4).all f = (f 0 && (f 1 && (f 2 && f 3))) := by
  simp [List.finRange_succ, Bool.and_assoc]

theorem blk_all_zero (D : UnionCheckData) (P : Poly4Q D.AtomIx) (j : Fin 4) (X Y : PcppVar D.pcpp) (pat : Fin 4 → FK)
    (call : (Fin 4 → D.AtomIx) → PrimRequest) (okR : PrimRequest → Bool) (h : P.κ j = 0) :
    (blk D P j X Y pat call).all (fun p => okR p.2) = true := by
  rw [blk_zero D P j X Y pat call h]; rfl

/-- **The validity test's admissibility at a position.** -/
theorem okV_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (fD : D.mode.Circuit D.q → Bool)
    (fE : Stars.Carrier D.q → Bool) (hf : TWFlags D d fD fE) (v : Fin NR → ℕ) (hC : decide (v rCDF ≠ 0) = fD D.const)
    (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (hX : v rX = (posVar D.pcpp pos.1 pos.2).val)
    (hXS : v rXS = (posVar D.pcpp pos.1 pos.2).val * D.s) (hSS : v rSS = D.s)
    (hSY : v rSYSX = if D.sysBit (posVar D.pcpp pos.1 pos.2) then 1 else 0) (okR : PrimRequest → Bool)
    (hok : ∀ (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ cand D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (pat k)) →
      okR (D.vCall pos t) = okT D fD fE (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) false t) :
    okV d v = (List.finRange 4).all fun j =>
      (blk D (D.polyVAt pos) j (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2)
        (patV (D.sysBit (posVar D.pcpp pos.1 pos.2)) j) (D.vCall pos)).all fun p => okR p.2 := by
  rw [finRange4_all, blk_all_zero D _ 3 _ _ _ _ okR (by rw [polyV_κ]; rfl), Bool.and_true]
  have hX' : ∀ Mx, withMag v Mx rX = (posVar D.pcpp pos.1 pos.2).val := fun Mx => by rw [withMag_ne _ _ _ (by decide), hX]
  have hC' : ∀ Mx, decide (withMag v Mx rCDF ≠ 0) = fD D.const := fun Mx => by rw [withMag_ne _ _ _ (by decide), hC]
  have B := fun Mx (pat : Fin 4 → FK) (hns : ∀ k, pat k ≠ .sy) (j : Fin 4) (hκ : (D.polyVAt pos).κ j ≠ 0) =>
    blockOk_blk D d hr fD fE hf (withMag v Mx) (hC' Mx) (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (hX' Mx) pat
      (fun _ _ => by rw [withMag_ne _ _ _ (by decide), hXS]) (fun k hk => absurd hk (hns k))
      (by rw [withMag_ne _ _ _ (by decide), hSS]) false (fun h => by simp at h) (D.polyVAt pos) j hκ (D.vCall pos) okR
      (fun t ht => hok pat t ht)
  cases hsb : D.sysBit (posVar D.pcpp pos.1 pos.2)
  · rw [hsb] at hSY
    simp only [okV, hSY, ne_eq, not_true_eq_false, if_false, Bool.false_eq_true]
    rw [B rMb _ (patV_nosy false 0) 0 (by rw [polyV_κ]; simp), B rMd _ (patV_nosy false 1) 1 (by rw [polyV_κ]; simp),
      B rMe _ (patV_nosy false 2) 2 (by rw [polyV_κ]; simp)]
  · rw [hsb] at hSY
    simp only [okV, hSY, ne_eq, one_ne_zero, not_false_eq_true, if_true]
    rw [B rMb _ (patV_nosy true 0) 0 (by rw [polyV_κ]; simp), B rMc _ (patV_nosy true 1) 1 (by rw [polyV_κ]; simp),
      B rMa _ (patV_nosy true 2) 2 (by rw [polyV_κ]; simp)]

/-- **The second-moment test's admissibility at a position.** -/
theorem okQ_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (fD : D.mode.Circuit D.q → Bool)
    (fE : Stars.Carrier D.q → Bool) (hf : TWFlags D d fD fE) (v : Fin NR → ℕ) (hC : decide (v rCDF ≠ 0) = fD D.const)
    (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (hX : v rX = (posVar D.pcpp pos.1 pos.2).val)
    (hXS : v rXS = (posVar D.pcpp pos.1 pos.2).val * D.s) (hSS : v rSS = D.s) (okR : PrimRequest → Bool)
    (hok : ∀ (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ cand D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (pat k)) →
      okR (D.vCall pos t) = okT D fD fE (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) false t) :
    okQ d v = (List.finRange 4).all fun j =>
      (blk D (D.polyQAt pos) j (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (patQ j) (D.vCall pos)).all
        fun p => okR p.2 := by
  rw [finRange4_all, blk_all_zero D _ 1 _ _ _ _ okR (by rw [polyQ_κ]; rfl),
    blk_all_zero D _ 2 _ _ _ _ okR (by rw [polyQ_κ]; rfl), blk_all_zero D _ 3 _ _ _ _ okR (by rw [polyQ_κ]; rfl)]
  simp only [Bool.and_true]
  exact blockOk_blk D d hr fD fE hf (withMag v rMb) (by rw [withMag_ne _ _ _ (by decide), hC]) _ _
    (by rw [withMag_ne _ _ _ (by decide), hX]) (patQ 0) (fun _ _ => by rw [withMag_ne _ _ _ (by decide), hXS])
    (fun k hk => absurd hk (patQ_nosy 0 k)) (by rw [withMag_ne _ _ _ (by decide), hSS]) false (fun h => by simp at h)
    (D.polyQAt pos) 0 (by rw [polyQ_κ]; simp) (D.vCall pos) okR (fun t ht => hok _ t ht)

/-- **The clause test's admissibility at a clause.** -/
theorem okMu_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (fD : D.mode.Circuit D.q → Bool)
    (fE : Stars.Carrier D.q → Bool) (hf : TWFlags D d fD fE) (v : Fin NR → ℕ) (hC : decide (v rCDF ≠ 0) = fD D.const)
    (i : Fin (2 ^ D.pcpp.clauseBits)) (hX : v rX = (posVar D.pcpp i 0).val) (hY : v rY = (posVar D.pcpp i 1).val)
    (hXS : v rXS = (posVar D.pcpp i 0).val * D.s) (hYS : v rYS = (posVar D.pcpp i 1).val * D.s) (hSS : v rSS = D.s)
    (hN0 : v rN0 = if posNeg D.pcpp i 0 then 1 else 0) (hN1 : v rN1 = if posNeg D.pcpp i 1 then 1 else 0)
    (okR : PrimRequest → Bool)
    (hok : ∀ (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx), (∀ k, t k ∈ cand D (posVar D.pcpp i 0) (posVar D.pcpp i 1) (pat k)) →
      okR (D.muCall i t) = okT D fD fE (posVar D.pcpp i 0) (posVar D.pcpp i 1) true t) :
    okMu d v = (List.finRange 4).all fun j =>
      (blk D (D.polyMuAt i) j (posVar D.pcpp i 0) (posVar D.pcpp i 1) (patMu j) (D.muCall i)).all fun p => okR p.2 := by
  have B := fun (Mx : Fin NR) (j : Fin 4) (hκ : (D.polyMuAt i).κ j ≠ 0) =>
    blockOk_blk D d hr fD fE hf (withMag v Mx) (by rw [withMag_ne _ _ _ (by decide), hC]) _ _
      (by rw [withMag_ne _ _ _ (by decide), hX]) (patMu j) (fun _ _ => by rw [withMag_ne _ _ _ (by decide), hXS])
      (fun _ _ => by rw [withMag_ne _ _ _ (by decide), hYS]) (by rw [withMag_ne _ _ _ (by decide), hSS]) true
      (fun _ => by rw [withMag_ne _ _ _ (by decide), hY]) (D.polyMuAt i) j hκ (D.muCall i) okR
      (fun t ht => hok _ t ht)
  rw [finRange4_all]
  have hκ := polyMu_κ D i
  cases h0 : posNeg D.pcpp i 0 <;> cases h1 : posNeg D.pcpp i 1 <;> rw [h0] at hN0 hκ <;> rw [h1] at hN1 hκ <;>
    simp only [okMu, hN0, hN1, if_true, if_false, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false,
      Bool.false_eq_true]
  · rw [blk_all_zero D _ 0 _ _ _ _ okR (by rw [hκ]; simp [litAQ]), B rMf 1 (by rw [hκ]; simp [litAQ, litBQ]),
      B rMf 2 (by rw [hκ]; simp [litAQ, litBQ]), B rMb 3 (by rw [hκ]; simp [litAQ, litBQ])]
  · rw [B rMa 0 (by rw [hκ]; simp [litAQ, litBQ]), blk_all_zero D _ 1 _ _ _ _ okR (by rw [hκ]; simp [litAQ]),
      B rMf 2 (by rw [hκ]; simp [litAQ, litBQ]), B rMb 3 (by rw [hκ]; simp [litAQ, litBQ])]
  · rw [B rMa 0 (by rw [hκ]; simp [litAQ, litBQ]), B rMf 1 (by rw [hκ]; simp [litAQ, litBQ]),
      blk_all_zero D _ 2 _ _ _ _ okR (by rw [hκ]; simp [litAQ]), B rMb 3 (by rw [hκ]; simp [litAQ, litBQ])]
  · rw [B rMa 0 (by rw [hκ]; simp [litAQ, litBQ]), blk_all_zero D _ 1 _ _ _ _ okR (by rw [hκ]; simp [litAQ]),
      blk_all_zero D _ 2 _ _ _ _ okR (by rw [hκ]; simp [litAQ]), B rMb 3 (by rw [hκ]; simp [litAQ, litBQ])]

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW

