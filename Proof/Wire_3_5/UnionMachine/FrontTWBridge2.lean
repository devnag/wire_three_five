import Proof.Wire_3_5.UnionMachine.FrontTWBridge

/-! # C6 front, U5: the table writer's positions and clauses are the tests' terms (P3:3685-3691, 3483-3489)

At a position `(i, b)` (variable `X`, the registers `X, X·s, [X systematic]` and the six magnitudes), the validity
test's blocks are `blk` of `polyVAt (i, b)` for `j = 0, 1, 2` (`κ₃ = 0`): **`outV_eq`**; likewise the second-moment
test (**`outQ_eq`**) and, at a clause, the clause test (**`outMu_eq`**). Paper quantity: the entries of the calls of
`(tr:tests)` at one position or clause. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge (entryOf)
open NearCubicWires.RepairRepresentation (natWord natListWord)

/-- The six magnitudes `|κ|·∏ m_k` held in registers. -/
structure MagRegs (D : UnionCheckData) (Λ : ℕ) (v : Fin NR → ℕ) : Prop where
  a : v rMa = D.s * D.s * D.s * D.s
  b : v rMb = Λ * Λ * D.s * D.s
  c : v rMc = 2 * (Λ * D.s * D.s * D.s)
  d : v rMd = 2 * (Λ * Λ * Λ * D.s)
  e : v rMe = Λ * Λ * Λ * Λ
  f : v rMf = Λ * D.s * D.s * D.s

theorem withMag_MAG (v : Fin NR → ℕ) (Mx : Fin NR) : withMag v Mx rMAG = v Mx := by simp [withMag]
theorem withMag_ne (v : Fin NR → ℕ) (Mx r : Fin NR) (h : r ≠ rMAG) : withMag v Mx r = v r := by
  simp [withMag, Function.update_of_ne h]

theorem polyV_κ (D : UnionCheckData) (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) :
    (D.polyVAt pos).κ = ![1, -2, 1, 0] := by
  unfold UnionCheckData.polyVAt polyVQ; split <;> rfl

theorem polyQ_κ (D : UnionCheckData) (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) :
    (D.polyQAt pos).κ = ![1, 0, 0, 0] := rfl

theorem finRange4_flatMap {β : Type} (f : Fin 4 → List β) :
    (List.finRange 4).flatMap f = f 0 ++ (f 1 ++ (f 2 ++ f 3)) := by
  simp [List.finRange_succ, List.flatMap_cons]

theorem blk_zero (D : UnionCheckData) (P : Poly4Q D.AtomIx) (j : Fin 4) (X Y : PcppVar D.pcpp) (pat : Fin 4 → FK)
    (call : (Fin 4 → D.AtomIx) → PrimRequest) (h : P.κ j = 0) : blk D P j X Y pat call = [] := by
  simp [blk, h]

/-- A validity/second-moment block at a position (one carrier, no `S_Y` factor). -/
theorem blockPos_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ)
    (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (hX : v rX = (posVar D.pcpp pos.1 pos.2).val)
    (hXS : v rXS = (posVar D.pcpp pos.1 pos.2).val * D.s) (hSS : v rSS = D.s)
    (Λ : ℕ) (hm : D.mass = Λ) (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true)
    (P : Poly4Q D.AtomIx) (j : Fin 4) (pat : Fin 4 → FK) (hnosy : ∀ k, pat k ≠ .sy)
    (hF : ∀ k, P.F j k = wOf D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (pat k)) (κn : Bool) (κm : ℕ)
    (hκ : P.κ j = ((sgnZ κn * κm : ℤ) : ℚ)) (hκm : 1 ≤ κm) (Mx : Fin NR) (hMag : v Mx = magOf D Λ κm pat) (kd : Fin 3) :
    blockW d (withMag v Mx) kd κn pat false =
      (blk D P j (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) pat (D.vCall pos)).flatMap
        fun t => Entry.entryWord (entryOf kd D.s t) := by
  have hX' : withMag v Mx rX = (posVar D.pcpp pos.1 pos.2).val := by rw [withMag_ne _ _ _ (by decide), hX]
  exact blockW_eq D d hr (withMag v Mx) _ _ pat (fun _ _ => by rw [withMag_ne _ _ _ (by decide), hXS])
    (fun k hk => absurd hk (hnosy k)) (by rw [withMag_ne _ _ _ (by decide), hSS]) Λ hm hΛ hs hsg P j hF κn κm hκ hκm kd
    false (D.vCall pos) (by rw [withMag_MAG, hMag])
    (fun t ht => callWord_v D d hr (withMag v Mx) pos hX' _ pat t ht)

theorem patV_nosy (sys : Bool) (j k : Fin 4) : patV sys j k ≠ .sy := by
  cases sys <;> fin_cases j <;> fin_cases k <;> simp [patV]

theorem patQ_nosy (j k : Fin 4) : patQ j k ≠ .sy := by
  fin_cases j <;> fin_cases k <;> simp [patQ]

/-- **The validity test at a position**: the three blocks are the position's terms' entries. -/
theorem outV_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ)
    (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (hX : v rX = (posVar D.pcpp pos.1 pos.2).val)
    (hXS : v rXS = (posVar D.pcpp pos.1 pos.2).val * D.s) (hSS : v rSS = D.s)
    (hSY : v rSYSX = if D.sysBit (posVar D.pcpp pos.1 pos.2) then 1 else 0)
    (Λ : ℕ) (hm : D.mass = Λ) (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true) (hmr : MagRegs D Λ v) :
    outV d v = (List.finRange 4).flatMap fun j =>
      (blk D (D.polyVAt pos) j (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2)
        (patV (D.sysBit (posVar D.pcpp pos.1 pos.2)) j) (D.vCall pos)).flatMap
          fun t => Entry.entryWord (entryOf 0 D.s t) := by
  rw [finRange4_flatMap, blk_zero D _ 3 _ _ _ _ (by rw [polyV_κ]; rfl), List.flatMap_nil, List.append_nil]
  have hF := fun j k => polyV_F D pos j k
  cases hsb : D.sysBit (posVar D.pcpp pos.1 pos.2)
  · rw [hsb] at hSY hF
    simp only [outV, hSY, ne_eq, not_true_eq_false, if_false, Bool.false_eq_true]
    rw [blockPos_eq D d hr v pos hX hXS hSS Λ hm hΛ hs hsg _ 0 _ (patV_nosy false 0) (hF 0) false 1
        (by rw [polyV_κ]; simp [sgnZ]) le_rfl rMb
        (by rw [hmr.b, show magOf D Λ 1 (patV false 0) = 1 * (Λ * Λ * D.s * D.s) from rfl]; ring) 0,
      blockPos_eq D d hr v pos hX hXS hSS Λ hm hΛ hs hsg _ 1 _ (patV_nosy false 1) (hF 1) true 2
        (by rw [polyV_κ]; simp [sgnZ]) (by omega) rMd
        (by rw [hmr.d, show magOf D Λ 2 (patV false 1) = 2 * (Λ * Λ * Λ * D.s) from rfl]) 0,
      blockPos_eq D d hr v pos hX hXS hSS Λ hm hΛ hs hsg _ 2 _ (patV_nosy false 2) (hF 2) false 1
        (by rw [polyV_κ]; simp [sgnZ]) le_rfl rMe
        (by rw [hmr.e, show magOf D Λ 1 (patV false 2) = 1 * (Λ * Λ * Λ * Λ) from rfl]; ring) 0]
  · rw [hsb] at hSY hF
    simp only [outV, hSY, ne_eq, one_ne_zero, not_false_eq_true, if_true]
    rw [blockPos_eq D d hr v pos hX hXS hSS Λ hm hΛ hs hsg _ 0 _ (patV_nosy true 0) (hF 0) false 1
        (by rw [polyV_κ]; simp [sgnZ]) le_rfl rMb
        (by rw [hmr.b, show magOf D Λ 1 (patV true 0) = 1 * (Λ * Λ * D.s * D.s) from rfl]; ring) 0,
      blockPos_eq D d hr v pos hX hXS hSS Λ hm hΛ hs hsg _ 1 _ (patV_nosy true 1) (hF 1) true 2
        (by rw [polyV_κ]; simp [sgnZ]) (by omega) rMc
        (by rw [hmr.c, show magOf D Λ 2 (patV true 1) = 2 * (D.s * Λ * D.s * D.s) from rfl]; ring) 0,
      blockPos_eq D d hr v pos hX hXS hSS Λ hm hΛ hs hsg _ 2 _ (patV_nosy true 2) (hF 2) false 1
        (by rw [polyV_κ]; simp [sgnZ]) le_rfl rMa
        (by rw [hmr.a, show magOf D Λ 1 (patV true 2) = 1 * (D.s * D.s * D.s * D.s) from rfl]; ring) 0]

/-- **The second-moment test at a position.** -/
theorem outQ_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ)
    (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (hX : v rX = (posVar D.pcpp pos.1 pos.2).val)
    (hXS : v rXS = (posVar D.pcpp pos.1 pos.2).val * D.s) (hSS : v rSS = D.s)
    (Λ : ℕ) (hm : D.mass = Λ) (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true) (hmr : MagRegs D Λ v) :
    outQ d v = (List.finRange 4).flatMap fun j =>
      (blk D (D.polyQAt pos) j (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (patQ j) (D.vCall pos)).flatMap
        fun t => Entry.entryWord (entryOf 1 D.s t) := by
  rw [finRange4_flatMap, blk_zero D _ 1 _ _ _ _ (by rw [polyQ_κ]; rfl), blk_zero D _ 2 _ _ _ _ (by rw [polyQ_κ]; rfl),
    blk_zero D _ 3 _ _ _ _ (by rw [polyQ_κ]; rfl)]
  simp only [List.flatMap_nil, List.append_nil]
  exact blockPos_eq D d hr v pos hX hXS hSS Λ hm hΛ hs hsg _ 0 _ (patQ_nosy 0) (fun k => polyQ_F D pos 0 k) false 1
    (by rw [polyQ_κ]; simp [sgnZ]) le_rfl rMb
    (by rw [hmr.b, show magOf D Λ 1 (patQ 0) = 1 * (Λ * Λ * D.s * D.s) from rfl]; ring) 1

/-- A clause-test block at a clause (two carriers). -/
theorem blockMu_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ)
    (i : Fin (2 ^ D.pcpp.clauseBits)) (hX : v rX = (posVar D.pcpp i 0).val) (hY : v rY = (posVar D.pcpp i 1).val)
    (hXS : v rXS = (posVar D.pcpp i 0).val * D.s) (hYS : v rYS = (posVar D.pcpp i 1).val * D.s) (hSS : v rSS = D.s)
    (Λ : ℕ) (hm : D.mass = Λ) (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true)
    (j : Fin 4) (κn : Bool) (hκ : (D.polyMuAt i).κ j = ((sgnZ κn * 1 : ℤ) : ℚ)) (Mx : Fin NR)
    (hMag : v Mx = magOf D Λ 1 (patMu j)) :
    blockW d (withMag v Mx) 2 κn (patMu j) true =
      (blk D (D.polyMuAt i) j (posVar D.pcpp i 0) (posVar D.pcpp i 1) (patMu j) (D.muCall i)).flatMap
        fun t => Entry.entryWord (entryOf 2 D.s t) := by
  have hX' : withMag v Mx rX = (posVar D.pcpp i 0).val := by rw [withMag_ne _ _ _ (by decide), hX]
  have hY' : withMag v Mx rY = (posVar D.pcpp i 1).val := by rw [withMag_ne _ _ _ (by decide), hY]
  exact blockW_eq D d hr (withMag v Mx) _ _ (patMu j) (fun _ _ => by rw [withMag_ne _ _ _ (by decide), hXS])
    (fun _ _ => by rw [withMag_ne _ _ _ (by decide), hYS]) (by rw [withMag_ne _ _ _ (by decide), hSS]) Λ hm hΛ hs hsg
    (D.polyMuAt i) j (fun k => polyMu_F D i j k) κn 1 hκ le_rfl 2 true (D.muCall i) (by rw [withMag_MAG, hMag])
    (fun t ht => callWord_mu D d hr (withMag v Mx) i hX' hY' (patMu j) t ht)

theorem polyMu_κ (D : UnionCheckData) (i : Fin (2 ^ D.pcpp.clauseBits)) :
    (D.polyMuAt i).κ = ![litAQ (posNeg D.pcpp i 0) + litAQ (posNeg D.pcpp i 1) -
      litAQ (posNeg D.pcpp i 0) * litAQ (posNeg D.pcpp i 1), litBQ (posNeg D.pcpp i 0) * (1 - litAQ (posNeg D.pcpp i 1)),
      litBQ (posNeg D.pcpp i 1) * (1 - litAQ (posNeg D.pcpp i 0)),
      -(litBQ (posNeg D.pcpp i 0) * litBQ (posNeg D.pcpp i 1))] := rfl

/-- **The clause test at a clause**: the active blocks are the clause's terms' entries. -/
theorem outMu_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ)
    (i : Fin (2 ^ D.pcpp.clauseBits)) (hX : v rX = (posVar D.pcpp i 0).val) (hY : v rY = (posVar D.pcpp i 1).val)
    (hXS : v rXS = (posVar D.pcpp i 0).val * D.s) (hYS : v rYS = (posVar D.pcpp i 1).val * D.s) (hSS : v rSS = D.s)
    (hN0 : v rN0 = if posNeg D.pcpp i 0 then 1 else 0) (hN1 : v rN1 = if posNeg D.pcpp i 1 then 1 else 0)
    (Λ : ℕ) (hm : D.mass = Λ) (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true) (hmr : MagRegs D Λ v) :
    outMu d v = (List.finRange 4).flatMap fun j =>
      (blk D (D.polyMuAt i) j (posVar D.pcpp i 0) (posVar D.pcpp i 1) (patMu j) (D.muCall i)).flatMap
        fun t => Entry.entryWord (entryOf 2 D.s t) := by
  have ma : v rMa = magOf D Λ 1 (patMu 0) := by
    rw [hmr.a, show magOf D Λ 1 (patMu 0) = 1 * (D.s * D.s * D.s * D.s) from rfl]; ring
  have mf1 : v rMf = magOf D Λ 1 (patMu 1) := by
    rw [hmr.f, show magOf D Λ 1 (patMu 1) = 1 * (Λ * D.s * D.s * D.s) from rfl]; ring
  have mf2 : v rMf = magOf D Λ 1 (patMu 2) := by
    rw [hmr.f, show magOf D Λ 1 (patMu 2) = 1 * (Λ * D.s * D.s * D.s) from rfl]; ring
  have mb3 : v rMb = magOf D Λ 1 (patMu 3) := by
    rw [hmr.b, show magOf D Λ 1 (patMu 3) = 1 * (Λ * Λ * D.s * D.s) from rfl]; ring
  have B := fun j κn hκ Mx hMag => blockMu_eq D d hr v i hX hY hXS hYS hSS Λ hm hΛ hs hsg j κn hκ Mx hMag
  rw [finRange4_flatMap]
  have hκ := polyMu_κ D i
  cases h0 : posNeg D.pcpp i 0 <;> cases h1 : posNeg D.pcpp i 1 <;> rw [h0] at hN0 hκ <;> rw [h1] at hN1 hκ <;>
    simp only [outMu, hN0, hN1, if_true, if_false, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false,
      Bool.false_eq_true]
  · rw [blk_zero D _ 0 _ _ _ _ (by rw [hκ]; simp [litAQ]),
      B 1 false (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMf mf1, B 2 false (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMf mf2,
      B 3 true (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMb mb3]
    simp
  · rw [B 0 false (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMa ma, blk_zero D _ 1 _ _ _ _ (by rw [hκ]; simp [litAQ]),
      B 2 true (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMf mf2, B 3 false (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMb mb3]
    simp
  · rw [B 0 false (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMa ma, B 1 true (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMf mf1,
      blk_zero D _ 2 _ _ _ _ (by rw [hκ]; simp [litAQ]), B 3 false (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMb mb3]
    simp
  · rw [B 0 false (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMa ma, blk_zero D _ 1 _ _ _ _ (by rw [hκ]; simp [litAQ]),
      blk_zero D _ 2 _ _ _ _ (by rw [hκ]; simp [litAQ]), B 3 true (by rw [hκ]; simp [litAQ, litBQ, sgnZ]) rMb mb3]
    simp

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
