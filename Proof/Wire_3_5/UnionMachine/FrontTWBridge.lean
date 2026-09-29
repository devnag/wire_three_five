import Proof.Wire_3_5.UnionMachine.FrontTWMain

/-! # C6 front, U5: the table writer computes the call table of `(tr:tests)` (P3:3685-3691, 3483-3489)

The table writer's sources hold one parsed guess's data (**`TWRel`**): the request head `natWord q ++ [mode] ++
natWord 4`, the tail `natListWord translation`, the constant's, each parity's and each carrier's code, and the grid
entries in the codec order (entry `X·s + a` = the sign word of `σ_{X,a}` and the atom's code). A machine digit (an
entry index) names an atom by **`psi`**; the factors' candidates are the supports' images (**`candOf_eq`**), so a
block's entries are the monomial's calls' entries (**`blockW_eq`**, via `FrontTableRef.entryOf_blk`).

Paper quantity of the main statements: the call table's entries, block by block. -/

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

section Rel
variable (D : UnionCheckData)

/-- A digit's entry index for an atom (`0` for the constant and the parities). -/
def psi : D.AtomIx → ℕ
  | Sum.inr (Sum.inl (X, a)) => X.val * D.s + a.val
  | _ => 0

/-- The mode's bit in a request word. -/
def modeBit : Mode → Bool
  | .thr => true
  | .sym => false

/-- **The sources hold the parsed guess** `D`. -/
structure TWRel (d : TWData) : Prop where
  hd : d.hd = natWord D.q ++ [modeBit D.mode] ++ natWord 4
  tl : d.tl = natListWord D.translation
  cc : d.cc = natWord (D.mode.code D.const)
  pcs : ∀ X : PcppVar D.pcpp, d.pcs.getD X.val [] = natWord (D.mode.code (D.parity X))
  crs : ∀ X : PcppVar D.pcpp, d.crs.getD X.val [] = natWord (Stars.Carrier.code (D.carrier X))
  esx : ∀ (X : PcppVar D.pcpp) (a : Fin D.s), (d.es.getD (X.val * D.s + a.val) (false, false, 0)).2.1 =
    decide (D.sign X a ≠ 0)
  esb : ∀ (X : PcppVar D.pcpp) (a : Fin D.s), (d.es.getD (X.val * D.s + a.val) (false, false, 0)).1 =
    decide (D.sign X a < 0)
  esc : ∀ (X : PcppVar D.pcpp) (a : Fin D.s), (d.es.getD (X.val * D.s + a.val) (false, false, 0)).2.2 =
    D.mode.code (D.atom X a)

end Rel

/-! ## Four-fold products under a map -/

theorem lexProd_map {α β : Type} (S : Fin 4 → List α) (f : α → β) :
    lexProd (fun k => (S k).map f) = (lexProd S).map fun t k => f (t k) := by
  simp only [lexProd, List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1; funext t3; congr 1; funext t2; congr 1; funext t1
  congr 1; funext t0
  funext k; fin_cases k <;> rfl

theorem flatMap_lexProd_map {α β : Type} (S : Fin 4 → List α) (f : α → β) (g : (Fin 4 → β) → List Bool) :
    (lexProd (fun k => (S k).map f)).flatMap g = (lexProd S).flatMap fun t => g fun k => f (t k) := by
  rw [lexProd_map, List.flatMap_map]

theorem all_lexProd_map {α β : Type} (S : Fin 4 → List α) (f : α → β) (g : (Fin 4 → β) → Bool) :
    (lexProd (fun k => (S k).map f)).all g = (lexProd S).all fun t => g fun k => f (t k) := by
  rw [lexProd_map, List.all_map]; rfl

/-! ## The factors' candidates are the supports' images -/

theorem finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) (by intro i h1 h2; simp)

theorem candBelow_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (X : PcppVar D.pcpp) :
    candBelow d (X.val * D.s) D.s = (gridC D X).map (psi D) := by
  unfold candBelow gridC
  rw [List.map_filterMap, ← finRange_map_val, List.filterMap_map]
  congr 1
  funext a
  simp only [Function.comp_apply, xbOf]
  have e := hr.esx X a
  by_cases h : D.sign X a = 0
  · have e' : (d.es.getD (X.val * D.s + a.val) (false, false, 0)).2.1 = false := by rw [e]; simp [h]
    simp only [List.getD_eq_getElem?_getD] at e'
    simp [e', h]
  · have e' : (d.es.getD (X.val * D.s + a.val) (false, false, 0)).2.1 = true := by rw [e]; simp [h]
    simp only [List.getD_eq_getElem?_getD] at e'
    simp [e', h, psi]

/-- **The machine's candidates** (entry indices) are the images of the factors' supports. -/
theorem candOf_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ) (X Y : PcppVar D.pcpp)
    (f : FK) (hXS : f = .sx → v rXS = X.val * D.s) (hYS : f = .sy → v rYS = Y.val * D.s) (hSS : v rSS = D.s) :
    candOf d v f = (cand D X Y f).map (psi D) := by
  cases f
  · rfl
  · rfl
  · simp only [candOf, cand, hXS rfl, hSS]; exact candBelow_eq D d hr X
  · simp only [candOf, cand, hYS rfl, hSS]; exact candBelow_eq D d hr Y

/-! ## One call's entry -/

theorem mem_cand_psi (D : UnionCheckData) (X Y : PcppVar D.pcpp) (f : FK) (a : D.AtomIx) (ha : a ∈ cand D X Y f) :
    (f = .sx ∨ f = .sy) → ∃ (Z : PcppVar D.pcpp) (b : Fin D.s), a = Sum.inr (Sum.inl (Z, b)) ∧ D.sign Z b ≠ 0 := by
  intro hf
  rcases hf with rfl | rfl
  · obtain ⟨b, hb, rfl⟩ := (mem_gridC D X a).1 ha; exact ⟨X, b, rfl, hb⟩
  · obtain ⟨b, hb, rfl⟩ := (mem_gridC D Y a).1 ha; exact ⟨Y, b, rfl, hb⟩

theorem nbOfF_psi (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (X Y : PcppVar D.pcpp) (f : FK) (a : D.AtomIx)
    (ha : a ∈ cand D X Y f) : nbOfF d f (psi D a) = nbOf D f a := by
  cases f
  · rfl
  · rfl
  all_goals
    obtain ⟨Z, b, rfl, -⟩ := mem_cand_psi D X Y _ a ha (by simp)
    simp only [nbOfF, nbOf, isS, psi, bbOf, sgnAt, Bool.true_and]
    exact hr.esb Z b

theorem negBitE_psi (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (X Y : PcppVar D.pcpp) (κn : Bool)
    (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx) (ht : ∀ k, t k ∈ cand D X Y (pat k)) :
    negBitE κn (nbVec d pat fun k => psi D (t k)) = negOf D κn pat t := by
  simp only [negBitE, nbVec, negOf, nbOfF_psi D d hr X Y _ _ (ht 0), nbOfF_psi D d hr X Y _ _ (ht 1),
    nbOfF_psi D d hr X Y _ _ (ht 2), nbOfF_psi D d hr X Y _ _ (ht 3)]
  cases nbOf D (pat 0) (t 0) <;> cases nbOf D (pat 1) (t 1) <;> cases nbOf D (pat 2) (t 2) <;>
    cases nbOf D (pat 3) (t 3) <;> cases κn <;> rfl

/-- A tuple request's word, field by field. -/
theorem tupleRequest_word {α : Type} (m : Mode) (q : ℕ) (circ : α → m.Circuit q) (t : Fin 4 → α)
    (cs : List (Stars.Carrier q)) (tr : List ℕ) :
    (tupleRequest m q circ t cs tr).word = natWord q ++ [modeBit m] ++ natWord 4 ++
      (natWord (m.code (circ (t 0))) ++ natWord (m.code (circ (t 1))) ++ natWord (m.code (circ (t 2))) ++
        natWord (m.code (circ (t 3)))) ++ natListWord (cs.map Stars.Carrier.code) ++ natListWord tr := by
  cases m <;> simp [PrimRequest.word, tupleRequest, modeBit, List.ofFn_succ, List.append_assoc]

theorem codeWE_psi (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ) (X Y : PcppVar D.pcpp)
    (hX : v rX = X.val) (f : FK) (k : Fin 4) (E : Fin 4 → ℕ) (a : D.AtomIx)
    (ha : a ∈ cand D X Y f) (hE : E k = psi D a) : codeWE d v E f k = natWord (D.mode.code (D.circ a)) := by
  cases f
  · simp only [cand, List.mem_singleton] at ha; subst ha
    simp only [codeWE, hr.cc]; rfl
  · simp only [cand, List.mem_singleton] at ha; subst ha
    simp only [codeWE, hX, hr.pcs X]; rfl
  all_goals
    obtain ⟨Z, b, rfl, -⟩ := mem_cand_psi D X Y _ a ha (by simp)
    simp only [codeWE, hE, psi, hr.esc Z b]; rfl

theorem all_congr_mem {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- **One monomial's block is the monomial's calls' entries**: the machine's product over entry indices is the image
of the product over atoms, and each call's entry is `entryOf` of its term. -/
theorem blockW_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ) (X Y : PcppVar D.pcpp)
    (pat : Fin 4 → FK) (hXS : ∀ k, pat k = .sx → v rXS = X.val * D.s) (hYS : ∀ k, pat k = .sy → v rYS = Y.val * D.s)
    (hSS : v rSS = D.s)
    (Λ : ℕ) (hm : D.mass = Λ) (hΛ : 1 ≤ Λ) (hs : D.s ≠ 0) (hsg : D.signsOk = true)
    (P : Poly4Q D.AtomIx) (j : Fin 4) (hF : ∀ k, P.F j k = wOf D X Y (pat k)) (κn : Bool) (κm : ℕ)
    (hκ : P.κ j = ((sgnZ κn * κm : ℤ) : ℚ)) (hκm : 1 ≤ κm) (kd : Fin 3) (two : Bool)
    (call : (Fin 4 → D.AtomIx) → PrimRequest) (hMag : v rMAG = magOf D Λ κm pat)
    (hcall : ∀ t : Fin 4 → D.AtomIx, (∀ k, t k ∈ cand D X Y (pat k)) →
      callWordE d v (fun k => psi D (t k)) pat two = (call t).word) :
    blockW d v kd κn pat two = (blk D P j X Y pat call).flatMap fun t => Entry.entryWord (entryOf kd D.s t) := by
  unfold blockW
  have hc : (fun k => candOf d v (pat k)) = fun k => (cand D X Y (pat k)).map (psi D) :=
    funext fun k => candOf_eq D d hr v X Y (pat k) (hXS k) (hYS k) hSS
  rw [hc, flatMap_lexProd_map]
  have hκ0 : P.κ j ≠ 0 := by
    rw [hκ]; cases κn <;> simp [sgnZ] <;> omega
  unfold blk
  rw [if_neg hκ0, List.flatMap_map]
  apply List.flatMap_congr
  intro t ht
  rw [mem_lexProd] at ht
  rw [negBitE_psi D d hr X Y κn pat t ht, hMag, hcall t ht,
    entryOf_blk D hs Λ hm hsg P j X Y pat hF κn κm hκ hκm hΛ kd call t ht]
  rfl

/-- The block's admissibility over the atoms' tuples. -/
theorem blockOk_eq (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ) (X Y : PcppVar D.pcpp)
    (pat : Fin 4 → FK) (hXS : ∀ k, pat k = .sx → v rXS = X.val * D.s) (hYS : ∀ k, pat k = .sy → v rYS = Y.val * D.s)
    (hSS : v rSS = D.s) (two : Bool)
    (okA : (Fin 4 → D.AtomIx) → Bool)
    (hok : ∀ t : Fin 4 → D.AtomIx, (∀ k, t k ∈ cand D X Y (pat k)) → callOkE d v (fun k => psi D (t k)) pat two = okA t) :
    blockOk d v pat two = (lexProd fun k => cand D X Y (pat k)).all okA := by
  unfold blockOk
  have hc : (fun k => candOf d v (pat k)) = fun k => (cand D X Y (pat k)).map (psi D) :=
    funext fun k => candOf_eq D d hr v X Y (pat k) (hXS k) (hYS k) hSS
  rw [hc, all_lexProd_map]
  exact all_congr_mem _ _ _ fun t ht => hok t ((mem_lexProd _ t).1 ht)

/-! ## The request words -/

theorem natListWord_one (c : ℕ) : natListWord [c] = natWord 1 ++ natWord c := by simp [natListWord]
theorem natListWord_two (c c' : ℕ) : natListWord [c, c'] = natWord 2 ++ (natWord c ++ natWord c') := by
  simp [natListWord]

/-- **A validity/second-moment call's word** is the copied word. -/
theorem callWord_v (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ)
    (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (hX : v rX = (posVar D.pcpp pos.1 pos.2).val) (Y : PcppVar D.pcpp)
    (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx) (ht : ∀ k, t k ∈ cand D (posVar D.pcpp pos.1 pos.2) Y (pat k)) :
    callWordE d v (fun k => psi D (t k)) pat false = (D.vCall pos t).word := by
  unfold callWordE UnionCheckData.vCall
  rw [codeWE_psi D d hr v _ Y hX _ 0 _ (t 0) (ht 0) rfl, codeWE_psi D d hr v _ Y hX _ 1 _ (t 1) (ht 1) rfl,
    codeWE_psi D d hr v _ Y hX _ 2 _ (t 2) (ht 2) rfl, codeWE_psi D d hr v _ Y hX _ 3 _ (t 3) (ht 3) rfl,
    tupleRequest_word, hr.hd, hr.tl, hX, hr.crs]
  simp only [List.map_cons, List.map_nil, natListWord_one, Bool.false_eq_true, if_false, List.append_nil,
    List.append_assoc]

/-- **A clause call's word** is the copied word. -/
theorem callWord_mu (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (v : Fin NR → ℕ)
    (i : Fin (2 ^ D.pcpp.clauseBits)) (hX : v rX = (posVar D.pcpp i 0).val) (hY : v rY = (posVar D.pcpp i 1).val)
    (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx)
    (ht : ∀ k, t k ∈ cand D (posVar D.pcpp i 0) (posVar D.pcpp i 1) (pat k)) :
    callWordE d v (fun k => psi D (t k)) pat true = (D.muCall i t).word := by
  unfold callWordE UnionCheckData.muCall
  rw [codeWE_psi D d hr v _ _ hX _ 0 _ (t 0) (ht 0) rfl, codeWE_psi D d hr v _ _ hX _ 1 _ (t 1) (ht 1) rfl,
    codeWE_psi D d hr v _ _ hX _ 2 _ (t 2) (ht 2) rfl, codeWE_psi D d hr v _ _ hX _ 3 _ (t 3) (ht 3) rfl,
    tupleRequest_word, hr.hd, hr.tl, hX, hY, hr.crs, hr.crs]
  simp only [List.map_cons, List.map_nil, natListWord_two, if_true, List.append_assoc]

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW

