import Proof.Wire_3_5.Primitive.SeedFix.HbLoop

/-! # C4.Hb, machine part 19: the machine prints `hashTermsM` (`filt:soft`, P3:2253-2290)

"Expand each `A`-product into at most `2^{2t}` signed products of hash prefix indicators [...] After fixing `p`,
Gaussian elimination finds its conditional probability [...] The cleared weights make every coefficient an integer"
(P3:2262-2268). The machine's cell `c` prints exactly the reference cell `hcell` of HashRefM at the decoded
`(q, e, p, λ, ι, γ)` (**`cell_link`**): validity (`validC_link`), the elimination count
(`cntG = 2^x` iff consistent, `elim_count`), and the term word (`coefWord (±W·2^x)`, the HASH factor, the `2t`
factors).

Paper quantity of the main type (**`cell_link`**): the reference cell's term `hcell` of `hashTermsM`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimT.HashB
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (termWord coefWord polyWord)

/-- The cleared weights' bits, levels `λ ≤ J`: `W_λ = clearW λ`, `W_J = prodW`. -/
def wsOf (MP : MajorantParams) : List (List Bool) :=
  (List.range (MP.J + 1)).map fun lam => Nat.bits (if lam < MP.J then SeedFix.clearW MP lam else SeedFix.prodW MP)

/-- The Hb machine's data is the reference's. -/
structure Matches (X : HbX) (MP : MajorantParams) (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ))
    (plen pre : ℕ) : Prop where
  Fs : X.Fs = Fs
  pops : X.pops = pops
  Ws : X.Ws = wsOf MP
  G : X.G = G
  N2 : X.N2 = N ^ 2
  nE : X.nE = nE
  J : X.J = MP.J
  T2 : X.T2 = 2 * MP.t
  ℓ : X.ℓ = MP.ell0
  mod : X.mod = MP.refMod
  plen : X.plen = plen
  pfx : X.pfx = pre

section Cell
variable (X : HbX) (MP : MajorantParams)

/-- The decoded positions and signs as the reference's digit functions. -/
def ιF (hℓ : X.ℓ = MP.ell0) (c : ℕ) : Fin (2 * MP.t) → Fin (2 ^ MP.ell0) :=
  fun r => ⟨(X.ιsOf c).getD r.val 0, by
    rw [← hℓ]
    by_cases hr : r.val < (X.ιsOf c).length
    · rw [List.getD_eq_getElem _ _ hr]
      simp only [HbX.ιsOf, List.getElem_map, List.getElem_range]
      exact Nat.mod_lt _ (by positivity)
    · rw [List.getD_eq_default _ _ (by omega)]; positivity⟩

def γF (c : ℕ) : Fin (2 * MP.t) → Bool := fun r => (X.γsOf c).getD r.val false

theorem validC_link (hT : X.T2 = 2 * MP.t) (hℓ : X.ℓ = MP.ell0) (hJ : X.J = MP.J) (c : ℕ) (hc : c < X.n) :
    X.validC c = decide (validOf MP (X.popOf c).2.length (X.lamOf c) (ιF X MP hℓ c) (γF X MP c)) := by
  obtain ⟨_, hJ1, _, _, _⟩ := pos_of_lt_n X c hc
  have hlamJ : X.lamOf c ≤ X.J := Nat.lt_succ_iff.mp (Nat.mod_lt _ hJ1)
  have hγl : (X.γsOf c).length = X.T2 := binary_length _ _
  have hιl : (X.ιsOf c).length = X.T2 := by simp [HbX.ιsOf]
  unfold HbX.validC validB gB iB validOf
  rw [hγl, hιl]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ιF, γF, Fin.ext_iff]
  rw [← hJ, ← hT]
  constructor
  · rintro ⟨hg, hi⟩
    refine ⟨fun r => (hi r.val r.isLt).1, fun heq => ⟨fun r => ?_, fun r s => ?_⟩⟩
    · rcases hg with h | h
      · omega
      · exact h r.val r.isLt
    · have h1 := (hi r.val r.isLt).2
      have h2 := (hi s.val s.isLt).2
      rcases h1 with h1 | h1
      · omega
      rcases h2 with h2 | h2
      · omega
      rw [h1, h2]
  · rintro ⟨hl, hA⟩
    by_cases hlt : X.lamOf c < X.J
    · exact ⟨Or.inl hlt, fun i hi => ⟨hl ⟨i, hi⟩, Or.inl hlt⟩⟩
    · have heq : X.lamOf c = X.J := by omega
      obtain ⟨hγ, hι⟩ := hA heq
      refine ⟨Or.inr fun i hi => hγ ⟨i, hi⟩, fun i hi => ⟨hl ⟨i, hi⟩, Or.inr ?_⟩⟩
      have hT0 : 0 < X.T2 := by omega
      exact hι ⟨i, hi⟩ ⟨0, hT0⟩

theorem consOf_link (hT : X.T2 = 2 * MP.t) (hℓ : X.ℓ = MP.ell0) (hJ : X.J = MP.J) (c : ℕ) :
    consOf MP (X.lamOf c) (ιF X MP hℓ c) (γF X MP c) = X.consOfC c := by
  have hιl : (X.ιsOf c).length = 2 * MP.t := by simp [HbX.ιsOf, hT]
  unfold consOf HbX.consOfC consL
  rw [hιl, hJ]
  apply List.ext_getElem
  · simp
  · intro r h1 h2
    simp [ιF, γF]

theorem kOf_link (hJ : X.J = MP.J) (c : ℕ) : kOf MP (X.lamOf c) = X.kOfC c := by
  unfold kOf HbX.kOfC kOfL; rw [hJ]

theorem cntG_link (hT : X.T2 = 2 * MP.t) (hℓ : X.ℓ = MP.ell0) (hJ : X.J = MP.J) (hmod : X.mod = MP.refMod)
    (plen pre : ℕ) (hplen : X.plen = plen) (hpfx : X.pfx = pre) (c : ℕ) :
    SeedFix.cntG MP (kOf MP (X.lamOf c)) plen pre (consOf MP (X.lamOf c) (ιF X MP hℓ c) (γF X MP c)) =
      if (X.ggOf c).1 then 2 ^ X.xOf c else 0 := by
  rw [consOf_link X MP hT hℓ hJ c, kOf_link X MP hJ c]
  unfold SeedFix.cntG
  rw [← SeedFix.elim_count]
  unfold HbX.xOf HbX.ggOf
  rw [hT, hℓ, hmod, hplen, hpfx]

end Cell

section Coef

theorem bits_mul_two_pow (W : ℕ) (hW : 0 < W) : ∀ x : ℕ, Nat.bits (W * 2 ^ x) = List.replicate x false ++ Nat.bits W
  | 0 => by simp
  | x + 1 => by
    rw [pow_succ, ← Nat.mul_assoc, Nat.mul_comm (W * 2 ^ x) 2, Nat.bit0_bits _ (by positivity),
      bits_mul_two_pow W hW x, List.replicate_succ, List.cons_append]

theorem pairs_append (u v : List Bool) : pairs (u ++ v) = pairs u ++ pairs v := by
  simp [pairs, List.flatMap_append]

/-- **The coefficient word** of `±W·2^x`. -/
theorem coefWord_link (W x : ℕ) (hW : 0 < W) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    coefWord ((W : ℤ) * s * 2 ^ x) = coefBits (decide (s = -1)) x (Nat.bits W) := by
  have habs : ((W : ℤ) * s * 2 ^ x).natAbs = W * 2 ^ x := by
    rcases hs with rfl | rfl <;> simp [Int.natAbs_mul, Int.natAbs_pow]
  have hneg : decide ((W : ℤ) * s * 2 ^ x < 0) = decide (s = -1) := by
    have hWp : (0 : ℤ) < W := by exact_mod_cast hW
    have h2 : (0 : ℤ) < 2 ^ x := by positivity
    rcases hs with rfl | rfl
    · simp only [mul_one]; rw [decide_eq_false (not_lt.mpr (by positivity)), decide_eq_false (by norm_num)]
    · rw [decide_eq_true (by nlinarith), decide_eq_true rfl]
  unfold coefWord coefBits
  rw [habs, hneg, bits_mul_two_pow W hW x]
  show true :: decide (s = -1) :: frame (List.replicate x false ++ W.bits) = _
  simp only [frame_pairs, pairs_append, pairs_rep_false]
  simp

theorem neg_one_pow_neg_iff (k : ℕ) : ((-1 : ℤ) ^ k = -1) ↔ k % 2 = 1 := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow]; have := Nat.even_iff.mp h; constructor <;> intro <;> omega
  · rw [h.neg_one_pow]; have := Nat.odd_iff.mp h; simp [this]

theorem card_false_eq : ∀ (l : List Bool),
    (Finset.univ.filter fun r : Fin l.length => l.getD r.val false = false).card = l.count false
  | [] => by simp
  | b :: l => by
    have ih := card_false_eq l
    rw [Finset.card_filter] at ih ⊢
    rw [List.length_cons, Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    rw [ih, List.count_cons]
    cases b <;> simp <;> omega

theorem clearW_pos (MP : MajorantParams) (j : ℕ) : 0 < SeedFix.clearW MP j :=
  Finset.prod_pos fun j' _ => pow_pos (by have := MP.W_ge j'; omega) _

end Coef

section Term
variable (X : HbX) (MP : MajorantParams)

theorem wsOf_getD (MP : MajorantParams) (lam : ℕ) (h : lam ≤ MP.J) :
    (wsOf MP).getD lam [] = Nat.bits (if lam < MP.J then SeedFix.clearW MP lam else SeedFix.prodW MP) := by
  unfold wsOf
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem sgnG_link (hT : X.T2 = 2 * MP.t) (c : ℕ) :
    (sgnG (γF X MP c) = -1) ↔ parZ (X.γsOf c) = 1 := by
  have hl : (X.γsOf c).length = 2 * MP.t := by rw [← hT]; exact binary_length _ _
  unfold sgnG parZ
  rw [neg_one_pow_neg_iff]
  have := card_false_eq (X.γsOf c)
  have e : (Finset.univ.filter fun k : Fin (2 * MP.t) => γF X MP c k = false).card =
      (Finset.univ.filter fun r : Fin (X.γsOf c).length => (X.γsOf c).getD r.val false = false).card := by
    rw [hl]; rfl
  rw [e, this]

end Term

section CellLink
variable (X : HbX) (MP : MajorantParams)

theorem flatMap_ofFn_getD (l : List ℕ) (n : ℕ) (h : l.length = n) (g : ℕ → List Bool) :
    l.flatMap g = (List.ofFn fun r : Fin n => l.getD r.val 0).flatMap g := by
  subst h
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem _ _ h1]

/-- **The machine's cell prints the reference's cell.** -/
theorem cell_link (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ)) (plen pre : ℕ)
    (hM : Matches X MP G N nE Fs pops plen pre) (c : ℕ) (hc : c < X.n) :
    X.cellWord c = (hcell MP G (Fs.getD (X.qOf c * nE + X.eOf c) []) (X.qOf c) (popOf pops (X.pOf c)) plen pre
      (X.lamOf c) (ιF X MP hM.ℓ c) (γF X MP c)).flatMap (fun t => true :: termWord t) := by
  obtain ⟨_, hJ1, _, _, _⟩ := pos_of_lt_n X c hc
  have hlamJ : X.lamOf c ≤ X.J := Nat.lt_succ_iff.mp (Nat.mod_lt _ hJ1)
  have hpop : X.popOf c = popOf pops (X.pOf c) := by unfold HbX.popOf popOf; rw [hM.pops]
  have hvl := validC_link X MP hM.T2 hM.ℓ hM.J c hc
  rw [hpop] at hvl
  have hcl := cntG_link X MP hM.T2 hM.ℓ hM.J hM.mod plen pre hM.plen hM.pfx c
  unfold HbX.cellWord hcell
  rw [hvl, hcl]
  by_cases hv : validOf MP (popOf pops (X.pOf c)).2.length (X.lamOf c) (ιF X MP hM.ℓ c) (γF X MP c)
  · by_cases hg : (X.ggOf c).1 = true
    · rw [if_pos ⟨decide_eq_true hv, hg⟩, if_pos ⟨hv, by rw [if_pos hg]; positivity⟩, if_pos hg]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      -- the term
      have hW : X.Ws.getD (X.lamOf c) [] =
          Nat.bits (if X.lamOf c < MP.J then SeedFix.clearW MP (X.lamOf c) else SeedFix.prodW MP) := by
        rw [hM.Ws]; exact wsOf_getD MP _ (by rw [← hM.J]; exact hlamJ)
      have hF : X.Fs.getD (X.idxOf c) [] = Fs.getD (X.qOf c * nE + X.eOf c) [] := by
        unfold HbX.idxOf; rw [hM.Fs, hM.nE, Nat.add_comm]
      have hιl : (X.ιsOf c).length = 2 * MP.t := by simp [HbX.ιsOf, hM.T2]
      have hZ : ((X.ιsOf c).flatMap fun i => zRec X.G (X.qOf c) (X.popOf c).1 ((X.popOf c).2.getD i 0)) =
          (List.ofFn fun r => zPoly G (X.qOf c) (popOf pops (X.pOf c)).1
            ((popOf pops (X.pOf c)).2.getD ((ιF X MP hM.ℓ c) r) 0)).flatMap (fun f => true :: polyWord f) := by
        rw [flatMap_ofFn_getD _ (2 * MP.t) hιl, hpop, hM.G]
        rw [show (List.ofFn fun r => zPoly G (X.qOf c) (popOf pops (X.pOf c)).1
            ((popOf pops (X.pOf c)).2.getD ((ιF X MP hM.ℓ c) r) 0)) =
            (List.ofFn fun r : Fin (2 * MP.t) => (X.ιsOf c).getD r.val 0).map
              (fun i => zPoly G (X.qOf c) (popOf pops (X.pOf c)).1 ((popOf pops (X.pOf c)).2.getD i 0)) by
          rw [List.map_ofFn]; rfl]
        rw [List.flatMap_map]
        rfl
      unfold HbX.tbOf termBits termWord
      rw [hW, hF, hZ]
      unfold wOf
      by_cases hlt : X.lamOf c < MP.J
      · have hs : sgnG (γF X MP c) = 1 ∨ sgnG (γF X MP c) = -1 := by
          unfold sgnG; rcases neg_one_pow_eq_or ℤ (Finset.univ.filter fun k => γF X MP c k = false).card with h | h
          · exact Or.inl h
          · exact Or.inr h
        have hsg : decide (X.lamOf c < X.J ∧ parZ (X.γsOf c) = 1) = decide (sgnG (γF X MP c) = -1) := by
          rw [hM.J]
          apply decide_eq_decide.mpr
          rw [sgnG_link X MP hM.T2 c]
          exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩
        rw [if_pos hlt, if_pos hlt, hsg]
        rw [show ((SeedFix.clearW MP (X.lamOf c) : ℤ) * sgnG (γF X MP c) * ((2 ^ X.xOf c : ℕ) : ℤ)) =
          (SeedFix.clearW MP (X.lamOf c) : ℤ) * sgnG (γF X MP c) * 2 ^ X.xOf c by push_cast; ring]
        rw [coefWord_link _ _ (clearW_pos MP _) _ hs]
        simp [List.append_assoc]
      · have hsg : decide (X.lamOf c < X.J ∧ parZ (X.γsOf c) = 1) = decide ((1 : ℤ) = -1) := by
          rw [hM.J]; apply decide_eq_decide.mpr; constructor
          · intro h; exact absurd h.1 hlt
          · intro h; norm_num at h
        rw [if_neg hlt, if_neg hlt, hsg]
        rw [show ((SeedFix.prodW MP : ℤ) * ((2 ^ X.xOf c : ℕ) : ℤ)) = (SeedFix.prodW MP : ℤ) * 1 * 2 ^ X.xOf c by
          push_cast; ring]
        rw [coefWord_link _ _ (SeedFix.prodW_pos MP) 1 (Or.inl rfl)]
        simp [List.append_assoc]
    · rw [if_neg (fun h => hg h.2), if_neg (fun h => h.2 (by rw [if_neg hg])), List.flatMap_nil]
  · rw [if_neg (fun h => hv (of_decide_eq_true h.1)), if_neg (fun h => hv h.1), List.flatMap_nil]

end CellLink

section Reindex

theorem range_mul_flatMap {β : Type} (a b : ℕ) (f : ℕ → List β) :
    (List.range (a * b)).flatMap f = (List.range a).flatMap fun i => (List.range b).flatMap fun j => f (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, List.flatMap_append, ih, List.range_succ, List.flatMap_append, List.flatMap_map]
    simp

/-- The base-`m` digits of `k` as a digit function. -/
def dig (m r k : ℕ) (hm : 0 < m) : Fin r → Fin m := fun j => ⟨k / m ^ j.val % m, Nat.mod_lt _ hm⟩

theorem digitsF_flatMap {β : Type} (m r : ℕ) (hm : 0 < m) (h : (Fin r → Fin m) → List β) :
    (digitsF m r).flatMap h = (List.range (m ^ r)).flatMap fun k => h (dig m r k hm) := by
  unfold digitsF
  rw [List.flatMap_map, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr (fun i _ => ?_)
  congr 1

theorem mdm (x m r : ℕ) (hr : r < m) : (x * m + r) / m = x ∧ (x * m + r) % m = r := by
  have hm : 0 < m := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem binary_getD : ∀ (w x r : ℕ), r < w → (binary w x).getD r false = (x / 2 ^ r % 2 == 1)
  | 0, _, r, h => absurd h (Nat.not_lt_zero r)
  | w + 1, x, 0, _ => by simp [SignedSortKey.binary]
  | w + 1, x, r + 1, h => by
    show (binary w (x / 2)).getD r false = _
    rw [binary_getD w (x / 2) r (by omega), Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm 2]

end Reindex

section Link
variable (X : HbX) (MP : MajorantParams)

theorem decode_cell (q e p lam ιI γI : ℕ) (hq : q < X.N2) (he : e < X.nE) (hp : p < X.P) (hl : lam < X.J + 1)
    (hι : ιI < 2 ^ (X.T2 * X.ℓ)) (hγ : γI < 2 ^ X.T2) :
    let c := ((((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) * 2 ^ (X.T2 * X.ℓ) + ιI) * 2 ^ X.T2 + γI
    X.d0 c = ιI * 2 ^ X.T2 + γI ∧ X.lamOf c = lam ∧ X.pOf c = p ∧ X.eOf c = e ∧ X.qOf c = q := by
  intro c
  have hB : X.B = 2 ^ (X.T2 * X.ℓ) * 2 ^ X.T2 := by unfold HbX.B HbX.L; rw [← pow_add, Nat.add_comm]
  have hr : ιI * 2 ^ X.T2 + γI < 2 ^ (X.T2 * X.ℓ) * 2 ^ X.T2 := by
    calc ιI * 2 ^ X.T2 + γI < ιI * 2 ^ X.T2 + 2 ^ X.T2 := by omega
      _ = (ιI + 1) * 2 ^ X.T2 := by ring
      _ ≤ 2 ^ (X.T2 * X.ℓ) * 2 ^ X.T2 := Nat.mul_le_mul_right _ hι
  have ec : c = (((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) * X.B + (ιI * 2 ^ X.T2 + γI) := by
    rw [hB]; simp only [c]; ring
  obtain ⟨d1, m1⟩ := mdm (((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) X.B _ (by rw [hB]; exact hr)
  rw [← ec] at d1 m1
  obtain ⟨d2, m2⟩ := mdm ((q * X.nE + e) * X.P + p) (X.J + 1) lam hl
  obtain ⟨d3, m3⟩ := mdm (q * X.nE + e) X.P p hp
  obtain ⟨d4, m4⟩ := mdm q X.nE e he
  refine ⟨m1, ?_, ?_, ?_, ?_⟩
  · unfold HbX.lamOf; rw [d1, m2]
  · unfold HbX.pOf; rw [d1, d2, m3]
  · unfold HbX.eOf; rw [d1, d2, d3, m4]
  · unfold HbX.qOf; rw [d1, d2, d3, d4, Nat.mod_eq_of_lt hq]

/-- **The machine prints `hashTermsM`**: the output before cell `n` is the term records of the reference
expression. -/
theorem outAt_link (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ)) (plen pre : ℕ)
    (hM : Matches X MP G N nE Fs pops plen pre) :
    X.outAt X.n = (hashTermsM MP G N nE Fs pops plen pre).flatMap (fun t => true :: termWord t) := by
  have hn : X.n = (((X.N2 * X.nE) * X.P) * (X.J + 1)) * 2 ^ (X.T2 * X.ℓ) * 2 ^ X.T2 := by
    unfold HbX.n HbX.B HbX.L; rw [pow_add]; ring
  unfold HbX.outAt hashTermsM
  rw [hn]
  simp only [range_mul_flatMap, List.flatMap_assoc]
  simp only [digitsF_flatMap (2 ^ MP.ell0) (2 * MP.t) (by positivity : 0 < 2 ^ MP.ell0), List.flatMap_assoc]
  simp only [digitsF_flatMap 2 (2 * MP.t) (by norm_num : 0 < 2)]
  have e1 : (2 ^ MP.ell0) ^ (2 * MP.t) = 2 ^ (X.T2 * X.ℓ) := by rw [hM.T2, hM.ℓ, ← pow_mul, Nat.mul_comm]
  have e2 : (2 : ℕ) ^ (2 * MP.t) = 2 ^ X.T2 := by rw [hM.T2]
  rw [e1, e2, hM.N2.symm, hM.nE.symm, hM.J.symm]
  have hP : X.P = pops.length := by unfold HbX.P; rw [hM.pops]
  rw [hP.symm]
  refine List.flatMap_congr (fun q hq => List.flatMap_congr (fun e he => List.flatMap_congr (fun p hp =>
    List.flatMap_congr (fun lam hl => List.flatMap_congr (fun ιI hι => List.flatMap_congr (fun γI hγ => ?_))))))
  rw [List.mem_range] at hq he hp hl hι hγ
  obtain ⟨hd0, hlam, hpo, heo, hqo⟩ := decode_cell X q e p lam ιI γI hq he hp hl hι hγ
  set c := ((((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) * 2 ^ (X.T2 * X.ℓ) + ιI) * 2 ^ X.T2 + γI with hc
  have hcn : c < X.n := by
    rw [hn]
    have h5 : ((q * X.nE + e) * X.P + p) * (X.J + 1) + lam < X.N2 * X.nE * X.P * (X.J + 1) := by
      have a1 : q * X.nE + e < X.N2 * X.nE := by
        calc q * X.nE + e < q * X.nE + X.nE := by omega
          _ = (q + 1) * X.nE := by ring
          _ ≤ X.N2 * X.nE := Nat.mul_le_mul_right _ hq
      have a2 : (q * X.nE + e) * X.P + p < X.N2 * X.nE * X.P := by
        calc (q * X.nE + e) * X.P + p < (q * X.nE + e) * X.P + X.P := by omega
          _ = (q * X.nE + e + 1) * X.P := by ring
          _ ≤ X.N2 * X.nE * X.P := Nat.mul_le_mul_right _ a1
      calc ((q * X.nE + e) * X.P + p) * (X.J + 1) + lam < ((q * X.nE + e) * X.P + p) * (X.J + 1) + (X.J + 1) := by omega
        _ = ((q * X.nE + e) * X.P + p + 1) * (X.J + 1) := by ring
        _ ≤ X.N2 * X.nE * X.P * (X.J + 1) := Nat.mul_le_mul_right _ a2
    have h6 : (((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) * 2 ^ (X.T2 * X.ℓ) + ιI <
        X.N2 * X.nE * X.P * (X.J + 1) * 2 ^ (X.T2 * X.ℓ) := by
      calc (((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) * 2 ^ (X.T2 * X.ℓ) + ιI
          < (((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) * 2 ^ (X.T2 * X.ℓ) + 2 ^ (X.T2 * X.ℓ) := by omega
        _ = ((((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) + 1) * 2 ^ (X.T2 * X.ℓ) := by ring
        _ ≤ X.N2 * X.nE * X.P * (X.J + 1) * 2 ^ (X.T2 * X.ℓ) := Nat.mul_le_mul_right _ h5
    calc c < ((((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) * 2 ^ (X.T2 * X.ℓ) + ιI) * 2 ^ X.T2 + 2 ^ X.T2 := by
          rw [hc]; omega
      _ = ((((q * X.nE + e) * X.P + p) * (X.J + 1) + lam) * 2 ^ (X.T2 * X.ℓ) + ιI + 1) * 2 ^ X.T2 := by ring
      _ ≤ X.N2 * X.nE * X.P * (X.J + 1) * 2 ^ (X.T2 * X.ℓ) * 2 ^ X.T2 := Nat.mul_le_mul_right _ h6
  rw [cell_link X MP G N nE Fs pops plen pre hM c hcn, hlam, hpo, heo, hqo, hM.nE]
  -- the digit functions
  have hγs : X.γsOf c = binary X.T2 γI := by
    unfold HbX.γsOf; rw [hd0, (mdm ιI (2 ^ X.T2) γI hγ).2]
  have hιv : X.d0 c / 2 ^ X.T2 = ιI := by rw [hd0]; exact (mdm ιI (2 ^ X.T2) γI hγ).1
  have hι' : ιF X MP hM.ℓ c = dig (2 ^ MP.ell0) (2 * MP.t) ιI (by positivity) := by
    funext r
    apply Fin.ext
    have hr : r.val < (X.ιsOf c).length := by simp [HbX.ιsOf, hM.T2]
    simp only [ιF, dig]
    rw [List.getD_eq_getElem _ _ hr]
    simp only [HbX.ιsOf, List.getElem_map, List.getElem_range, hιv]
    rw [hM.ℓ, ← pow_mul, Nat.mul_comm r.val MP.ell0]
  have hγ' : γF X MP c = fun r => finTwoEquiv (dig 2 (2 * MP.t) γI (by norm_num) r) := by
    funext r
    simp only [γF, dig, hγs]
    rw [binary_getD X.T2 γI r.val (by rw [hM.T2]; exact r.isLt)]
    rcases Nat.mod_two_eq_zero_or_one (γI / 2 ^ r.val) with h | h
    · simp [h, finTwoEquiv]
    · simp [h, finTwoEquiv]
  rw [hι', hγ']

end Link

section Spec
variable (X : HbX) (MP : MajorantParams)

/-- **The Hb machine prints the hash expression** `hashTermsM` (`filt:soft`): from the invariant bank before cell `0`,
`hashLoopM` reaches, within `n·(K + 2) + 1` steps, the invariant bank before cell `n`, whose output stream holds the
term records of `hashTermsM MP G N nE Fs pops plen pre` (its `exprWord` without the final `F`). -/
theorem hbMachine_spec (G N nE : ℕ) (Fs : List (F2Poly ℕ)) (pops : List (Bool × List ℕ)) (plen pre : ℕ)
    (hM : Matches X MP G N nE Fs pops plen pre) (hok : X.HbOk) (hcell : ∀ c < X.n, X.CellOk c) (K : ℕ)
    (hK : ∀ c < X.n, X.cellCost c ≤ K) (A0 : Fin 94 → List Bool) (h0 : X.Inv 0 A0) :
    ∃ A', ExtDecompositionBatch.Step hashLoopM (X.n * (K + 2) + 1) (fun _ => 0) A0 (fun _ => 0) A' ∧ X.Inv X.n A' ∧
      X.outAt X.n = (hashTermsM MP G N nE Fs pops plen pre).flatMap (fun t => true :: termWord t) := by
  obtain ⟨A', hinv, hs⟩ := X.hashEnum_run hok hcell K hK A0 h0
  exact ⟨A', hs, hinv, outAt_link X MP G N nE Fs pops plen pre hM⟩

end Spec

end NearCubicWires.WireExponent3_5.PrimT.HbM
