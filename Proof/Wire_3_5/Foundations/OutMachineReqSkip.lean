import Proof.Wire_3_5.Foundations.OutMachineSlot1W

/-! # The request word's frame boundary: skipping `r.word` inside a marked input

The final pass's input stream holds `frame (r.word ++ seed)`, every bit behind a mark. The request word is
self-delimiting (`word_eq`: `natWord n`, the mode bit, then three `natListWord`s); PA's `skipNatM` / `readNatM` read
its fields through the marks:

* `skipListW`, **`skipList_spec`** (a list of `natWord`s skipped, its count counted down);
* `natListW`, **`natList_spec`** (a `natListWord` skipped: its length read, its entries skipped);
* `ListCaps`, `ReqCaps`, **`reqCaps_of`** (the registers' needs from `4|r.word| + 4 ≤ cap`);
* **`reqSkipW`**, **`reqSkip_spec`**: the head moves from `0` to `2|r.word|` (the seed's first mark, any tail), the
  mode bit lands in `M`, every other register is kept (`0`).

Shared by SA's slot 1 (the seed's frames) and slot 0 (the trimmed request word).

Paper quantity of the main type: the request word's end inside the final pass's input (P3:3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.ReqSkip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (skipNatM readNatM skipNatM_spec readNatM_spec)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)
open NearCubicWires.RepairRepresentation (natWord natListWord)

section Parse
variable {ns nr : ℕ} (cap : ℕ) (i : Fin (ns + 1)) (f c v p t : Fin nr)

theorem enc_true (w : List Bool) : PrimAsm.ParseNat.enc true w = marks w := rfl

/-- A list of `natWord`s skipped, `v` counted down. -/
def skipListW : WM ns nr := .whr v (.seq (.dec v) (skipNatM true i f c))

theorem skipList_spec (hfc : f ≠ c) (hfv : f ≠ v) (hcv : c ≠ v) (rest : List Bool) :
    ∀ (xs : List ℕ) (pre : List Bool) (σ : WState ns nr), σ.st i = pre ++ marks (xs.flatMap natWord) ++ rest →
      σ.sh i = pre.length → σ.val v = xs.length → σ.val f = 0 → σ.val c = 0 →
      (∀ x ∈ xs, natBitLength x + 1 ≤ cap) → xs.length ≤ cap →
      WExec cap (skipListW i f c v) σ ((σ.seth i (pre.length + 2 * (xs.flatMap natWord).length)).setv v 0)
        (24 * (xs.flatMap natWord).length + 1)
  | [], pre, σ, _, hsh, hv, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hv) ?_ (by simp)
    refine WState.eq ?_ rfl ?_ rfl
    · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs with h
      · subst h; simp [hsh]
      · rfl
    · funext q; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs with h
      · subst h; simp [hv]
      · rfl
  | x :: xs, pre, σ, hst, hsh, hv, hf, hc, hx, hl => by
    have s1 := WExec.dec (cap := cap) v σ (by rw [hv]; exact hl)
    have s2 := skipNatM_spec cap true i f c hfc x pre (marks (xs.flatMap natWord) ++ rest) (σ.setv v (σ.val v - 1))
      (by simp only [WState.setv_st]; rw [hst, enc_true]; simp [marks_append, List.append_assoc])
      (by simp only [WState.setv_sh]; exact hsh)
      (by simp only [WState.setv_val, Function.update_apply, if_neg hfv]; exact hf)
      (by simp only [WState.setv_val, Function.update_apply, if_neg (Ne.symm hcv).symm]; exact hc)
      (hx x (by simp))
    have ih := skipList_spec hfc hfv hcv rest xs (pre ++ marks (natWord x))
      ((σ.setv v (σ.val v - 1)).seth i (pre.length + PrimAsm.ParseNat.stp true * (natWord x).length))
      (by simp only [WState.seth_st, WState.setv_st]; rw [hst]; simp [marks_append, List.append_assoc])
      (by simp only [WState.seth_sh, Function.update_self, marks_length, List.length_append]; rfl)
      (by simp only [WState.seth_val, WState.setv_val, Function.update_self, hv]; simp)
      (by simp only [WState.seth_val, WState.setv_val, Function.update_apply, if_neg hfv]; exact hf)
      (by simp only [WState.seth_val, WState.setv_val, Function.update_apply, if_neg (Ne.symm hcv).symm]; exact hc)
      (fun y hy => hx y (by simp [hy])) (by simp at hl; omega)
    have hne : σ.val v ≠ 0 := by rw [hv]; simp
    refine WExec.cast cap (WExec.whrT hne (WExec.seq s1 s2) ih) ?_ ?_
    · refine WState.eq ?_ rfl ?_ rfl
      · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
        split_ifs with h
        · subst h; simp [marks_length, List.flatMap_cons]; ring
        · rfl
      · funext q; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
        split_ifs <;> rfl
    · have := PrimAsm.ParseNat.natWord_length x
      simp only [List.flatMap_cons, List.length_append]
      omega

/-- A `natListWord` skipped: the length read into `v`, the entries skipped. -/
def natListW : WM ns nr := .seq (readNatM true i f c v p t) (skipListW i f c v)

/-- The cost of `natListW`. -/
def natListCost (xs : List ℕ) : ℕ :=
  (natBitLength xs.length + 2) * (40 * 2 ^ natBitLength xs.length + 40) + 1 + (24 * (xs.flatMap natWord).length + 1)

/-- The registers' needs of one `natListWord`. -/
def ListCaps (xs : List ℕ) : Prop :=
  2 ^ (natBitLength xs.length + 1) ≤ cap ∧ (∀ x ∈ xs, natBitLength x + 1 ≤ cap) ∧ xs.length ≤ cap

theorem natList_spec (hfc : f ≠ c) (hfv : f ≠ v) (hfp : f ≠ p) (hft : f ≠ t) (hcv : c ≠ v) (hcp : c ≠ p)
    (hct : c ≠ t) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (xs : List ℕ) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st i = pre ++ marks (natListWord xs) ++ rest) (hsh : σ.sh i = pre.length)
    (hf : σ.val f = 0) (hc : σ.val c = 0) (hv : σ.val v = 0) (hp : σ.val p = 0) (ht : σ.val t = 0)
    (hcap : ListCaps cap xs) :
    WExec cap (natListW i f c v p t) σ (σ.seth i (pre.length + 2 * (natListWord xs).length)) (natListCost xs) := by
  obtain ⟨h1, h2, h3⟩ := hcap
  have s1 := readNatM_spec cap true i f c v p t hfc hfv hfp hft hcv hcp hct hpv hpt hvt xs.length pre
    (marks (xs.flatMap natWord) ++ rest) σ (by rw [hst, enc_true]; simp [natListWord, marks_append, List.append_assoc])
    hsh hf hc hp ht (by rw [hv]; omega)
  have s2 := skipList_spec cap i f c v hfc hfv hcv rest xs (pre ++ marks (natWord xs.length))
    ((σ.seth i (pre.length + PrimAsm.ParseNat.stp true * (natWord xs.length).length)).setv v (σ.val v + xs.length))
    (by simp only [WState.setv_st, WState.seth_st]; rw [hst]; simp [natListWord, marks_append, List.append_assoc])
    (by simp only [WState.setv_sh, WState.seth_sh, Function.update_self, marks_length, List.length_append]; rfl)
    (by simp [hv]) (by simp only [WState.setv_val, WState.seth_val, Function.update_apply, if_neg hfv]; exact hf)
    (by simp only [WState.setv_val, WState.seth_val, Function.update_apply, if_neg (Ne.symm hcv).symm]; exact hc)
    h2 h3
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by unfold natListCost; omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs with h
    · subst h; simp [natListWord, marks_length]; ring
    · rfl
  · funext q; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs with h
    · subst h; exact hv.symm
    · rfl

/-- **The request word skipped**: `natWord n`, the mode bit (into `M`), the three `natListWord`s. -/
def reqSkipW (M : Fin nr) : WM ns nr :=
  .seq (skipNatM true i f c) (.seq (.fwd i) (.seq (.ifs i (.inc M) .skip) (.seq (.fwd i)
    (.seq (natListW i f c v p t) (.seq (natListW i f c v p t) (natListW i f c v p t))))))

/-- The registers' needs of the request word. -/
def ReqCaps (r : PrimRequest) : Prop :=
  natBitLength r.n + 1 ≤ cap ∧ 1 ≤ cap ∧ ListCaps cap (PrimAsm.Codec.codeList r) ∧
    ListCaps cap (PrimAsm.Codec.carrierCodes r) ∧ ListCaps cap r.translation

/-- The cost of `reqSkipW`. -/
def reqCost (r : PrimRequest) : ℕ :=
  20 * natBitLength r.n + 20 + 1 + (1 + 1 + (4 + 1 + (1 + 1 + (natListCost (PrimAsm.Codec.codeList r) + 1 +
    (natListCost (PrimAsm.Codec.carrierCodes r) + 1 + natListCost r.translation)))))

theorem word_split3 (r : PrimRequest) :
    r.word = natWord r.n ++ ([PrimAsm.Codec.modeBit r.mode] ++ (natListWord (PrimAsm.Codec.codeList r) ++
      (natListWord (PrimAsm.Codec.carrierCodes r) ++ natListWord r.translation))) := by
  rw [PrimAsm.Codec.word_eq]
  simp only [natListWord, PrimAsm.Codec.codeList_length, List.append_assoc]

theorem rd_mark (w rest : List Bool) (b : Bool) :
    readTapeBit (marks w ++ (true :: b :: rest)) ((marks w).length + 1) = b := by
  unfold readTapeBit; rw [List.getD_append_right _ _ _ _ (by omega)]; simp

theorem reqSkip_spec (hfc : f ≠ c) (hfv : f ≠ v) (hfp : f ≠ p) (hft : f ≠ t) (hcv : c ≠ v) (hcp : c ≠ p)
    (hct : c ≠ t) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (M : Fin nr) (hMf : M ≠ f) (hMc : M ≠ c) (hMv : M ≠ v)
    (hMp : M ≠ p) (hMt : M ≠ t) (r : PrimRequest) (tail : List Bool) (σ : WState ns nr)
    (hst : σ.st i = marks r.word ++ tail) (hsh : σ.sh i = 0) (hf : σ.val f = 0) (hc : σ.val c = 0)
    (hv : σ.val v = 0) (hp : σ.val p = 0) (ht : σ.val t = 0) (hM : σ.val M = 0) (hcap : ReqCaps cap r) :
    WExec cap (reqSkipW i f c v p t M) σ
      ((σ.seth i (2 * r.word.length)).setv M (if PrimAsm.Codec.modeBit r.mode then 1 else 0)) (reqCost r) := by
  obtain ⟨cn, c1, cC, cK, cT⟩ := hcap
  have hw := word_split3 r
  -- `natWord n`
  have s1 := skipNatM_spec cap true i f c hfc r.n [] (marks ([PrimAsm.Codec.modeBit r.mode] ++
      (natListWord (PrimAsm.Codec.codeList r) ++ (natListWord (PrimAsm.Codec.carrierCodes r) ++
        natListWord r.translation))) ++ tail) σ
    (by rw [hst, hw, enc_true]; simp [marks, List.append_assoc]) (by simp [hsh]) hf hc cn
  set σ1 := σ.seth i (([] : List Bool).length + PrimAsm.ParseNat.stp true * (natWord r.n).length) with hσ1
  -- the mode bit
  have s2 := WExec.fwd (cap := cap) i σ1
  set σ2 := σ1.seth i (σ1.sh i + 1) with hσ2
  have h2st : σ2.st i = marks (natWord r.n) ++ (true :: PrimAsm.Codec.modeBit r.mode ::
      (marks (natListWord (PrimAsm.Codec.codeList r) ++ (natListWord (PrimAsm.Codec.carrierCodes r) ++
        natListWord r.translation)) ++ tail)) := by
    rw [hσ2, WState.seth_st, hσ1, WState.seth_st, hst, hw]; simp [marks, List.append_assoc]
  have h2sh : σ2.sh i = (marks (natWord r.n)).length + 1 := by
    rw [hσ2, WState.seth_sh, Function.update_self, hσ1, WState.seth_sh, Function.update_self, marks_length]
    simp [PrimAsm.ParseNat.stp]
  have hb : wbit σ2 i = PrimAsm.Codec.modeBit r.mode := by
    simp only [wbit, h2st, h2sh]; exact rd_mark _ _ _
  have h2v : σ2.val = σ.val := by rw [hσ2, WState.seth_val, hσ1, WState.seth_val]
  obtain ⟨σ3, s3, e3⟩ : ∃ σ3, WExec cap (.ifs i (.inc M) .skip) σ2 σ3 4 ∧
      σ3 = σ2.setv M (if PrimAsm.Codec.modeBit r.mode then 1 else 0) := by
    cases hmbv : PrimAsm.Codec.modeBit r.mode
    · refine ⟨σ2, WExec.mono (WExec.ifsF (by rw [hb, hmbv]) (WExec.skip σ2)) (by omega), ?_⟩
      refine WState.eq rfl rfl ?_ rfl
      funext q
      by_cases h : q = M
      · subst h; simp [h2v, hM]
      · simp [Function.update_apply, h]
    · have hlt : σ2.val M < cap := by rw [h2v, hM]; omega
      refine ⟨_, WExec.mono (WExec.ifsT (by rw [hb, hmbv]) (WExec.inc M σ2 hlt)) (by omega), ?_⟩
      simp [h2v, hM]
  have s4 := WExec.fwd (cap := cap) i σ3
  set σ4 := σ3.seth i (σ3.sh i + 1) with hσ4
  have h4sh : σ4.sh i = (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode])).length := by
    rw [hσ4, WState.seth_sh, Function.update_self, e3, WState.setv_sh, h2sh]
    simp [marks_length]
  have h4st : σ4.st i = marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode]) ++
      (marks (natListWord (PrimAsm.Codec.codeList r)) ++ (marks (natListWord (PrimAsm.Codec.carrierCodes r)) ++
        (marks (natListWord r.translation) ++ tail))) := by
    rw [hσ4, WState.seth_st, e3, WState.setv_st, h2st]; simp [marks, List.append_assoc]
  have hval4 : ∀ q, q ≠ M → σ4.val q = σ.val q := by
    intro q hq
    rw [hσ4, WState.seth_val, e3, WState.setv_val, Function.update_apply, if_neg hq, h2v]
  -- the three lists
  have s5 := natList_spec cap i f c v p t hfc hfv hfp hft hcv hcp hct hpv hpt hvt (PrimAsm.Codec.codeList r)
    (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode]))
    (marks (natListWord (PrimAsm.Codec.carrierCodes r)) ++ (marks (natListWord r.translation) ++ tail)) σ4
    (by rw [h4st]; simp [List.append_assoc]) h4sh
    (by rw [hval4 f (Ne.symm hMf)]; exact hf) (by rw [hval4 c (Ne.symm hMc)]; exact hc)
    (by rw [hval4 v (Ne.symm hMv)]; exact hv) (by rw [hval4 p (Ne.symm hMp)]; exact hp)
    (by rw [hval4 t (Ne.symm hMt)]; exact ht) cC
  set σ5 := σ4.seth i ((marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode])).length +
    2 * (natListWord (PrimAsm.Codec.codeList r)).length) with hσ5
  have s6 := natList_spec cap i f c v p t hfc hfv hfp hft hcv hcp hct hpv hpt hvt (PrimAsm.Codec.carrierCodes r)
    (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode]) ++ marks (natListWord (PrimAsm.Codec.codeList r)))
    (marks (natListWord r.translation) ++ tail) σ5
    (by rw [hσ5, WState.seth_st, h4st]; simp [List.append_assoc])
    (by rw [hσ5, WState.seth_sh, Function.update_self]; simp [marks_length]; omega)
    (by rw [hσ5, WState.seth_val, hval4 f (Ne.symm hMf)]; exact hf)
    (by rw [hσ5, WState.seth_val, hval4 c (Ne.symm hMc)]; exact hc)
    (by rw [hσ5, WState.seth_val, hval4 v (Ne.symm hMv)]; exact hv)
    (by rw [hσ5, WState.seth_val, hval4 p (Ne.symm hMp)]; exact hp)
    (by rw [hσ5, WState.seth_val, hval4 t (Ne.symm hMt)]; exact ht) cK
  set σ6 := σ5.seth i ((marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode]) ++
    marks (natListWord (PrimAsm.Codec.codeList r))).length +
    2 * (natListWord (PrimAsm.Codec.carrierCodes r)).length) with hσ6
  have s7 := natList_spec cap i f c v p t hfc hfv hfp hft hcv hcp hct hpv hpt hvt r.translation
    (marks (natWord r.n ++ [PrimAsm.Codec.modeBit r.mode]) ++ marks (natListWord (PrimAsm.Codec.codeList r)) ++
      marks (natListWord (PrimAsm.Codec.carrierCodes r))) tail σ6
    (by rw [hσ6, WState.seth_st, hσ5, WState.seth_st, h4st]; simp [List.append_assoc])
    (by rw [hσ6, WState.seth_sh, Function.update_self]; simp [marks_length]; omega)
    (by rw [hσ6, WState.seth_val, hσ5, WState.seth_val, hval4 f (Ne.symm hMf)]; exact hf)
    (by rw [hσ6, WState.seth_val, hσ5, WState.seth_val, hval4 c (Ne.symm hMc)]; exact hc)
    (by rw [hσ6, WState.seth_val, hσ5, WState.seth_val, hval4 v (Ne.symm hMv)]; exact hv)
    (by rw [hσ6, WState.seth_val, hσ5, WState.seth_val, hval4 p (Ne.symm hMp)]; exact hp)
    (by rw [hσ6, WState.seth_val, hσ5, WState.seth_val, hval4 t (Ne.symm hMt)]; exact ht) cT
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5
    (WExec.seq s6 s7)))))) ?_ (by unfold reqCost; omega)
  refine WState.eq ?_ ?_ ?_ ?_
  · funext j
    rw [WState.setv_sh, WState.seth_sh, hσ6, WState.seth_sh, hσ5, WState.seth_sh, hσ4, WState.seth_sh, e3,
      WState.setv_sh]
    by_cases h : j = i
    · subst h
      simp only [Function.update_self]
      rw [hw]; simp [marks_length]; ring
    · simp only [Function.update_apply, if_neg h, hσ2, hσ1, WState.seth_sh]
  · rw [WState.setv_st, WState.seth_st, hσ6, WState.seth_st, hσ5, WState.seth_st, hσ4, WState.seth_st, e3,
      WState.setv_st, hσ2, WState.seth_st, hσ1, WState.seth_st]
    rfl
  · rw [WState.setv_val, WState.seth_val, hσ6, WState.seth_val, hσ5, WState.seth_val, hσ4, WState.seth_val, e3,
      WState.setv_val, h2v]
    rfl
  · rw [WState.setv_cell, WState.seth_cell, hσ6, WState.seth_cell, hσ5, WState.seth_cell, hσ4, WState.seth_cell, e3,
      WState.setv_cell, hσ2, WState.seth_cell, hσ1, WState.seth_cell]
    rfl

end Parse

/-- **The registers' needs from the request word's length.** -/
theorem reqCaps_of (cap : ℕ) (r : PrimRequest) (h : 4 * r.word.length + 4 ≤ cap) : ReqCaps cap r := by
  have hw := word_split3 r
  have hlen := congrArg List.length hw
  simp only [List.length_append, natListWord, List.length_singleton, List.length_cons, List.length_nil] at hlen
  have hn := PrimAsm.ParseNat.natWord_length r.n
  have lc : ∀ xs : List ℕ, (natWord xs.length).length + (xs.flatMap natWord).length ≤ r.word.length →
      ListCaps cap xs := by
    intro xs hx
    have hl := PrimAsm.ParseNat.natWord_length xs.length
    have h2 := PrimAsm.CopyNat.two_pow_natBitLength_le xs.length
    have hfl : xs.length ≤ (xs.flatMap natWord).length := by
      rw [List.length_flatMap]
      calc xs.length = (xs.map fun _ => 1).sum := by simp
        _ ≤ (xs.map fun x => (natWord x).length).sum := by
          apply List.sum_le_sum; intro x _; rw [PrimAsm.ParseNat.natWord_length]; omega
    refine ⟨by rw [pow_succ]; omega, fun x hx' => ?_, by omega⟩
    have hle : (natWord x).length ≤ (xs.flatMap natWord).length := by
      rw [List.length_flatMap]
      exact List.le_sum_of_mem (List.mem_map.2 ⟨x, hx', rfl⟩)
    rw [PrimAsm.ParseNat.natWord_length] at hle
    omega
  refine ⟨by omega, by omega, lc _ (by omega), lc _ (by omega), lc _ (by omega)⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.ReqSkip
