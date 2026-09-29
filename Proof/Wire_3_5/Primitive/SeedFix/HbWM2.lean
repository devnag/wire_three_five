import Proof.Wire_3_5.Primitive.SeedFix.HbTermW

/-! # C4.Hb, machine part 9: the odometer's word and the cell's term (P3:2253-2290)

The odometer's binary word holds the cell's sign pattern `γ` (its first `2t` bits) and moment tuple `ι` (then `2t`
fields of `ℓ₀` bits, low bit first): `ctrWord γs ιs ℓ₀`. The term program writes, at the end of the output, the cell's
term record `T`, the coefficient word, the HASH factor `T polyWord F_{q,e}`, the `2t` factor records `T polyWord Z` and
the term's end `F` (**`termW_spec`**).

Paper quantity of the main type: the printed term of a cell (`termBits`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-- **The odometer's word**: the sign pattern, then the moment tuple's `ℓ`-bit fields. -/
def ctrWord (γs : List Bool) (ιs : List ℕ) (ℓ : ℕ) : List Bool := γs ++ (ιs.map (binary ℓ)).flatten

theorem flatten_fixed_getD (ws : List (List Bool)) (ℓ : ℕ) (hw : ∀ w ∈ ws, w.length = ℓ) (k m : ℕ)
    (hk : k < ws.length) (hm : m < ℓ) : ws.flatten.getD (k * ℓ + m) false = ws[k].getD m false := by
  induction ws generalizing k with
  | nil => simp at hk
  | cons w ws ih =>
    have hwl : w.length = ℓ := hw w List.mem_cons_self
    rw [List.flatten_cons]
    cases k with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_append _ _ _ _ (by omega)]
    | succ k =>
      rw [List.getD_append_right _ _ _ _ (by rw [hwl]; nlinarith)]
      have e : (k + 1) * ℓ + m - w.length = k * ℓ + m := by rw [hwl]; ring_nf; omega
      rw [e, ih (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) k (by simpa using hk)]
      simp

theorem ctrWord_field (γs : List Bool) (ιs : List ℕ) (ℓ k m : ℕ) (hk : k < ιs.length) (hm : m < ℓ) :
    readTapeBit (ctrWord γs ιs ℓ) (γs.length + k * ℓ + m) = (binary ℓ (ιs.getD k 0)).getD m false := by
  unfold readTapeBit ctrWord
  rw [Nat.add_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
  rw [flatten_fixed_getD (ιs.map (binary ℓ)) ℓ (fun w hw => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw; exact binary_length ℓ i) k m (by simpa using hk) hm]
  simp [List.getD_eq_getElem _ _ hk, List.getElem?_eq_getElem hk]

theorem ctrWord_sign (γs : List Bool) (ιs : List ℕ) (ℓ k : ℕ) (hk : k < γs.length) :
    readTapeBit (ctrWord γs ιs ℓ) k = γs.getD k false := by
  unfold readTapeBit ctrWord
  rw [List.getD_append _ _ _ _ hk]

section Term1
variable (cap : ℕ)

/-- The term's first half: the output's end, the term marker, the sign, the coefficient word. -/
def termW1 : HW := .seq (olenWalkW sOLEN sOUT) (.seq (emitC sOUT 0 true) (.seq signW coefW))

/-- The coefficient word of a cell. -/
def coefBits (sgn : Bool) (e : ℕ) (w : List Bool) : List Bool :=
  [true, sgn] ++ PrimAsm.FiltRec.reps e [true, false] ++ frame w

theorem termW1_spec (γs : List Bool) (ιs : List ℕ) (ℓ lam J e : ℕ) (xs : List Bool) (Ws : List (List Bool))
    (hlam : lam < Ws.length) (σ : HS) (hOL : σ.st sOLEN = List.replicate (σ.st sOUT).length true)
    (hOLh : σ.sh sOLEN = 0) (hOh : σ.sh sOUT = 0) (hC : σ.st sCTR = ctrWord γs ιs ℓ) (hCh : σ.sh sCTR = 0)
    (hX : σ.st sXE = List.replicate e true ++ false :: xs) (hXh : σ.sh sXE = 0) (hW : σ.st sWT = wtWord Ws)
    (hWh : σ.sh sWT = 0) (h0 : σ.val 0 = 0) (h9 : σ.val 9 = lam) (h10 : σ.val 10 = J) (h15 : σ.val 15 = γs.length)
    (h18 : σ.val 18 = 0) (h22 : σ.val 22 = 0) (h23 : σ.val 23 = 0) (h25 : σ.val 25 = 0) (h28 : σ.val 28 = 0)
    (h29 : σ.val 29 = 0) (h30 : σ.val 30 = 0) (h31 : σ.val 31 = 0)
    (hcap : γs.length + lam + J + 5 + 2 * e + (wtWord Ws).length ≤ cap) :
    ∃ hx hw c, c ≤ 5 * (σ.st sOUT).length + 80 + 40 * (γs.length + lam + J) +
        coefCost e lam (wtWord Ws).length (frame Ws[lam]).length ∧ WExec cap termW1 σ
      (appendO ((((((σ.seth sOLEN (σ.st sOUT).length).seth sOUT (σ.st sOUT).length).seth sCTR γs.length).setv 23
        (if lam < J ∧ parZ γs = 1 then 1 else 0)).seth sXE hx).seth sWT hw) sOUT 0
        ([true] ++ coefBits (lam < J ∧ parZ γs = 1) e Ws[lam])) c := by
  have s1 := olenWalk_loop cap sOLEN sOUT (by decide) (σ.st sOUT).length 0 σ hOL hOLh hOh (by omega)
  set σ1 := (σ.seth sOLEN (σ.st sOUT).length).seth sOUT (σ.st sOUT).length with hσ1
  have s2 := emitC_app cap sOUT 0 true σ1 (by simp [σ1]) (by simp [σ1, h0]; omega)
  obtain ⟨c3, hc3, s3⟩ := signW_spec cap γs lam J (appendO σ1 sOUT 0 [true])
    (fun k hk => by simp [σ1, hC]; exact ctrWord_sign γs ιs ℓ k hk) (by simp [σ1, hCh])
    (by simp [σ1, h9]) (by simp [σ1, h10]) (by simp [σ1, h15]) (by simp [σ1, h22]) (by simp [σ1, h23])
    (by simp [σ1, h25]) (by simp [σ1, h28]) (by simp [σ1, h29]) (by simp [σ1, h30]) (by simp [σ1, h31]) (by omega)
  set σ3 := ((appendO σ1 sOUT 0 [true]).seth sCTR γs.length).setv 23 (if lam < J ∧ parZ γs = 1 then 1 else 0)
    with hσ3
  obtain ⟨hx, hw, s4⟩ := coefW_spec cap (lam < J ∧ parZ γs = 1) e lam xs Ws hlam σ3
    (by simp only [hσ3, WState.setv_val, Function.update_self]
        by_cases h : lam < J ∧ parZ γs = 1 <;> simp [h])
    (by simp [σ3, σ1, h9]) (by simp [σ3, σ1, h18]) (by simp [σ3, σ1, h22]) (by simp [σ3, σ1, hX])
    (by simp [σ3, σ1, hXh]) (by simp [σ3, σ1, hW]) (by simp [σ3, σ1, hWh]) (by simp [σ3, σ1])
    (by simp [σ3, σ1, h0]; omega)
  refine ⟨hx, hw, _, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (le_refl _)⟩
  · omega
  rw [hσ3, hσ1]
  unfold coefBits
  wst
  all_goals (try simp_all) <;> omega

end Term1

section Term2
variable (cap : ℕ)

/-- The term's second half: the HASH factor, the population's sign, the `2t` factors, the term's end. -/
def termW2 : HW := .seq factorFW (.seq sgnReadW (.seq zsW (emitC sOUT 0 false)))

theorem termW2_spec (Fs : List (List (List ℕ))) (γs : List Bool) (ιs : List ℕ) (pops : List (Bool × List ℕ))
    (G q ℓ p e nE idx : ℕ) (hi : e + q * nE = idx) (hidx : idx < Fs.length) (hp : p < pops.length)
    (hι : ∀ i ∈ ιs, i < pops[p].2.length ∧ i < 2 ^ ℓ) (hG : ∀ gi ∈ pops[p].2, gi ≤ G) (σ : HS)
    (hH : σ.st sHT = htWord Fs) (hHh : σ.sh sHT = 0) (hP : σ.st sPOPS = popsWord pops) (hPh : σ.sh sPOPS = 0)
    (hC : σ.st sCTR = ctrWord γs ιs ℓ) (hCh : σ.sh sCTR = γs.length) (hO : σ.sh sOUT = (σ.st sOUT).length)
    (h1 : σ.val 1 = 4 * q) (h2 : σ.val 2 = G) (h3 : σ.val 3 = 0) (h4 : σ.val 4 = 0) (h5 : σ.val 5 = 0)
    (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0) (h8 : σ.val 8 = 0) (h11 : σ.val 11 = p) (h12 : σ.val 12 = e)
    (h13 : σ.val 13 = q) (h14 : σ.val 14 = nE) (h15 : σ.val 15 = ιs.length) (h16 : σ.val 16 = ℓ)
    (h17 : σ.val 17 = 0) (h18 : σ.val 18 = 0) (h19 : σ.val 19 = 0) (h20 : σ.val 20 = 0) (h21 : σ.val 21 = 0)
    (h22 : σ.val 22 = 0) (h25 : σ.val 25 = 0) (h26 : σ.val 26 = 0) (h27 : σ.val 27 = 0)
    (hcap : σ.val 0 + 1 + (htWord Fs).length + e + q * nE + nE + q + ιs.length * (10 * monoRoom (4 * q) G G + 2) +
      1 + 11 * monoRoom (4 * q) G G + (popsWord pops).length + 2 ^ (ℓ + 1) + p + ℓ + G + ιs.length + 2 ≤ cap) :
    ∃ hH' c, c ≤ factorCost e q nE idx (htWord Fs).length (polyWord Fs[idx]).length +
        p * (9 * (popsWord pops).length + 20 + 4) + 18 * p + 5 * (popsWord pops).length + (18 * ιs.length + 3) + 1 +
        (ιs.length * (zBodyBound q G ℓ p (popsWord pops).length + 4) + 1) + 60 ∧ WExec cap termW2 σ
      ((appendO ((σ.seth sHT hH').seth sCTR (γs.length + ιs.length * ℓ)) sOUT 0
        ([true] ++ polyWord Fs[idx] ++ ιs.flatMap (fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)) ++ [false])).setv 4
          (if pops[p].1 then 1 else 0)) c := by
  have hpw : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hpl : (polyWord Fs[idx]).length ≤ (htWord Fs).length := by
    rw [ht_split Fs idx hidx, entry_single]; simp only [List.length_append]; omega
  obtain ⟨x, s1⟩ := factorFW_spec cap Fs e q nE idx hi hidx σ h12 h13 h14 h22 h26 h27 hO hH hHh (by omega)
  set σ1 := appendO (σ.seth sHT x) sOUT 0 ([true] ++ polyWord Fs[idx]) with hσ1
  obtain ⟨c2, hc2, s2⟩ := sgnReadW_spec cap p pops hp σ1 (by simp [σ1, hP]) (by simp [σ1, hPh]) (by simp [σ1, h4])
    (by simp [σ1, h11]) (by simp [σ1, h17]) (by simp [σ1, h18]) (by simp [σ1, h22]) (by omega)
  set σ2 := σ1.setv 4 (if pops[p].1 then 1 else 0) with hσ2
  have s3 := zsW_spec cap G q ℓ p ιs pops hp hι hG σ2 γs.length
    (fun k hk m hm => by simp [σ2, σ1, hC]; exact ctrWord_field γs ιs ℓ k m hk hm)
    (by simp [σ2, σ1, hCh]) (by simp [σ2, σ1, hP]) (by simp [σ2, σ1, hPh]) (by simp [σ2, σ1, h1])
    (by simp [σ2, σ1, h2]) (by simp [σ2, σ1, h3]) (by simp [σ2]) (by simp [σ2, σ1, h5]) (by simp [σ2, σ1, h6])
    (by simp [σ2, σ1, h7]) (by simp [σ2, σ1, h8]) (by simp [σ2, σ1, h11]) (by simp [σ2, σ1, h15])
    (by simp [σ2, σ1, h16]) (by simp [σ2, σ1, h17]) (by simp [σ2, σ1, h18]) (by simp [σ2, σ1, h19])
    (by simp [σ2, σ1, h20]) (by simp [σ2, σ1, h21]) (by simp [σ2, σ1, h22]) (by simp [σ2, σ1, h25])
    (by simp [σ2, σ1, hO])
    (by simp only [hσ2, hσ1, WState.setv_val, appendO_val, WState.seth_val, Function.update_apply]; simp; omega)
  set σ3 := appendO (σ2.seth sCTR (γs.length + ιs.length * ℓ)) sOUT 0
    (ιs.flatMap fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)) with hσ3
  have hzl : (ιs.flatMap fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)).length ≤
      ιs.length * (10 * monoRoom (4 * q) G G + 2) := by
    rw [List.length_flatMap]
    calc (ιs.map fun i => (zRec G q pops[p].1 (pops[p].2.getD i 0)).length).sum
        ≤ (ιs.map fun _ => 10 * monoRoom (4 * q) G G + 2).sum := by
          refine List.sum_le_sum (fun i hi => ?_)
          have hgi : pops[p].2.getD i 0 ≤ G := by
            rw [List.getD_eq_getElem _ _ (hι i hi).1]; exact hG _ (List.getElem_mem _)
          exact zRec_length_le G q _ _ hgi
      _ = ιs.length * (10 * monoRoom (4 * q) G G + 2) := sum_map_const' _ _
  have v3 : σ3.val 0 = σ.val 0 + ([true] ++ polyWord Fs[idx]).length +
      (ιs.flatMap fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)).length := by
    rw [hσ3, appendO_val, Function.update_self, WState.seth_val, hσ2, WState.setv_val,
      Function.update_of_ne (by decide), hσ1, appendO_val, Function.update_self, WState.seth_val]
  have s4 := emitC_app cap sOUT 0 false σ3 (by simp [σ3, σ2, σ1, hO]; try omega)
    (by rw [v3]; simp only [List.length_append, List.length_singleton]; omega)
  refine ⟨x, _, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (le_refl _)⟩
  · omega
  rw [hσ3, hσ2, hσ1]
  wst
  all_goals (try simp_all) <;> omega

end Term2

end NearCubicWires.WireExponent3_5.PrimT.HbM
