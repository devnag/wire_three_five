import Proof.Wire_3_5.Primitive.SeedFix.HbZs

/-! # C4.Hb, machine part 8: loads, the output's end, the sign and the population's sign (P3:2253-2290)

The term program reads the cell's numbers into registers (`loadU`: C5's `WM.readU`, then `WM.rewind`), walks the
output to its end along `1^{|OUT|}` (`olenWalkW`), computes the coefficient's sign `(−1)^{#{γ_r = 0}}` of a moment
level (`signW`: the parity of the sign pattern's zeros, cleared at the terminal level `λ = J` by PA's `gtFlagW`), and
reads the population's sign `Z^±` (`sgnReadW`).

Paper quantities of the main types: the sign `sgnG γ` of the moment terms (`signW_spec`) and the population's sign
(`sgnReadW_spec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

section Loads
variable {ns nr : ℕ} (cap : ℕ)

/-- Add the unary word `1^v` at the head of `S` to register `r`, then return the head (moves counted in `c`). -/
def loadU (S : Fin (ns + 1)) (c r : Fin nr) : WM ns nr := .seq (WM.readU S c r) (WM.rewind S c)

theorem loadU_spec (S : Fin (ns + 1)) (c r : Fin nr) (hcr : c ≠ r) (v : ℕ) (rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = List.replicate v true ++ rest) (hr0 : rest.getD 0 false = false) (hh : σ.sh S = 0)
    (hc : σ.val c = 0) (hcap : σ.val r + v + 1 ≤ cap) :
    WExec cap (loadU S c r) σ (σ.setv r (σ.val r + v)) (11 * v + 7 + 1 + (5 * (v + 1) + 1)) := by
  have s1 := wreadU_spec cap S c r hcr v σ
    (fun k hk => by
      simp only [hS, hh, Nat.zero_add, readTapeBit]
      rw [List.getD_append _ _ _ _ (by simpa using hk)]; simp [hk])
    (by simp only [hS, hh, Nat.zero_add]; unfold readTapeBit
        rw [List.getD_append_right _ _ _ _ (by simp)]; simpa using hr0)
    (by omega) (by omega)
  have s2 := wrewind_spec cap S c (v + 1) (((σ.seth S (σ.sh S + v + 1)).setv c (σ.val c + v + 1)).setv r (σ.val r + v))
    (by simp [Function.update_apply, hcr, hc]) (by simp [Function.update_apply, hcr, hc]; omega)
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (le_refl _)
  wst
  all_goals (try simp_all) <;> omega

/-- Walk the output's head to its end along `1^{|OUT|}` on `L`. -/
def olenWalkW (L O : Fin (ns + 1)) : WM ns nr := .whs L (.seq (.fwd L) (.fwd O))

theorem olenWalk_loop (L O : Fin (ns + 1)) (hLO : L ≠ O) (m : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.st L = List.replicate m true → σ.sh L = k → σ.sh O = k → k ≤ m →
      WExec cap (olenWalkW L O) σ ((σ.seth L m).seth O m) (5 * (m - k) + 1)
  | k, σ, hL, hLh, hOh, hkm => by
    by_cases hk : k = m
    · subst hk
      have hz : wbit σ L = false := by
        simp only [wbit, hL, hLh, readTapeBit]; simp
      have e : (σ.seth L k).seth O k = σ := by rw [← hLh]; rw [wseth_same]; conv_rhs => rw [← wseth_same σ O]
                                               rw [hOh, hLh]
      rw [e]; exact WExec.mono (WExec.whsF hz) (by omega)
    · have hlt : k < m := by omega
      have hw : wbit σ L = true := by
        simp only [wbit, hL, hLh, readTapeBit]; simp [hlt]
      have s1 := WExec.fwd (cap := cap) L σ
      have s2 := WExec.fwd (cap := cap) O (σ.seth L (σ.sh L + 1))
      have ih := olenWalk_loop L O hLO m (k + 1) ((σ.seth L (σ.sh L + 1)).seth O ((σ.seth L (σ.sh L + 1)).sh O + 1))
        (by simp [hL]) (by simp [Function.update_of_ne hLO, hLh]; try omega)
        (by simp [Function.update_of_ne (Ne.symm hLO), hOh]; try omega)
        (by omega)
      refine WExec.cast cap (WExec.whsT hw (WExec.seq s1 s2) ih) ?_ (by omega)
      wst
      all_goals (try simp_all) <;> omega
  termination_by k => m - k

end Loads

section Sign
variable (cap : ℕ)

/-- The parity of a sign pattern's zeros, as a register value. -/
def parZ (γs : List Bool) : ℕ := γs.count false % 2

theorem parZ_take_succ (γs : List Bool) (k : ℕ) (hk : k < γs.length) :
    parZ (γs.take (k + 1)) = if γs[k] then parZ (γs.take k) else 1 - parZ (γs.take k) := by
  unfold parZ
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.count_append]
  cases γs[k] <;> simp <;> omega

/-- Toggle the flag register `23`. -/
def togW : HW := .ifr 23 (.dec 23) (.inc 23)

/-- One sign bit: toggle on a zero, step on. -/
def parBodyW : HW := .seq (.ifs sCTR .skip togW) (.fwd sCTR)

/-- `gtFlagW`'s registers: `a = 10` (`J`), `b = 9` (`λ`), `f = 28`, scratch `29 30 31`. -/
def gR : Fin 6 ↪ Fin 40 := ⟨![10, 9, 28, 29, 30, 31], by decide⟩

/-- **The coefficient's sign**: the parity of the sign pattern's zeros (register `15` holds `2t`), kept only at a
moment level `λ < J`. -/
def signW : HW :=
  .seq (FinalPass.Hash4.wcopyR 15 25 22) (.seq (.whr 25 (.seq (.dec 25) parBodyW)) (.seq (PrimAsm.UnaryArith.gtFlagW gR)
    (.seq (.ifr 28 .skip (WM.clear 23)) (WM.clear 28))))

theorem signW_spec (γs : List Bool) (lam J : ℕ) (σ : HS)
    (hC : ∀ k < γs.length, readTapeBit (σ.st sCTR) k = γs.getD k false) (hCh : σ.sh sCTR = 0)
    (h9 : σ.val 9 = lam) (h10 : σ.val 10 = J) (h15 : σ.val 15 = γs.length) (h22 : σ.val 22 = 0)
    (h23 : σ.val 23 = 0) (h25 : σ.val 25 = 0) (h28 : σ.val 28 = 0) (h29 : σ.val 29 = 0) (h30 : σ.val 30 = 0)
    (h31 : σ.val 31 = 0) (hcap : γs.length + lam + J + 2 ≤ cap) :
    ∃ c, c ≤ 40 * (γs.length + lam + J) + 60 ∧
      WExec cap signW σ ((σ.seth sCTR γs.length).setv 23 (if lam < J ∧ parZ γs = 1 then 1 else 0)) c := by
  have hpar1 : ∀ l : List Bool, parZ l ≤ 1 := fun l => by unfold parZ; omega
  have s1 := FinalPass.Hash4.wcopyR_spec cap 15 25 22 (by decide) (by decide) (by decide) σ h25 h22
    (by rw [h15]; omega)
  rw [h15] at s1
  let S : ℕ → HS := fun k => ((σ.seth sCTR k).setv 23 (parZ (γs.take k))).setv 25 (γs.length - k)
  have hS0 : S 0 = σ.setv 25 γs.length := by
    simp only [S, List.take_zero]
    wst
    all_goals (try simp_all [parZ]) <;> omega
  have hloop := UnionMachine.Round.wloop cap 25 parBodyW 8 γs.length S (fun k _ => by simp [S]) (by omega)
    (fun k hk => by
      have hb : wbit ((S k).setv 25 (γs.length - k - 1)) sCTR = γs[k] := by
        simp only [wbit, S, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [hC k hk, List.getD_eq_getElem _ _ hk]
      have hts := parZ_take_succ γs k hk
      cases hγ : γs[k]
      · rw [hγ] at hb hts
        have hv := hpar1 (γs.take k)
        have st : WExec cap togW ((S k).setv 25 (γs.length - k - 1))
            (((S k).setv 25 (γs.length - k - 1)).setv 23 (1 - parZ (γs.take k))) 4 := by
          by_cases h0 : parZ (γs.take k) = 0
          · have e : 1 - parZ (γs.take k) = parZ (γs.take k) + 1 := by omega
            rw [e]
            have hz : ((S k).setv 25 (γs.length - k - 1)).val 23 = parZ (γs.take k) := by simp [S]
            refine WExec.mono (WExec.ifrF (by rw [hz, h0]) (WExec.cast cap (WExec.inc 23 _ (by rw [hz]; omega)) ?_
              (le_refl _))) (by omega)
            rw [hz]
          · have e : 1 - parZ (γs.take k) = parZ (γs.take k) - 1 := by omega
            rw [e]
            have hz : ((S k).setv 25 (γs.length - k - 1)).val 23 = parZ (γs.take k) := by simp [S]
            refine WExec.mono (WExec.ifrT (by rw [hz]; exact h0) (WExec.cast cap (WExec.dec 23 _ (by rw [hz]; omega)) ?_
              (le_refl _))) (by omega)
            rw [hz]
        have s := WExec.seq (WExec.ifsF (P := WM.skip) hb st) (WExec.fwd (cap := cap) sCTR _)
        refine WExec.cast cap s ?_ (by omega)
        simp only [S, hts]
        wst
        all_goals (try simp_all) <;> omega
      · rw [hγ] at hb hts
        have s := WExec.seq (WExec.ifsT (Q := togW) hb (WExec.skip _)) (WExec.fwd (cap := cap) sCTR _)
        refine WExec.cast cap s ?_ (by omega)
        simp only [S, hts, if_true]
        wst
        all_goals (try simp_all) <;> omega)
  rw [hS0] at hloop
  set σ2 := S γs.length with hσ2
  have v9 : σ2.val (gR 1) = lam := by simp [σ2, S, gR, h9]
  have v10 : σ2.val (gR 0) = J := by simp [σ2, S, gR, h10]
  have s3 := PrimAsm.UnaryArith.gtFlagW_spec cap gR σ2 (by simp [σ2, S, gR, h28]) (by simp [σ2, S, gR, h29])
    (by simp [σ2, S, gR, h30]) (by simp [σ2, S, gR, h31]) (by rw [v10]; omega) (by rw [v9]; omega) (by omega)
  rw [v9, v10] at s3
  have hg2 : (gR 2 : Fin 40) = 28 := rfl
  rw [hg2] at s3
  set σ3 := σ2.setv 28 (if lam < J then 1 else 0) with hσ3
  have v23 : σ3.val 23 = parZ γs := by simp [σ3, σ2, S]
  by_cases hlt : lam < J
  · have s4 : WExec cap (.ifr 28 .skip (WM.clear 23)) σ3 σ3 1 := WExec.ifrT (by simp [σ3, hlt]) (WExec.skip _)
    have s5 := wclear_spec cap 28 1 σ3 (by simp [σ3, hlt]) (by simp [σ3, hlt]; omega)
    refine ⟨_, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq hloop (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (le_refl _)⟩
    · have := hpar1 γs; omega
    rw [hσ3, hσ2]
    simp only [S, List.take_length, Nat.sub_self, hlt, true_and]
    have hp1 := hpar1 γs
    wst
    all_goals (try simp_all) <;> (try split_ifs) <;> omega
  · have s4 := WExec.ifrF (r := 28) (P := WM.skip) (σ := σ3) (by simp only [hσ3, WState.setv_val, Function.update_apply]; simp [hlt])
      (wclear_spec cap 23 (parZ γs) σ3 v23 (by rw [v23]; have := hpar1 γs; omega))
    have s5 := wclear_spec cap 28 0 (σ3.setv 23 0)
      (by simp only [hσ3, WState.setv_val, Function.update_apply]; simp [hlt])
      (by simp only [hσ3, WState.setv_val, Function.update_apply]; simp [hlt])
    refine ⟨_, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq hloop (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (le_refl _)⟩
    · have := hpar1 γs; omega
    rw [hσ3, hσ2]
    simp only [S, List.take_length, Nat.sub_self, hlt, false_and, if_false]
    wst
    all_goals (try simp_all) <;> omega

end Sign

section SgnRead
variable (cap : ℕ)

/-- **The population's sign** into register `4`: walk to record `p`, read its sign bit, return the stream. -/
def sgnReadW : HW :=
  .seq (FinalPass.Hash4.wcopyR 11 18 22) (.seq (skipPopsC sPOPS 17 18) (.seq (WM.fwdC sPOPS 17)
    (.seq (.ifs sPOPS (.inc 4) .skip) (WM.rewind sPOPS 17))))

theorem sgnReadW_spec (p : ℕ) (pops : List (Bool × List ℕ)) (hp : p < pops.length) (σ : HS)
    (hP : σ.st sPOPS = popsWord pops) (hPh : σ.sh sPOPS = 0) (h4 : σ.val 4 = 0) (h11 : σ.val 11 = p)
    (h17 : σ.val 17 = 0) (h18 : σ.val 18 = 0) (h22 : σ.val 22 = 0) (hcap : (popsWord pops).length + p + 2 ≤ cap) :
    ∃ c, c ≤ p * (9 * (popsWord pops).length + 20 + 4) + 18 * p + 5 * (popsWord pops).length + 40 ∧
      WExec cap sgnReadW σ (σ.setv 4 (if pops[p].1 then 1 else 0)) c := by
  have hpw := popsWord_split pops p hp
  have hlen : (popsPre pops p).length + 2 ≤ (popsWord pops).length := by
    rw [hpw]; simp [popRec]
    try omega
  have s1 := FinalPass.Hash4.wcopyR_spec cap 11 18 22 (by decide) (by decide) (by decide) σ h18 h22
    (by rw [h11]; omega)
  rw [h11] at s1
  have s2 := skipPopsC_spec cap sPOPS 17 18 (by decide) pops p hp.le (σ.setv 18 p) (by simp [hP]) (by simp [hPh])
    (by simp) (by simp [h17]; omega) (by omega)
  set σ2 := (((σ.setv 18 p).seth sPOPS (popsPre pops p).length).setv 17 ((σ.setv 18 p).val 17 +
    (popsPre pops p).length)).setv 18 0 with hσ2
  have s3 := wfwdC_spec cap sPOPS 17 σ2 (by simp [σ2, h17]; omega)
  set σ3 := (σ2.seth sPOPS (σ2.sh sPOPS + 1)).setv 17 (σ2.val 17 + 1) with hσ3
  have hb : wbit σ3 sPOPS = pops[p].1 := by
    simp only [wbit, σ3, σ2, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hP,
      hpw]
    unfold readTapeBit
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [popRec]
  have v3c : σ3.val 17 = (popsPre pops p).length + 1 := by simp [σ3, σ2, h17]
  have v3h : σ3.sh sPOPS = (popsPre pops p).length + 1 := by simp [σ3, σ2]
  cases hs : pops[p].1
  · rw [hs] at hb
    have s4 := WExec.ifsF (cap := cap) (P := WM.inc 4) hb (WExec.skip σ3)
    have s5 := wrewind_spec cap sPOPS 17 ((popsPre pops p).length + 1) σ3 v3c (by rw [v3c]; omega)
    refine ⟨_, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (le_refl _)⟩
    · omega
    rw [hσ3, hσ2]
    wst
    all_goals (try simp_all) <;> omega
  · rw [hs] at hb
    have s4 := WExec.ifsT (cap := cap) (Q := WM.skip) hb (WExec.inc (cap := cap) 4 σ3 (by simp [σ3, σ2, h4]; omega))
    have s5 := wrewind_spec cap sPOPS 17 ((popsPre pops p).length + 1) (σ3.setv 4 (σ3.val 4 + 1))
      (by simp [v3c]) (by simp [v3c]; omega)
    refine ⟨_, ?_, WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (le_refl _)⟩
    · omega
    rw [hσ3, hσ2]
    wst
    all_goals (try simp_all) <;> omega

end SgnRead

end NearCubicWires.WireExponent3_5.PrimT.HbM
