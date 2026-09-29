import Proof.Wire_3_5.Primitive.SeedFix.HbWM2

/-! # C4.Hb, machine part 10: the term cell (`filt:soft`, P3:2253-2290)

"After fixing `p`, Gaussian elimination finds its conditional probability" (P3:2268-2269): once the elimination has
left the cell's count exponent on `XE` and its consistency flag on `GF`, the term cell prints the cell's term
`(W·2^x·(±1), F_{q,e} :: [Z_{ι_r}]_r)` when the cell is valid (`VAL`) and consistent (`GF`), and extends the output's
length ruler `OLEN`. The program loads its registers from the unary counters and rulers (`loadsW`), and clears every
register at the end (`clearsW`), so that it runs again at the next cell (`wm_mask`).

Paper quantity of the main type (**`tcellW_spec`**): the term word `termBits` of the cell's printed term. -/

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

section Regs
variable {ns nr : ℕ} (cap : ℕ)

/-- **Loads**: add the unary word at the head of each listed stream to its register (moves counted in `c`). -/
def loadsW (c : Fin nr) : List (Fin (ns + 1) × Fin nr) → WM ns nr
  | [] => .skip
  | x :: ls => .seq (loadU x.1 c x.2) (loadsW c ls)

/-- The value the loads add to register `r`. -/
def ldv (vs : Fin (ns + 1) → ℕ) (ls : List (Fin (ns + 1) × Fin nr)) (r : Fin nr) : ℕ :=
  ((ls.filter fun x => x.2 = r).map fun x => vs x.1).sum

/-- The loads' cost. -/
def ldCost (vs : Fin (ns + 1) → ℕ) : List (Fin (ns + 1) × Fin nr) → ℕ
  | [] => 0
  | x :: ls => (11 * vs x.1 + 7 + 1 + (5 * (vs x.1 + 1) + 1)) + 1 + ldCost vs ls

theorem ldv_cons (vs : Fin (ns + 1) → ℕ) (x : Fin (ns + 1) × Fin nr) (ls : List (Fin (ns + 1) × Fin nr)) (r : Fin nr) :
    ldv vs (x :: ls) r = (if x.2 = r then vs x.1 else 0) + ldv vs ls r := by
  unfold ldv
  by_cases h : x.2 = r
  · simp [List.filter_cons, h]
  · simp [List.filter_cons, h]

theorem loadsW_spec (c : Fin nr) (vs : Fin (ns + 1) → ℕ) (rs : Fin (ns + 1) → List Bool) :
    ∀ (ls : List (Fin (ns + 1) × Fin nr)) (σ : WState ns nr), (∀ x ∈ ls, x.2 ≠ c) → σ.val c = 0 →
      (∀ x ∈ ls, σ.st x.1 = List.replicate (vs x.1) true ++ rs x.1 ∧ (rs x.1).getD 0 false = false ∧ σ.sh x.1 = 0) →
      (∀ r, σ.val r + ldv vs ls r + 1 ≤ cap) →
      WExec cap (loadsW c ls) σ ⟨σ.sh, σ.st, fun r => σ.val r + ldv vs ls r, σ.cell⟩ (ldCost vs ls)
  | [], σ, _, _, _, _ => by
    have e : (⟨σ.sh, σ.st, fun r => σ.val r + ldv vs [] r, σ.cell⟩ : WState ns nr) = σ := by
      cases σ; simp [ldv]
    rw [e]; exact WExec.skip σ
  | x :: ls, σ, hc, h0, hS, hcap => by
    obtain ⟨hs, hr, hh⟩ := hS x List.mem_cons_self
    have hxc : x.2 ≠ c := hc x List.mem_cons_self
    have hx := hcap x.2
    rw [ldv_cons, if_pos rfl] at hx
    have s1 := loadU_spec cap x.1 c x.2 (Ne.symm hxc) (vs x.1) (rs x.1) σ hs hr hh h0 (by omega)
    have ih := loadsW_spec c vs rs ls (σ.setv x.2 (σ.val x.2 + vs x.1))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
      (by simp only [WState.setv_val]; rw [Function.update_of_ne (Ne.symm hxc)]; exact h0)
      (fun y hy => by simpa using hS y (List.mem_cons_of_mem _ hy))
      (fun r => by
        have := hcap r
        rw [ldv_cons] at this
        simp only [WState.setv_val, Function.update_apply]
        by_cases h : r = x.2
        · subst h; rw [if_pos rfl] at this ⊢; omega
        · rw [if_neg (Ne.symm h)] at this; rw [if_neg h]; omega)
    refine WExec.cast cap (WExec.seq s1 ih) ?_ (by simp only [ldCost]; omega)
    apply WState.eq
    · rfl
    · rfl
    · funext r
      simp only [WState.setv_val, Function.update_apply, ldv_cons]
      by_cases h : r = x.2
      · subst h; simp; omega
      · rw [if_neg h, if_neg (Ne.symm h)]; omega
    · rfl

/-- **Clears**: every listed register back to `0`. -/
def clearsW : List (Fin nr) → WM ns nr
  | [] => .skip
  | r :: rs => .seq (WM.clear r) (clearsW rs)

/-- The clears' cost. -/
def clCost (v : Fin nr → ℕ) : List (Fin nr) → ℕ
  | [] => 0
  | r :: rs => (3 * v r + 1) + 1 + clCost v rs

theorem clCost_congr (v v' : Fin nr → ℕ) :
    ∀ (rs : List (Fin nr)), (∀ r ∈ rs, v r = v' r) → clCost v rs = clCost v' rs
  | [], _ => rfl
  | r :: rs, h => by
    simp only [clCost]
    rw [h r List.mem_cons_self, clCost_congr v v' rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]

theorem clCost_le (v : Fin nr → ℕ) (B : ℕ) (hv : ∀ r, v r ≤ B) :
    ∀ (rs : List (Fin nr)), clCost v rs ≤ rs.length * (3 * B + 2)
  | [] => by simp [clCost]
  | r :: rs => by
    have h1 := clCost_le v B hv rs
    have h2 := hv r
    show (3 * v r + 1) + 1 + clCost v rs ≤ (rs.length + 1) * (3 * B + 2)
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem clearsW_spec : ∀ (rs : List (Fin nr)) (σ : WState ns nr), rs.Nodup → (∀ r, σ.val r ≤ cap) →
    WExec cap (clearsW rs) σ ⟨σ.sh, σ.st, fun r => if r ∈ rs then 0 else σ.val r, σ.cell⟩ (clCost σ.val rs)
  | [], σ, _, _ => by
    have e : (⟨σ.sh, σ.st, fun r => if r ∈ ([] : List (Fin nr)) then 0 else σ.val r, σ.cell⟩ : WState ns nr) = σ := by
      cases σ; simp
    rw [e]; exact WExec.skip σ
  | r :: rs, σ, hnd, hcap => by
    have hnd' := List.nodup_cons.mp hnd
    have s1 := wclear_spec cap r (σ.val r) σ rfl (hcap r)
    have ih := clearsW_spec rs (σ.setv r 0) hnd'.2 (fun r' => by
      simp only [WState.setv_val, Function.update_apply]; split_ifs <;> simp [hcap])
    have hc : clCost (σ.setv r 0).val rs = clCost σ.val rs :=
      clCost_congr _ _ rs (fun r' hr' => by
        have : r' ≠ r := fun h => hnd'.1 (h ▸ hr')
        simp [Function.update_of_ne this])
    refine WExec.cast cap (WExec.seq s1 ih) ?_ (by rw [hc]; simp only [clCost]; omega)
    apply WState.eq
    · rfl
    · rfl
    · funext r'
      simp only [WState.setv_val, Function.update_apply, List.mem_cons]
      by_cases h1 : r' = r
      · subst h1; simp
      · simp [h1]
    · rfl

end Regs

section OlenUpd
variable (cap : ℕ)

theorem write_rep_true (n : ℕ) : writeTapeBit (List.replicate n true) n true = List.replicate (n + 1) true := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, writeTapeBit, ih]

/-- **The output's length ruler**: `r₀` more ones at the head of `OLEN`. -/
def olenUpdW : HW := .whr 0 (.seq (.dec 0) (.seq (.wr sOLEN true) (.fwd sOLEN)))

theorem olenUpd_spec (m : ℕ) (σ : HS) (hL : σ.st sOLEN = List.replicate (σ.sh sOLEN) true) (h0 : σ.val 0 = m)
    (hcap : m ≤ cap) :
    WExec cap olenUpdW σ (((σ.sets sOLEN (List.replicate (σ.sh sOLEN + m) true)).seth sOLEN (σ.sh sOLEN + m)).setv 0 0)
      (m * (3 + 4) + 1) := by
  set h := σ.sh sOLEN with hh
  let S : ℕ → HS := fun k => ((σ.sets sOLEN (List.replicate (h + k) true)).seth sOLEN (h + k)).setv 0 (m - k)
  have hS0 : S 0 = σ := by
    simp only [S, Nat.add_zero, Nat.sub_zero]
    apply WState.eq
    · funext j; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs with hj
      · subst hj; rfl
      · rfl
    · funext j; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs with hj
      · subst hj; exact hL.symm
      · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs with hj
      · subst hj; exact h0.symm
      · rfl
    · rfl
  have hloop := UnionMachine.Round.wloop cap 0 (.seq (.wr sOLEN true) (.fwd sOLEN)) 3 m S
    (fun k _ => by simp [S]) hcap
    (fun k hk => by
      have s1 := WExec.wr (cap := cap) sOLEN true ((S k).setv 0 (m - k - 1))
      have s2 := WExec.fwd (cap := cap) sOLEN (((S k).setv 0 (m - k - 1)).sets sOLEN
        (writeTapeBit (((S k).setv 0 (m - k - 1)).st sOLEN) (((S k).setv 0 (m - k - 1)).sh sOLEN) true))
      refine WExec.cast cap (WExec.seq s1 s2) ?_ (le_refl _)
      simp only [S, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh,
        Function.update_self, write_rep_true]
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
        split_ifs <;> omega
      · funext j; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
        split_ifs <;> first | rfl | (congr 1)
      · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
        split_ifs <;> first | rfl | omega
      · rfl)
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ (le_refl _)
  simp only [S, Nat.sub_self]

end OlenUpd

section Term
variable (cap : ℕ)

/-- **The cell's term program**: the two halves. -/
def termW : HW := .seq termW1 termW2

/-- **The cell's term word**: the term marker, the coefficient word, the HASH factor's record, the `2t` factor records,
the term's end. -/
def termBits (sgn : Bool) (x : ℕ) (w : List Bool) (F : List (List ℕ)) (zs : List Bool) : List Bool :=
  [true] ++ coefBits sgn x w ++ ([true] ++ polyWord F ++ zs ++ [false])

theorem frame_le_wt (Ws : List (List Bool)) (lam : ℕ) (hlam : lam < Ws.length) :
    (frame Ws[lam]).length ≤ (wtWord Ws).length := by
  rw [wt_split Ws lam hlam]; simp only [List.length_append]; omega

theorem coefBits_length (s : Bool) (x : ℕ) (w : List Bool) :
    (coefBits s x w).length = 2 + 2 * x + (frame w).length := by
  simp only [coefBits, List.length_append, reps_length, List.length_cons, List.length_nil]; omega

theorem termW_spec (Fs : List (List (List ℕ))) (γs : List Bool) (ιs : List ℕ) (pops : List (Bool × List ℕ))
    (Ws : List (List Bool)) (G q ℓ p e nE idx lam J x : ℕ) (xs : List Bool)
    (hi : e + q * nE = idx) (hidx : idx < Fs.length) (hp : p < pops.length) (hlam : lam < Ws.length)
    (hγι : γs.length = ιs.length)
    (hι : ∀ i ∈ ιs, i < pops[p].2.length ∧ i < 2 ^ ℓ) (hG : ∀ gi ∈ pops[p].2, gi ≤ G) (σ : HS)
    (hOL : σ.st sOLEN = List.replicate (σ.st sOUT).length true) (hOLh : σ.sh sOLEN = 0) (hOh : σ.sh sOUT = 0)
    (hC : σ.st sCTR = ctrWord γs ιs ℓ) (hCh : σ.sh sCTR = 0)
    (hX : σ.st sXE = List.replicate x true ++ false :: xs) (hXh : σ.sh sXE = 0)
    (hW : σ.st sWT = wtWord Ws) (hWh : σ.sh sWT = 0)
    (hH : σ.st sHT = htWord Fs) (hHh : σ.sh sHT = 0) (hP : σ.st sPOPS = popsWord pops) (hPh : σ.sh sPOPS = 0)
    (h0 : σ.val 0 = 0) (h1 : σ.val 1 = 4 * q) (h2 : σ.val 2 = G) (h3 : σ.val 3 = 0) (h4 : σ.val 4 = 0)
    (h5 : σ.val 5 = 0) (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0) (h8 : σ.val 8 = 0) (h9 : σ.val 9 = lam)
    (h10 : σ.val 10 = J) (h11 : σ.val 11 = p) (h12 : σ.val 12 = e) (h13 : σ.val 13 = q) (h14 : σ.val 14 = nE)
    (h15 : σ.val 15 = γs.length) (h16 : σ.val 16 = ℓ) (h17 : σ.val 17 = 0) (h18 : σ.val 18 = 0)
    (h19 : σ.val 19 = 0) (h20 : σ.val 20 = 0) (h21 : σ.val 21 = 0) (h22 : σ.val 22 = 0) (h23 : σ.val 23 = 0)
    (h25 : σ.val 25 = 0) (h26 : σ.val 26 = 0) (h27 : σ.val 27 = 0) (h28 : σ.val 28 = 0) (h29 : σ.val 29 = 0)
    (h30 : σ.val 30 = 0) (h31 : σ.val 31 = 0)
    (hcap1 : γs.length + lam + J + 5 + 2 * x + (wtWord Ws).length ≤ cap)
    (hcap2 : 3 + 2 * x + (wtWord Ws).length + 1 + (htWord Fs).length + e + q * nE + nE + q +
      ιs.length * (10 * monoRoom (4 * q) G G + 2) + 1 + 11 * monoRoom (4 * q) G G + (popsWord pops).length +
      2 ^ (ℓ + 1) + p + ℓ + G + ιs.length + 2 ≤ cap) :
    ∃ τ c, c ≤ (5 * (σ.st sOUT).length + 80 + 40 * (γs.length + lam + J) +
        coefCost x lam (wtWord Ws).length (frame Ws[lam]).length) + 1 +
        (factorCost e q nE idx (htWord Fs).length (polyWord Fs[idx]).length +
        p * (9 * (popsWord pops).length + 20 + 4) + 18 * p + 5 * (popsWord pops).length + (18 * ιs.length + 3) + 1 +
        (ιs.length * (zBodyBound q G ℓ p (popsWord pops).length + 4) + 1) + 60) ∧ WExec cap termW σ τ c ∧
      τ.st = Function.update σ.st sOUT (σ.st sOUT ++ termBits (lam < J ∧ parZ γs = 1) x Ws[lam] Fs[idx]
        (ιs.flatMap fun i => HbM.zRec G q pops[p].1 (pops[p].2.getD i 0))) ∧
      τ.sh sOLEN = (σ.st sOUT).length ∧
      τ.val = Function.update (Function.update (Function.update σ.val 23 (if lam < J ∧ parZ γs = 1 then 1 else 0)) 4
        (if pops[p].1 then 1 else 0)) 0 (termBits (lam < J ∧ parZ γs = 1) x Ws[lam] Fs[idx]
        (ιs.flatMap fun i => HbM.zRec G q pops[p].1 (pops[p].2.getD i 0))).length ∧ τ.cell = σ.cell := by
  obtain ⟨hx, hw, c1, hc1, s1⟩ := termW1_spec cap γs ιs ℓ lam J x xs Ws hlam σ hOL hOLh hOh hC hCh hX hXh hW hWh h0 h9
    h10 h15 h18 h22 h23 h25 h28 h29 h30 h31 hcap1
  set b1 := [true] ++ coefBits (lam < J ∧ parZ γs = 1) x Ws[lam] with hb1
  set σ1 := appendO ((((((σ.seth sOLEN (σ.st sOUT).length).seth sOUT (σ.st sOUT).length).seth sCTR γs.length).setv 23
        (if lam < J ∧ parZ γs = 1 then 1 else 0)).seth sXE hx).seth sWT hw) sOUT 0 b1 with hσ1
  have hfl := frame_le_wt Ws lam hlam
  have hl1 : b1.length = 3 + 2 * x + (frame Ws[lam]).length := by
    rw [hb1, List.length_append, coefBits_length]; simp; omega
  have v0 : σ1.val 0 = b1.length := by simp [σ1, h0]
  obtain ⟨hH', c2, hc2, s2⟩ := termW2_spec cap Fs γs ιs pops G q ℓ p e nE idx hi hidx hp hι hG σ1
    (by simp [σ1, hH]) (by simp [σ1, hHh]) (by simp [σ1, hP]) (by simp [σ1, hPh]) (by simp [σ1, hC])
    (by simp [σ1]) (by simp [σ1]) (by simp [σ1, h1]) (by simp [σ1, h2]) (by simp [σ1, h3]) (by simp [σ1, h4])
    (by simp [σ1, h5]) (by simp [σ1, h6]) (by simp [σ1, h7]) (by simp [σ1, h8]) (by simp [σ1, h11])
    (by simp [σ1, h12]) (by simp [σ1, h13]) (by simp [σ1, h14]) (by simp [σ1, h15, hγι]) (by simp [σ1, h16])
    (by simp [σ1, h17]) (by simp [σ1, h18]) (by simp [σ1, h19]) (by simp [σ1, h20]) (by simp [σ1, h21])
    (by simp [σ1, h22]) (by simp [σ1, h25]) (by simp [σ1, h26]) (by simp [σ1, h27])
    (by rw [v0, hl1]; omega)
  refine ⟨_, _, ?_, WExec.seq s1 s2, ?_, ?_, ?_, ?_⟩
  · omega
  · funext j
    simp only [σ1, appendO_st, WState.setv_st, WState.seth_st, Function.update_apply, termBits, hb1]
    split_ifs <;> simp [List.append_assoc]
  · simp [σ1, Function.update_apply]
  · funext j
    simp only [σ1, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply, termBits, hb1]
    split_ifs <;> subst_vars <;> simp_all <;> omega
  · simp [σ1]

end Term

section Cell
variable (cap : ℕ)

/-- A unary counter of range `R`: the value `v < R` as `1^v 0^{R-1-v}`. -/
def unary (v R : ℕ) : List Bool := List.replicate v true ++ List.replicate (R - 1 - v) false

theorem ldv_le_sum {ns nr : ℕ} (vs : Fin (ns + 1) → ℕ) :
    ∀ (ls : List (Fin (ns + 1) × Fin nr)) (r : Fin nr), ldv vs ls r ≤ (ls.map fun x => vs x.1).sum
  | [], _ => by simp [ldv]
  | x :: ls, r => by
    rw [ldv_cons, List.map_cons, List.sum_cons]
    have := ldv_le_sum vs ls r
    split_ifs <;> omega

theorem ldCost_le {ns nr : ℕ} (vs : Fin (ns + 1) → ℕ) (B : ℕ) :
    ∀ (ls : List (Fin (ns + 1) × Fin nr)), (∀ x ∈ ls, vs x.1 ≤ B) → ldCost vs ls ≤ ls.length * (16 * B + 15)
  | [], _ => by simp [ldCost]
  | x :: ls, h => by
    have h1 := ldCost_le vs B ls (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have h2 := h x List.mem_cons_self
    show (11 * vs x.1 + 7 + 1 + (5 * (vs x.1 + 1) + 1)) + 1 + ldCost vs ls ≤ (ls.length + 1) * (16 * B + 15)
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- The term cell's loads: `4q`, `G`, `λ`, `J`, `p`, `e`, `q`, `nE − 1`, `2t`, `ℓ₀`. -/
def ldT : List (Fin 24 × Fin 40) :=
  [(sQC, 1), (sQC, 1), (sQC, 1), (sQC, 1), (sGG, 2), (sLAM, 9), (sJJ, 10), (sPC, 11), (sEC, 12), (sQC, 13), (sEE, 14),
    (sTT, 15), (sLL, 16)]

/-- **The term cell**: the loads, then (valid and consistent) the term and the length ruler, then the clears. -/
def tcellW : HW :=
  .seq (loadsW 26 ldT) (.seq (.inc 14) (.seq (.ifs sVAL (.ifs sGF (.seq termW olenUpdW) .skip) .skip)
    (clearsW (List.finRange 40))))

/-- The term program's cost bound. -/
def termBound (Fs : List (List (List ℕ))) (pops : List (Bool × List ℕ)) (Ws : List (List Bool))
    (O T2 lam J x e q nE idx p G ℓ : ℕ) : ℕ :=
  (5 * O + 80 + 40 * (T2 + lam + J) + coefCost x lam (wtWord Ws).length (frame (Ws.getD lam [])).length) + 1 +
    (factorCost e q nE idx (htWord Fs).length (polyWord (Fs.getD idx [])).length +
    p * (9 * (popsWord pops).length + 20 + 4) + 18 * p + 5 * (popsWord pops).length + (18 * T2 + 3) + 1 +
    (T2 * (zBodyBound q G ℓ p (popsWord pops).length + 4) + 1) + 60)

/-- The loaded values' sum. -/
def ldSum (q G lam J p e nE T2 ℓ : ℕ) : ℕ := 4 * q + G + lam + J + p + e + q + nE + T2 + ℓ

theorem tcellW_spec (Fs : List (List (List ℕ))) (γs : List Bool) (ιs : List ℕ) (pops : List (Bool × List ℕ))
    (Ws : List (List Bool)) (G q ℓ p e nE N2 idx lam J T2 x : ℕ) (xs : List Bool) (v g : Bool)
    (hnE : 1 ≤ nE) (hi : e + q * nE = idx) (hidx : idx < Fs.length) (hp : p < pops.length) (hlam : lam < Ws.length)
    (hlJ : lam ≤ J) (hγ : γs.length = T2) (hιl : ιs.length = T2)
    (hι : v = true → ∀ i ∈ ιs, i < pops[p].2.length) (hι2 : ∀ i ∈ ιs, i < 2 ^ ℓ) (hG : ∀ gi ∈ pops[p].2, gi ≤ G)
    (σ : HS) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0)
    (hOL : σ.st sOLEN = List.replicate (σ.st sOUT).length true)
    (hH : σ.st sHT = htWord Fs) (hP : σ.st sPOPS = popsWord pops) (hW : σ.st sWT = wtWord Ws)
    (hC : σ.st sCTR = ctrWord γs ιs ℓ) (hLAM : σ.st sLAM = unary lam (J + 1)) (hPC : σ.st sPC = unary p pops.length)
    (hEC : σ.st sEC = unary e nE) (hQC : σ.st sQC = unary q N2) (hJJ : σ.st sJJ = List.replicate J true)
    (hGG : σ.st sGG = List.replicate G true) (hEE : σ.st sEE = List.replicate (nE - 1) true)
    (hTT : σ.st sTT = List.replicate T2 true) (hLL : σ.st sLL = List.replicate ℓ true)
    (hX : σ.st sXE = List.replicate x true ++ false :: xs) (hVAL : σ.st sVAL = [v]) (hGF : σ.st sGF = [g])
    (hcapS : ldSum q G lam J p e nE T2 ℓ + 2 ≤ cap)
    (hcap1 : T2 + lam + J + 5 + 2 * x + (wtWord Ws).length ≤ cap)
    (hcap2 : 3 + 2 * x + (wtWord Ws).length + 1 + (htWord Fs).length + e + q * nE + nE + q +
      T2 * (10 * monoRoom (4 * q) G G + 2) + 1 + 11 * monoRoom (4 * q) G G + (popsWord pops).length +
      2 ^ (ℓ + 1) + p + ℓ + G + T2 + 2 ≤ cap)
    (hcap3 : (termBits (lam < J ∧ parZ γs = 1) x Ws[lam] Fs[idx]
        (ιs.flatMap fun i => HbM.zRec G q pops[p].1 (pops[p].2.getD i 0))).length ≤ cap) :
    ∃ τ c, c ≤ 13 * (16 * ldSum q G lam J p e nE T2 ℓ + 15) + 5 + 1 + (2 + (termBound Fs pops Ws (σ.st sOUT).length T2
        lam J x e q nE idx p G ℓ + 1 + ((termBits (lam < J ∧ parZ γs = 1) x Ws[lam] Fs[idx]
        (ιs.flatMap fun i => HbM.zRec G q pops[p].1 (pops[p].2.getD i 0))).length * 7 + 1))) + 1 +
        40 * (3 * (ldSum q G lam J p e nE T2 ℓ + 1) + 2) ∧
      WExec cap tcellW σ τ c ∧
      τ.st = Function.update (Function.update σ.st sOUT (σ.st sOUT ++
        (if v = true ∧ g = true then termBits (lam < J ∧ parZ γs = 1) x Ws[lam] Fs[idx]
          (ιs.flatMap fun i => HbM.zRec G q pops[p].1 (pops[p].2.getD i 0)) else [])))
        sOLEN (List.replicate ((σ.st sOUT).length + (if v = true ∧ g = true then termBits (lam < J ∧ parZ γs = 1) x
          Ws[lam] Fs[idx] (ιs.flatMap fun i => HbM.zRec G q pops[p].1 (pops[p].2.getD i 0)) else []).length) true) ∧
      τ.val = (fun _ => 0) ∧ τ.cell = σ.cell := by
  set tb := termBits (lam < J ∧ parZ γs = 1) x Ws[lam] Fs[idx]
    (ιs.flatMap fun i => HbM.zRec G q pops[p].1 (pops[p].2.getD i 0)) with htb
  set S := ldSum q G lam J p e nE T2 ℓ with hS
  -- the loads
  let vs : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 0, lam, p, e, q, 0, 0, 0, 0, 0, T2, ℓ, J, G, 0, nE - 1, 0, 0, 0]
  let rs : Fin 24 → List Bool := ![[], [], [], [], [], [], List.replicate (J + 1 - 1 - lam) false,
    List.replicate (pops.length - 1 - p) false, List.replicate (nE - 1 - e) false, List.replicate (N2 - 1 - q) false,
    [], [], [], [], [], [], [], [], [], [], [], [], [], []]
  have gz : ∀ n : ℕ, (List.replicate n false).getD 0 false = false := fun n => by cases n <;> rfl
  have hmem : ∀ y ∈ ldT, σ.st y.1 = List.replicate (vs y.1) true ++ rs y.1 ∧ (rs y.1).getD 0 false = false ∧
      σ.sh y.1 = 0 := by
    intro y hy
    simp only [ldT, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by rw [hQC]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hQC]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hQC]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hQC]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hGG]; exact (List.append_nil _).symm, rfl, hsh _⟩
    · exact ⟨by rw [hLAM]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hJJ]; exact (List.append_nil _).symm, rfl, hsh _⟩
    · exact ⟨by rw [hPC]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hEC]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hQC]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hEE]; exact (List.append_nil _).symm, rfl, hsh _⟩
    · exact ⟨by rw [hTT]; exact (List.append_nil _).symm, rfl, hsh _⟩
    · exact ⟨by rw [hLL]; exact (List.append_nil _).symm, rfl, hsh _⟩
  have hsum : (ldT.map fun y => vs y.1).sum ≤ S := by
    have e : (ldT.map fun y => vs y.1).sum = q + (q + (q + (q + (G + (lam + (J + (p + (e + (q + ((nE - 1) +
        (T2 + (ℓ + 0)))))))))))) := rfl
    rw [e, hS]; unfold ldSum; omega
  have s1 := loadsW_spec cap 26 vs rs ldT σ (by decide) (hv 26) hmem
    (fun r => by have := (ldv_le_sum vs ldT r).trans hsum; rw [hv r]; omega)
  have hlc : ldCost vs ldT ≤ 13 * (16 * S + 15) := by
    have hb : ∀ y ∈ ldT, vs y.1 ≤ S := by
      intro y hy
      simp only [ldT, List.mem_cons, List.mem_nil_iff, or_false] at hy
      have hS' : S = 4 * q + G + lam + J + p + e + q + nE + T2 + ℓ := rfl
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show q ≤ S; omega
      · show q ≤ S; omega
      · show q ≤ S; omega
      · show q ≤ S; omega
      · show G ≤ S; omega
      · show lam ≤ S; omega
      · show J ≤ S; omega
      · show p ≤ S; omega
      · show e ≤ S; omega
      · show q ≤ S; omega
      · show nE - 1 ≤ S; omega
      · show T2 ≤ S; omega
      · show ℓ ≤ S; omega
    have := ldCost_le vs S ldT hb
    have hl : ldT.length = 13 := rfl
    rw [hl] at this
    exact this
  set σ1 : HS := ⟨σ.sh, σ.st, fun r => σ.val r + ldv vs ldT r, σ.cell⟩ with hσ1
  have e1 : ∀ r, σ1.val r = ldv vs ldT r := fun r => by simp [σ1, hv]
  have hv1 : ∀ r, σ1.val r ≤ S := fun r => by rw [e1]; exact (ldv_le_sum vs ldT r).trans hsum
  have s2 := WExec.inc (cap := cap) 14 σ1 (by have := hv1 14; omega)
  set σ2 := σ1.setv 14 (σ1.val 14 + 1) with hσ2
  have v14 : σ1.val 14 = nE - 1 := by rw [e1]; rfl
  have hr : ∀ r : Fin 40, σ2.val r = if r = 14 then nE else ldv vs ldT r := by
    intro r
    simp only [σ2, WState.setv_val, Function.update_apply]
    split_ifs with h
    · rw [v14]; omega
    · exact e1 r
  have hv2 : ∀ r, σ2.val r ≤ S + 1 := fun r => by
    simp only [σ2, WState.setv_val, Function.update_apply]
    have := hv1 r; have := hv1 14
    split_ifs <;> omega
  have r1 : σ2.val 1 = 4 * q := by rw [hr]; show q + (q + (q + (q + 0))) = 4 * q; omega
  by_cases hvg : v = true ∧ g = true
  · obtain ⟨rfl, rfl⟩ := hvg
    have hlam' : lam < J + 1 := by omega
    obtain ⟨τ, c3, hc3, s3, hst3, hsh3, hval3, hcell3⟩ := termW_spec cap Fs γs ιs pops Ws G q ℓ p e nE idx lam J x xs
      hi hidx hp hlam (by rw [hγ, hιl]) (fun i hi' => ⟨hι rfl i hi', hι2 i hi'⟩) hG σ2
      (by simp [σ2, σ1, hOL]) (by simp [σ2, σ1, hsh]) (by simp [σ2, σ1, hsh]) (by simp [σ2, σ1, hC])
      (by simp [σ2, σ1, hsh]) (by simp [σ2, σ1, hX]) (by simp [σ2, σ1, hsh]) (by simp [σ2, σ1, hW])
      (by simp [σ2, σ1, hsh]) (by simp [σ2, σ1, hH]) (by simp [σ2, σ1, hsh]) (by simp [σ2, σ1, hP])
      (by simp [σ2, σ1, hsh])
      (by rw [hr]; rfl) r1 (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl)
      (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl)
      (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl)
      (by rw [hr]; exact hγ.symm) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl)
      (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl)
      (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl)
      (by rw [hr]; rfl) (by rw [hγ]; exact hcap1) (by rw [hιl]; exact hcap2)
    have hOLτ : τ.st sOLEN = List.replicate (τ.sh sOLEN) true := by
      rw [hst3, hsh3, Function.update_of_ne (by decide)]; simp [σ2, σ1, hOL]
    have s4 := olenUpd_spec cap tb.length τ hOLτ (by rw [hval3]; simp [htb]) hcap3
    set τ4 := ((τ.sets sOLEN (List.replicate (τ.sh sOLEN + tb.length) true)).seth sOLEN
      (τ.sh sOLEN + tb.length)).setv 0 0 with hτ4
    have hv4 : ∀ r, τ4.val r ≤ S + 1 := by
      intro r
      simp only [τ4, WState.setv_val, WState.seth_val, WState.sets_val, hval3, Function.update_apply]
      have := hv2 r
      split_ifs <;> omega
    have s5 := clearsW_spec cap (List.finRange 40) τ4 (List.nodup_finRange 40) (fun r => by have := hv4 r; omega)
    have hcl : clCost τ4.val (List.finRange 40) ≤ 40 * (3 * (S + 1) + 2) := by
      simpa using clCost_le τ4.val (S + 1) hv4 (List.finRange 40)
    have hbw : WExec cap (.ifs sVAL (.ifs sGF (.seq termW olenUpdW) .skip) .skip) σ2 τ4 (c3 + 1 + (tb.length * (3 + 4) + 1) + 1 + 1) :=
      WExec.ifsT (by simp [wbit, σ2, σ1, hVAL, hsh, readTapeBit])
        (WExec.ifsT (by simp [wbit, σ2, σ1, hGF, hsh, readTapeBit]) (WExec.seq s3 s4))
    have hb' : c3 ≤ termBound Fs pops Ws (σ.st sOUT).length T2 lam J x e q nE idx p G ℓ := by
      have e2 : (σ2.st sOUT).length = (σ.st sOUT).length := by simp [σ2, σ1]
      rw [e2, hγ, hιl] at hc3
      unfold termBound
      rw [List.getD_eq_getElem _ _ hlam, List.getD_eq_getElem _ _ hidx]
      exact hc3
    refine ⟨_, _, ?_, WExec.seq s1 (WExec.seq s2 (WExec.seq hbw s5)), ?_, ?_, ?_⟩
    · omega
    · simp only [τ4, WState.setv_st, WState.seth_st, WState.sets_st, hst3, hsh3, if_pos (And.intro rfl rfl :
        true = true ∧ true = true)]
      rfl
    · funext r; simp
    · simp [τ4, hcell3, σ2, σ1]
  · have hbw : WExec cap (.ifs sVAL (.ifs sGF (.seq termW olenUpdW) .skip) .skip) σ2 σ2 2 := by
      cases v
      · exact WExec.mono (WExec.ifsF (by simp [wbit, σ2, σ1, hVAL, hsh, readTapeBit]) (WExec.skip _)) (by omega)
      · cases g
        · exact WExec.ifsT (by simp [wbit, σ2, σ1, hVAL, hsh, readTapeBit])
            (WExec.ifsF (by simp [wbit, σ2, σ1, hGF, hsh, readTapeBit]) (WExec.skip _))
        · exact absurd ⟨rfl, rfl⟩ hvg
    have s5 := clearsW_spec cap (List.finRange 40) σ2 (List.nodup_finRange 40) (fun r => by have := hv2 r; omega)
    have hcl : clCost σ2.val (List.finRange 40) ≤ 40 * (3 * (S + 1) + 2) := by
      simpa using clCost_le σ2.val (S + 1) hv2 (List.finRange 40)
    refine ⟨_, _, ?_, WExec.seq s1 (WExec.seq s2 (WExec.seq hbw s5)), ?_, ?_, ?_⟩
    · omega
    · rw [if_neg hvg]
      funext j
      simp only [σ2, σ1, WState.setv_st, List.append_nil, List.length_nil, Nat.add_zero, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; first | exact hOL | exact hOL.symm
      · subst h2; rfl
      · rfl
    · funext r; simp
    · simp [σ2, σ1]

end Cell

end NearCubicWires.WireExponent3_5.PrimT.HbM
