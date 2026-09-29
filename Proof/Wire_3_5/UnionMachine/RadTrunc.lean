import Proof.Wire_3_5.UnionMachine.RadCnt

/-! # RADIX, stage 5a (5): digit `d`'s table word, truncated from the table at `Lmax` (P3:2604)

The table builder runs once, at `Lmax = G`; digit `d`'s block writer reads the table word at `L_d = |gis_d| ≤ G`.
Row `j` of the list data at length `L` is the first `L` bits of its row at `G` (`rowsOf D L j = (range L).map
(inLevel j)`), so digit `d`'s table word is the table at `G` with every row cut to its first `L_d` bits.
The record loop copies the records, appending, from the table at `G` (read in place); the full truncation program
(header, loop, closing bits, rewinds) is the next file's.

* `copyUn` / **`copyUn_spec`** (a unary field), `skipK` / **`skipK_spec`** (`K` cells), the reader-writer state `St`,
  `recC` / **`recC_spec`** (one record `true :: (unary a ++ unary b ++ row)`, the row cut to `L`), **`recLoop_spec`**;
* **`rowsOf_take`**: `(rowsOf D G j).take L = rowsOf D L j` for `L ≤ G`.

Paper quantity of the main type: the fixed hash's level table at the digit's population size (the list data's rows). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadTrunc
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.FinalPass.ListEval NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.UnionMachine.RadFields
open NearCubicWires.WireExponent3_5.UnionMachine.RadWin

theorem rowsOf_take (D : Lists.ListData) (L G j : ℕ) (h : L ≤ G) : (rowsOf D G j).take L = rowsOf D L j := by
  unfold rowsOf
  rw [← List.map_take, List.take_range, min_eq_left h]

variable {ns nr : ℕ} (cap : ℕ)

/-- Copy a unary field `1^a 0` of `S` onto `O`. -/
def copyUn (O S : Fin (ns + 1)) (OP SP : Fin nr) : WM ns nr :=
  .seq (.whs S (.seq (emitW O OP [true]) (WM.fwdC S SP))) (.seq (emitW O OP [false]) (WM.fwdC S SP))

theorem copyUnLoop_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP : Fin nr) (hOSP : OP ≠ SP) : ∀ (a : ℕ) (rest : List Bool)
    (σ : WState ns nr), (σ.st S).drop (σ.sh S) = List.replicate a true ++ false :: rest →
    σ.sh O = (σ.st O).length → σ.val OP + a ≤ cap → σ.val SP + a < cap →
    WExec cap (.whs S (.seq (emitW O OP [true]) (WM.fwdC S SP))) σ
      (((appendO σ O OP (List.replicate a true)).seth S (σ.sh S + a)).setv SP (σ.val SP + a)) (16 * a + 1)
  | 0, rest, σ, hd, _, _, _ => by
    have hb : wbit σ S = false := by
      unfold wbit; rw [← Nat.add_zero (σ.sh S), readDrop, hd]; rfl
    have e : ((appendO σ O OP (List.replicate 0 true)).seth S (σ.sh S + 0)).setv SP (σ.val SP + 0) = σ := by
      rw [List.replicate_zero, appendO_nil]; exact WState.eq (by simp) rfl (by simp) rfl
    rw [e]; exact WExec.whsF hb
  | a + 1, rest, σ, hd, ho, hc, hs => by
    have hb : wbit σ S = true := by
      unfold wbit; rw [← Nat.add_zero (σ.sh S), readDrop, hd]; rfl
    have h1 := emitW_spec cap O OP [true] σ ho (by simp; omega)
    have h2 := wfwdC_spec cap S SP (appendO σ O OP [true]) (by rw [ao_val_ne O OP _ _ (Ne.symm hOSP)]; omega)
    set τ := ((appendO σ O OP [true]).seth S ((appendO σ O OP [true]).sh S + 1)).setv SP
      ((appendO σ O OP [true]).val SP + 1) with hτ
    have hτd : (τ.st S).drop (τ.sh S) = List.replicate a true ++ false :: rest := by
      simp only [τ, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
      rw [appendO_st, Function.update_of_ne (Ne.symm hOS)]
      have hsh : (appendO σ O OP [true]).sh S = σ.sh S := by simp [Function.update_apply, Ne.symm hOS]
      rw [hsh]; exact dropSucc (a := true) (by rw [hd]; rfl)
    have ih := copyUnLoop_spec O S hOS OP SP hOSP a rest τ hτd (by simp [τ, hOS, ho])
      (by simp [τ, Function.update_apply, hOSP, Ne.symm hOSP]; omega)
      (by simp [τ, Function.update_apply, hOSP, Ne.symm hOSP]; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq h1 h2) ih) ?_ (by simp; omega)
    simp only [τ]
    apply WState.eq
    · funext j; by_cases hj : j = S
      · subst hj; simp [Function.update_apply, Ne.symm hOS]; omega
      · by_cases hjO : j = O
        · subst hjO; simp [Function.update_apply, hj]; omega
        · simp [Function.update_apply, hj, hjO]
    · funext j; by_cases hjO : j = O
      · subst hjO; simp [Function.update_apply, List.replicate_succ]
      · simp [Function.update_apply, hjO]
    · funext q; by_cases hq : q = SP
      · subst hq; simp [Function.update_apply, Ne.symm hOSP]; omega
      · by_cases hq2 : q = OP
        · subst hq2; simp [Function.update_apply, hq]; omega
        · simp [Function.update_apply, hq, hq2]
    · simp

theorem copyUn_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP : Fin nr) (hOSP : OP ≠ SP) (a : ℕ) (rest : List Bool)
    (σ : WState ns nr) (hd : (σ.st S).drop (σ.sh S) = unary a ++ rest) (ho : σ.sh O = (σ.st O).length)
    (hc : σ.val OP + a + 1 ≤ cap) (hs : σ.val SP + a + 1 < cap) :
    WExec cap (copyUn O S OP SP) σ
      (((appendO σ O OP (unary a)).seth S (σ.sh S + (a + 1))).setv SP (σ.val SP + (a + 1))) (16 * a + 17) := by
  have hd' : (σ.st S).drop (σ.sh S) = List.replicate a true ++ false :: rest := by rw [hd]; simp [unary]
  have h1 := copyUnLoop_spec cap O S hOS OP SP hOSP a rest σ hd' ho (by omega) (by omega)
  set τ := ((appendO σ O OP (List.replicate a true)).seth S (σ.sh S + a)).setv SP (σ.val SP + a) with hτ
  have h2 := emitW_spec cap O OP [false] τ (by simp [τ, hOS, ho]) (by simp [τ, Function.update_apply, hOSP]; omega)
  have h3 := wfwdC_spec cap S SP (appendO τ O OP [false]) (by simp [τ, Function.update_apply, Ne.symm hOSP]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by simp <;> omega)
  rw [hτ, appendO_setv _ O OP SP (Ne.symm hOSP), ao_seth _ S O (Ne.symm hOS), appendO_append]
  have hu : List.replicate a true ++ [false] = unary a := rfl
  rw [hu]
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp [Function.update_apply, Ne.symm hOS]; omega
    · simp [Function.update_apply, hj]
  · simp
  · funext q; by_cases hq : q = SP
    · subst hq; simp [Function.update_apply, Ne.symm hOSP]; omega
    · simp [Function.update_apply, hq]
  · simp

/-- `K` cells forward on `S`, counting in `SP`, consuming `K`. -/
def skipK (S : Fin (ns + 1)) (SP K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (WM.fwdC S SP))

theorem skipK_spec (S : Fin (ns + 1)) (SP K : Fin nr) (hKS : K ≠ SP) (n : ℕ) (σ : WState ns nr) (hK : σ.val K = n)
    (hn : n ≤ cap) (hs : σ.val SP + n ≤ cap) :
    WExec cap (skipK S SP K) σ (((σ.seth S (σ.sh S + n)).setv SP (σ.val SP + n)).setv K 0) (n * (5 + 4) + 1) := by
  let S' : ℕ → WState ns nr := fun k => ((σ.seth S (σ.sh S + k)).setv SP (σ.val SP + k)).setv K (n - k)
  have hS0 : S' 0 = σ := by
    simp only [S', Nat.add_zero, Nat.sub_zero, ← hK]
    apply WState.eq <;> simp [Function.update_eq_self]
  have hloop := UnionMachine.Round.wloop cap K (WM.fwdC S SP) 5 n S' (fun k _ => by simp [S']) hn
    (fun k hk => by
      have e1 : (S' k).setv K (n - k - 1) = ((σ.seth S (σ.sh S + k)).setv SP (σ.val SP + k)).setv K (n - k - 1) := by
        simp only [S', wsetv_setv]
      rw [e1]
      have h := wfwdC_spec cap S SP (((σ.seth S (σ.sh S + k)).setv SP (σ.val SP + k)).setv K (n - k - 1))
        (by simp [Function.update_apply, Ne.symm hKS]; omega)
      refine WExec.cast cap h ?_ le_rfl
      simp only [S']
      apply WState.eq
      · funext j; by_cases hj : j = S
        · subst hj; simp; omega
        · simp [Function.update_apply, hj]
      · rfl
      · funext q; by_cases hq : q = K
        · subst hq; simp [Function.update_apply, hKS]; omega
        · by_cases hq2 : q = SP
          · subst hq2; simp [Function.update_apply, hq]; omega
          · simp [Function.update_apply, hq, hq2]
      · rfl)
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  simp only [S', Nat.sub_self]

section RW
variable (σ : WState ns nr) (O S : Fin (ns + 1)) (OP SP : Fin nr)

/-- The reader-writer state: `u` appended to `O` (by `OP`), `S` read `k` cells further (by `SP`). -/
def St (u : List Bool) (k : ℕ) : WState ns nr := ((appendO σ O OP u).seth S (σ.sh S + k)).setv SP (σ.val SP + k)

variable {σ O S OP SP}

theorem St_nil : St σ O S OP SP [] 0 = σ := by
  unfold St; rw [appendO_nil]; apply WState.eq <;> simp [Function.update_eq_self]

theorem St_st_S (hOS : O ≠ S) (u : List Bool) (k : ℕ) : (St σ O S OP SP u k).st S = σ.st S := by
  simp [St, Function.update_apply, Ne.symm hOS]

theorem St_sh_S (u : List Bool) (k : ℕ) : (St σ O S OP SP u k).sh S = σ.sh S + k := by simp [St]

theorem St_st_O (u : List Bool) (k : ℕ) : (St σ O S OP SP u k).st O = σ.st O ++ u := by simp [St]

theorem St_sh_O (hOS : O ≠ S) (u : List Bool) (k : ℕ) : (St σ O S OP SP u k).sh O = σ.sh O + u.length := by
  simp [St, Function.update_apply, hOS]

theorem St_val_OP (hOSP : OP ≠ SP) (u : List Bool) (k : ℕ) : (St σ O S OP SP u k).val OP = σ.val OP + u.length := by
  simp [St, Function.update_apply, hOSP]

theorem St_val_SP (u : List Bool) (k : ℕ) : (St σ O S OP SP u k).val SP = σ.val SP + k := by simp [St]

theorem St_val (r : Fin nr) (h1 : r ≠ OP) (h2 : r ≠ SP) (u : List Bool) (k : ℕ) :
    (St σ O S OP SP u k).val r = σ.val r := by simp [St, Function.update_apply, h1, h2]

theorem St_emit (hOS : O ≠ S) (hOSP : OP ≠ SP) (u v : List Bool) (k : ℕ) :
    appendO (St σ O S OP SP u k) O OP v = St σ O S OP SP (u ++ v) k := by
  unfold St
  rw [appendO_setv _ O OP SP (Ne.symm hOSP), ao_seth _ S O (Ne.symm hOS), appendO_append]

theorem St_fwd (u : List Bool) (k : ℕ) :
    ((St σ O S OP SP u k).seth S ((St σ O S OP SP u k).sh S + 1)).setv SP ((St σ O S OP SP u k).val SP + 1) =
      St σ O S OP SP u (k + 1) := by
  unfold St
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp; omega
    · simp [Function.update_apply, hj]
  · simp
  · funext q; by_cases hq : q = SP
    · subst hq; simp; omega
    · simp [Function.update_apply, hq]
  · simp

theorem St_setv (K : Fin nr) (hK1 : K ≠ OP) (hK2 : K ≠ SP) (x : ℕ) (u : List Bool) (k : ℕ) :
    (St σ O S OP SP u k).setv K x = St (σ.setv K x) O S OP SP u k := by
  unfold St
  rw [appendO_setv _ O OP K hK1]
  apply WState.eq
  · simp
  · simp
  · funext q; by_cases hq : q = K
    · subst hq; simp [Function.update_apply, hK2, hK1]
    · by_cases hq2 : q = SP
      · subst hq2; simp [Function.update_apply, hq, Ne.symm hK2]
      · simp [Function.update_apply, hq, hq2]
  · simp

theorem St_adv (u : List Bool) (k m : ℕ) :
    ((St σ O S OP SP u k).seth S (σ.sh S + k + m)).setv SP (σ.val SP + k + m) = St σ O S OP SP u (k + m) := by
  unfold St
  apply WState.eq
  · funext j; by_cases hj : j = S
    · subst hj; simp; omega
    · simp [Function.update_apply, hj]
  · simp
  · funext q; by_cases hq : q = SP
    · subst hq; simp; omega
    · simp [Function.update_apply, hq]
  · simp

theorem St_setv_self (K : Fin nr) (hK1 : K ≠ OP) (hK2 : K ≠ SP) (hK0 : σ.val K = 0) (x : ℕ) (u : List Bool) (k : ℕ) :
    (St (σ.setv K x) O S OP SP u k).setv K 0 = St σ O S OP SP u k := by
  rw [St_setv K hK1 hK2, wsetv_setv, ← hK0, wsetv_same]

end RW

/-- A record's head: the marker and the two unary fields. -/
def recA (O S : Fin (ns + 1)) (OP SP : Fin nr) : WM ns nr :=
  .seq (emitW O OP [true]) (.seq (WM.fwdC S SP) (.seq (copyUn O S OP SP) (copyUn O S OP SP)))

theorem recA_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP : Fin nr) (hOSP : OP ≠ SP) (σ : WState ns nr) (a b : ℕ)
    (rest : List Bool) (hrd : (σ.st S).drop (σ.sh S) = true :: (unary a ++ (unary b ++ rest)))
    (ho : σ.sh O = (σ.st O).length) (hc : σ.val OP + a + b + 3 ≤ cap) (hs : σ.val SP + a + b + 3 < cap) :
    WExec cap (recA O S OP SP) σ (St σ O S OP SP ([true] ++ unary a ++ unary b) (1 + (a + 1) + (b + 1)))
      (8 + 1 + (5 + 1 + ((16 * a + 17) + 1 + (16 * b + 17)))) := by
  have lua : (unary a).length = a + 1 := by simp [unary]
  have hd1 : (σ.st S).drop (σ.sh S + 1) = unary a ++ (unary b ++ rest) := dropSucc hrd
  have hd2 : (σ.st S).drop (σ.sh S + 1 + (a + 1)) = unary b ++ rest := by rw [← lua]; exact dropAppend hd1
  have ho0 : ∀ (u : List Bool) (k : ℕ), (St σ O S OP SP u k).sh O = ((St σ O S OP SP u k).st O).length := by
    intro u k; rw [St_sh_O hOS, St_st_O, ho]; simp
  have s1 := emitW_spec cap O OP [true] (St σ O S OP SP [] 0) (ho0 _ _) (by rw [St_val_OP hOSP]; simp; omega)
  rw [St_emit hOS hOSP, St_nil, List.nil_append] at s1
  have s2 := wfwdC_spec cap S SP (St σ O S OP SP [true] 0) (by rw [St_val_SP]; omega)
  rw [St_sh_S, St_val_SP, St_adv, Nat.zero_add] at s2
  have s3 := copyUn_spec cap O S hOS OP SP hOSP a (unary b ++ rest) (St σ O S OP SP [true] 1)
    (by rw [St_st_S hOS, St_sh_S]; exact hd1) (ho0 _ _) (by rw [St_val_OP hOSP]; simp; omega)
    (by rw [St_val_SP]; omega)
  rw [St_emit hOS hOSP, St_sh_S, St_val_SP, St_adv] at s3
  have s4 := copyUn_spec cap O S hOS OP SP hOSP b rest (St σ O S OP SP ([true] ++ unary a) (1 + (a + 1)))
    (by rw [St_st_S hOS, St_sh_S, ← Nat.add_assoc]; exact hd2) (ho0 _ _) (by rw [St_val_OP hOSP]; simp [lua]; omega)
    (by rw [St_val_SP]; omega)
  rw [St_emit hOS hOSP, St_sh_S, St_val_SP, St_adv] at s4
  exact WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))

/-- A record's row: its first `L` bits (`Lr = L`), then `G − L` cells skipped (`GLr = G − L`); counter `K`, temp `T`. -/
def recB (O S : Fin (ns + 1)) (OP SP K T Lr GLr : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR Lr K T) (.seq (copyP O S OP SP K) (.seq (FinalPass.Hash4.wcopyR GLr K T)
    (skipK S SP K)))

theorem wcopyR_St (O S : Fin (ns + 1)) (OP SP A K T : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T)
    (hA1 : A ≠ OP) (hA2 : A ≠ SP) (hK1 : K ≠ OP) (hK2 : K ≠ SP) (hT1 : T ≠ OP) (hT2 : T ≠ SP) (σ : WState ns nr)
    (u : List Bool) (k : ℕ) (hK : σ.val K = 0) (hT : σ.val T = 0) (hA : σ.val A ≤ cap) :
    WExec cap (FinalPass.Hash4.wcopyR A K T) (St σ O S OP SP u k) ((St σ O S OP SP u k).setv K (σ.val A))
      (18 * σ.val A + 3) := by
  have h := FinalPass.Hash4.wcopyR_spec cap A K T hAK hAT hKT (St σ O S OP SP u k)
    (by rw [St_val K hK1 hK2]; exact hK) (by rw [St_val T hT1 hT2]; exact hT) (by rw [St_val A hA1 hA2]; exact hA)
  rwa [St_val A hA1 hA2] at h

theorem copyP_St (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP K : Fin nr) (hKO : K ≠ OP) (hKS : K ≠ SP) (hOSP : OP ≠ SP)
    (σ : WState ns nr) (u : List Bool) (k : ℕ) (w rest : List Bool) (hK0 : σ.val K = 0)
    (hrd : (σ.st S).drop (σ.sh S + k) = w ++ rest) (ho : σ.sh O = (σ.st O).length)
    (hc : σ.val OP + u.length + w.length ≤ cap) (hs : σ.val SP + k + w.length ≤ cap) :
    WExec cap (copyP O S OP SP K) ((St σ O S OP SP u k).setv K w.length) (St σ O S OP SP (u ++ w) (k + w.length))
      (w.length * (8 + 1 + 1 + 5 + 4) + 1) := by
  rw [St_setv K hKO hKS]
  have vOP : (St (σ.setv K w.length) O S OP SP u k).val OP = σ.val OP + u.length := by
    rw [St_val_OP hOSP]; simp [Function.update_apply, Ne.symm hKO]
  have vSP : (St (σ.setv K w.length) O S OP SP u k).val SP = σ.val SP + k := by
    rw [St_val_SP]; simp [Function.update_apply, Ne.symm hKS]
  have h := copyP_spec cap O S hOS OP SP K hKO hKS hOSP w (St (σ.setv K w.length) O S OP SP u k)
    (by rw [St_val K hKO hKS]; simp)
    (fun i hi => by
      rw [St_st_S hOS, St_sh_S]
      simp only [WState.setv_st, WState.setv_sh]
      rw [readDrop, hrd]
      unfold readTapeBit
      rw [List.getD_append _ _ _ _ hi])
    (by rw [St_sh_O hOS, St_st_O]; simp [ho])
    (by rw [vOP]; omega) (by rw [vSP]; omega) (by omega)
  rw [St_emit hOS hOSP, St_sh_S, St_val_SP, St_adv, St_setv_self K hKO hKS hK0] at h
  exact h

theorem skipK_St (O S : Fin (ns + 1)) (OP SP K : Fin nr) (hKO : K ≠ OP) (hKS : K ≠ SP) (σ : WState ns nr)
    (u : List Bool) (k n : ℕ) (hK0 : σ.val K = 0) (hn : n ≤ cap) (hs : σ.val SP + k + n ≤ cap) :
    WExec cap (skipK S SP K) ((St σ O S OP SP u k).setv K n) (St σ O S OP SP u (k + n)) (n * (5 + 4) + 1) := by
  rw [St_setv K hKO hKS]
  have vSP : (St (σ.setv K n) O S OP SP u k).val SP = σ.val SP + k := by
    rw [St_val_SP]; simp [Function.update_apply, Ne.symm hKS]
  have h := skipK_spec cap S SP K hKS n (St (σ.setv K n) O S OP SP u k) (by rw [St_val K hKO hKS]; simp) hn
    (by rw [vSP]; omega)
  rw [St_sh_S, St_val_SP, St_adv, St_setv_self K hKO hKS hK0] at h
  exact h

theorem recB_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP K T Lr GLr : Fin nr)
    (hd : [OP, SP, K, T, Lr, GLr].Nodup) (σ : WState ns nr) (u : List Bool) (k L G : ℕ) (r rest : List Bool)
    (hrd : (σ.st S).drop (σ.sh S + k) = r ++ rest) (hr : r.length = G) (hLG : L ≤ G)
    (ho : σ.sh O = (σ.st O).length) (hK : σ.val K = 0) (hT : σ.val T = 0) (hLr : σ.val Lr = L)
    (hGL : σ.val GLr = G - L) (hc : σ.val OP + u.length + L ≤ cap) (hs : σ.val SP + k + G ≤ cap) :
    WExec cap (recB O S OP SP K T Lr GLr) (St σ O S OP SP u k) (St σ O S OP SP (u ++ r.take L) (k + G))
      ((18 * L + 3) + 1 + ((L * 19 + 1) + 1 + ((18 * (G - L) + 3) + 1 + ((G - L) * 9 + 1)))) := by
  have htl : (r.take L).length = L := by rw [List.length_take, min_eq_left (by omega)]
  have f5 : σ.val Lr ≤ cap := by omega
  have f6a : σ.val OP + u.length + (r.take L).length ≤ cap := by rw [htl]; omega
  have f6b : σ.val SP + k + (r.take L).length ≤ cap := by rw [htl]; omega
  have f7 : σ.val GLr ≤ cap := by omega
  have f8a : G - L ≤ cap := by omega
  have f8b : σ.val SP + (k + L) + (G - L) ≤ cap := by omega
  have f8c : k + L + (G - L) = k + G := by omega
  have hrd' : (σ.st S).drop (σ.sh S + k) = r.take L ++ (r.drop L ++ rest) := by
    rw [hrd, ← List.append_assoc, List.take_append_drop]
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1, -⟩ := hd
  have s5 := wcopyR_St cap O S OP SP Lr K T (Ne.symm c2) (Ne.symm d1) c1 (Ne.symm a4) (Ne.symm b3) (Ne.symm a2)
    (Ne.symm b1) (Ne.symm a3) (Ne.symm b2) σ u k hK hT f5
  rw [hLr] at s5
  have s6 := copyP_St cap O S hOS OP SP K (Ne.symm a2) (Ne.symm b1) a1 σ u k (r.take L) (r.drop L ++ rest) hK hrd' ho
    f6a f6b
  rw [htl] at s6
  have s7 := wcopyR_St cap O S OP SP GLr K T (Ne.symm c3) (Ne.symm d2) c1 (Ne.symm a5) (Ne.symm b4) (Ne.symm a2)
    (Ne.symm b1) (Ne.symm a3) (Ne.symm b2) σ (u ++ r.take L) (k + L) hK hT f7
  rw [hGL] at s7
  have s8 := skipK_St cap O S OP SP K (Ne.symm a2) (Ne.symm b1) σ (u ++ r.take L) (k + L) (G - L) hK f8a f8b
  rw [f8c] at s8
  exact WExec.seq s5 (WExec.seq s6 (WExec.seq s7 s8))

theorem St_St (σ : WState ns nr) (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP : Fin nr) (hOSP : OP ≠ SP)
    (u v : List Bool) (k m : ℕ) :
    St (St σ O S OP SP u k) O S OP SP v m = St σ O S OP SP (u ++ v) (k + m) := by
  show ((appendO (St σ O S OP SP u k) O OP v).seth S ((St σ O S OP SP u k).sh S + m)).setv SP
    ((St σ O S OP SP u k).val SP + m) = _
  rw [St_emit hOS hOSP, St_sh_S, St_val_SP, St_adv]

/-- One record, its row cut. -/
def recC (O S : Fin (ns + 1)) (OP SP K T Lr GLr : Fin nr) : WM ns nr :=
  .seq (recA O S OP SP) (recB O S OP SP K T Lr GLr)

/-- One record's cost. -/
def recCost (a b L G : ℕ) : ℕ :=
  (8 + 1 + (5 + 1 + ((16 * a + 17) + 1 + (16 * b + 17)))) + 1 +
    ((18 * L + 3) + 1 + ((L * 19 + 1) + 1 + ((18 * (G - L) + 3) + 1 + ((G - L) * 9 + 1))))

theorem recC_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP K T Lr GLr : Fin nr)
    (hd : [OP, SP, K, T, Lr, GLr].Nodup) (σ : WState ns nr) (a b L G : ℕ) (row rest : List Bool)
    (hrd : (σ.st S).drop (σ.sh S) = true :: (unary a ++ (unary b ++ (row ++ rest)))) (hr : row.length = G) (hLG : L ≤ G)
    (ho : σ.sh O = (σ.st O).length) (hK : σ.val K = 0) (hT : σ.val T = 0) (hLr : σ.val Lr = L)
    (hGL : σ.val GLr = G - L) (hc : σ.val OP + a + b + L + 3 ≤ cap) (hs : σ.val SP + a + b + G + 3 < cap) :
    WExec cap (recC O S OP SP K T Lr GLr) σ
      (St σ O S OP SP (true :: (unary a ++ unary b ++ row.take L)) (a + b + G + 3)) (recCost a b L G) := by
  have lua : (unary a).length = a + 1 := by simp [unary]
  have lub : (unary b).length = b + 1 := by simp [unary]
  have hlu : ([true] ++ unary a ++ unary b).length = a + b + 3 := by simp [lua, lub]; omega
  have fc : σ.val OP + ([true] ++ unary a ++ unary b).length + L ≤ cap := by rw [hlu]; omega
  have fs : σ.val SP + (1 + (a + 1) + (b + 1)) + G ≤ cap := by omega
  have fk : 1 + (a + 1) + (b + 1) + G = a + b + G + 3 := by omega
  have hrd2 : (σ.st S).drop (σ.sh S + (1 + (a + 1) + (b + 1))) = row ++ rest := by
    have e : σ.sh S + (1 + (a + 1) + (b + 1)) = σ.sh S + ([true] ++ unary a ++ unary b).length := by rw [hlu]; omega
    rw [e]
    exact dropAppend (by rw [hrd]; simp [List.append_assoc])
  have hnd := hd
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨a1, -, -, -, -⟩, -⟩ := hnd
  have s1 := recA_spec cap O S hOS OP SP a1 σ a b (row ++ rest) hrd ho (by omega) (by omega)
  have s2 := recB_spec cap O S hOS OP SP K T Lr GLr hd σ ([true] ++ unary a ++ unary b) (1 + (a + 1) + (b + 1)) L G row
    rest hrd2 hr hLG ho hK hT hLr hGL fc fs
  rw [fk] at s2
  have eu : [true] ++ unary a ++ unary b ++ row.take L = true :: (unary a ++ unary b ++ row.take L) := by simp
  rw [eu] at s2
  exact WExec.seq s1 s2

/-- A source record `true :: (unary a_j ++ unary b_j ++ row_j)`. -/
def recG (a b : ℕ → ℕ) (row : ℕ → List Bool) (j : ℕ) : List Bool := true :: (unary (a j) ++ unary (b j) ++ row j)

/-- The loop over the records. -/
def recLoop (O S : Fin (ns + 1)) (OP SP K T Lr GLr : Fin nr) : WM ns nr := .whs S (recC O S OP SP K T Lr GLr)

/-- The record loop's cost. -/
def loopCost (a b : ℕ → ℕ) (L G : ℕ) (js : List ℕ) : ℕ := (js.map fun j => recCost (a j) (b j) L G + 2).sum + 1

theorem recG_len (a b : ℕ → ℕ) (row : ℕ → List Bool) (j : ℕ) :
    (recG a b row j).length = a j + b j + (row j).length + 3 := by
  simp [recG, unary]; omega

theorem recLoop_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP K T Lr GLr : Fin nr)
    (hd : [OP, SP, K, T, Lr, GLr].Nodup) (σ : WState ns nr) (a b : ℕ → ℕ) (row : ℕ → List Bool) (L G : ℕ)
    (rest : List Bool) (hLG : L ≤ G) (ho : σ.sh O = (σ.st O).length) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (hLr : σ.val Lr = L) (hGL : σ.val GLr = G - L) :
    ∀ (js : List ℕ) (u : List Bool) (k : ℕ), (∀ j ∈ js, (row j).length = G) →
      (σ.st S).drop (σ.sh S + k) = js.flatMap (recG a b row) ++ (false :: rest) →
      σ.val OP + u.length + (js.flatMap (recG a b fun j => (row j).take L)).length ≤ cap →
      σ.val SP + k + (js.flatMap (recG a b row)).length < cap →
      WExec cap (recLoop O S OP SP K T Lr GLr) (St σ O S OP SP u k)
        (St σ O S OP SP (u ++ js.flatMap (recG a b fun j => (row j).take L)) (k + (js.flatMap (recG a b row)).length))
        (loopCost a b L G js)
  | [], u, k, _, hdr, _, _ => by
    have hb : wbit (St σ O S OP SP u k) S = false := by
      unfold wbit; rw [St_st_S hOS, St_sh_S, ← Nat.add_zero (σ.sh S + k), readDrop, hdr]; rfl
    have e : St σ O S OP SP (u ++ ([] : List ℕ).flatMap (recG a b fun j => (row j).take L))
        (k + (([] : List ℕ).flatMap (recG a b row)).length) = St σ O S OP SP u k := by simp
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by simp [loopCost])
  | j :: js, u, k, hrow, hdr, hc, hs => by
    have hrj : (row j).length = G := hrow j (by simp)
    have hlG := recG_len a b row j
    have hlL : (recG a b (fun j => (row j).take L) j).length = a j + b j + L + 3 := by
      unfold recG; simp [unary, List.length_take, hrj, Nat.min_eq_left hLG]; omega
    have htk : ((row j).take L).length = L := by rw [List.length_take, min_eq_left (by omega)]
    have hfG : ((j :: js).flatMap (recG a b row)).length =
        (recG a b row j).length + (js.flatMap (recG a b row)).length := by simp [List.flatMap_cons]
    have hfL : ((j :: js).flatMap (recG a b fun j => (row j).take L)).length =
        (recG a b (fun j => (row j).take L) j).length + (js.flatMap (recG a b fun j => (row j).take L)).length := by
      simp [List.flatMap_cons]
    have fc : σ.val OP + u.length + a j + b j + L + 3 ≤ cap := by
      rw [hfL, hlL] at hc; omega
    have fs : σ.val SP + k + a j + b j + G + 3 < cap := by rw [hfG, hlG, hrj] at hs; omega
    have fc' : σ.val OP + (u ++ recG a b (fun j => (row j).take L) j).length +
        (js.flatMap (recG a b fun j => (row j).take L)).length ≤ cap := by
      rw [List.length_append]; rw [hfL] at hc; omega
    have fs' : σ.val SP + (k + (a j + b j + G + 3)) + (js.flatMap (recG a b row)).length < cap := by
      rw [hfG, hlG, hrj] at hs; omega
    have fk : k + (a j + b j + G + 3) + (js.flatMap (recG a b row)).length =
        k + ((j :: js).flatMap (recG a b row)).length := by rw [hfG, hlG, hrj]; omega
    have hdr1 : ((St σ O S OP SP u k).st S).drop ((St σ O S OP SP u k).sh S) =
        true :: (unary (a j) ++ (unary (b j) ++ (row j ++ (js.flatMap (recG a b row) ++ false :: rest)))) := by
      rw [St_st_S hOS, St_sh_S, hdr]; simp [recG, List.flatMap_cons, List.append_assoc]
    have hdr2 : (σ.st S).drop (σ.sh S + (k + (a j + b j + G + 3))) = js.flatMap (recG a b row) ++ false :: rest := by
      have e : σ.sh S + (k + (a j + b j + G + 3)) = σ.sh S + k + (recG a b row j).length := by rw [hlG, hrj]; omega
      rw [e]; exact dropAppend (by rw [hdr]; simp [List.flatMap_cons, List.append_assoc])
    have hnd := hd
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, List.not_mem_nil, or_false, not_or] at hnd
    obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, -⟩ := hnd
    have hb : wbit (St σ O S OP SP u k) S = true := by
      unfold wbit; rw [← Nat.add_zero ((St σ O S OP SP u k).sh S), readDrop, hdr1]; rfl
    have s1 := recC_spec cap O S hOS OP SP K T Lr GLr hd (St σ O S OP SP u k) (a j) (b j) L G (row j)
      (js.flatMap (recG a b row) ++ false :: rest) hdr1 hrj hLG
      (by rw [St_sh_O hOS, St_st_O]; simp [ho])
      (by rw [St_val K (Ne.symm a2) (Ne.symm b1)]; exact hK) (by rw [St_val T (Ne.symm a3) (Ne.symm b2)]; exact hT)
      (by rw [St_val Lr (Ne.symm a4) (Ne.symm b3)]; exact hLr) (by rw [St_val GLr (Ne.symm a5) (Ne.symm b4)]; exact hGL)
      (by rw [St_val_OP a1]; exact fc) (by rw [St_val_SP]; exact fs)
    rw [St_St σ O S hOS OP SP a1] at s1
    have ih := recLoop_spec O S hOS OP SP K T Lr GLr hd σ a b row L G rest hLG ho hK hT hLr hGL js
      (u ++ recG a b (fun j => (row j).take L) j) (k + (a j + b j + G + 3)) (fun j' hj' => hrow j' (by simp [hj']))
      hdr2 fc' fs'
    rw [fk, List.append_assoc] at ih
    have eL : recG a b (fun j => (row j).take L) j ++ js.flatMap (recG a b fun j => (row j).take L) =
        (j :: js).flatMap (recG a b fun j => (row j).take L) := by simp [List.flatMap_cons]
    rw [eL] at ih
    have eR : true :: (unary (a j) ++ unary (b j) ++ (row j).take L) = recG a b (fun j => (row j).take L) j := rfl
    rw [eR] at s1
    exact WExec.mono (WExec.whsT hb s1 ih) (by simp [loopCost]; omega)

end NearCubicWires.WireExponent3_5.UnionMachine.RadTrunc
