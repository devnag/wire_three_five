import Proof.Wire_3_5.Primitive.SeedFix.HbVal
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixElimX

/-! # C4.Hb, machine part 13: the cell's constraint records (`filt:soft`, P3:2253-2290)

"After fixing `p`, Gaussian elimination finds its conditional probability" (P3:2268-2269). The elimination reads its
constraints from `CONS` as the records `T frame(binary ℓ₀ ι_r) frame(binary k tgt_r)` (`consRec`), `k = λ+1` and
`tgt_r = γ_r·2^λ` at a moment level, `k = J` and `tgt_r = 0` at the terminal level (`consOf`, HashRefM). The records
program copies the sign bits to the scratch `S2`, then writes one record per position (the position's field copied,
framed, from `CTR`), over the stale records (`overlay`).

Paper quantity of the main type (**`consW_spec`**): the cell's constraint tape `consTape ℓ₀ k (consL …)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

section Put
variable (cap : ℕ)

/-- Stream `S` holds `w` over the backing `B`, its head just after `w`. -/
def wov (σ : HS) (S : Fin 24) (w B : List Bool) : HS := (σ.sets S (overlay w B)).seth S w.length

/-- Close a `WState` equality stream by stream. -/
syntax "hbeq" : tactic
macro_rules
  | `(tactic| hbeq) => `(tactic| (apply WState.eq <;> (try funext _) <;>
      simp [wov, Function.update_apply] <;> (try split_ifs) <;> (try subst_vars) <;> (try simp_all) <;> (try omega)))

/-- Write one bit over the backing and step. -/
def putW (S : Fin 24) (b : Bool) : HW := .seq (.wr S b) (.fwd S)

theorem putW_spec (S : Fin 24) (b : Bool) (w B : List Bool) (σ : HS) :
    WExec cap (putW S b) (wov σ S w B) (wov σ S (w ++ [b]) B) 3 := by
  have s1 := WExec.wr (cap := cap) S b (wov σ S w B)
  have s2 := WExec.fwd (cap := cap) S ((wov σ S w B).sets S (writeTapeBit ((wov σ S w B).st S) ((wov σ S w B).sh S) b))
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (le_refl _)
  simp only [wov, WState.sets_st, WState.seth_st, WState.seth_sh, WState.sets_sh, Function.update_self, overlay_write]
  apply WState.eq
  · funext j; simp only [WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> simp
  · funext j; simp only [WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> rfl
  · rfl
  · rfl

/-- The framed pairs of a bit word (a frame without its end). -/
def pairs (w : List Bool) : List Bool := w.flatMap fun b => [true, b]

theorem frame_pairs : ∀ w : List Bool, frame w = pairs w ++ [false]
  | [] => rfl
  | b :: w => by simp only [frame, pairs, List.flatMap_cons] at *; rw [frame_pairs w]; simp [pairs]

theorem pairs_take_succ (w : List Bool) (j : ℕ) (hj : j < w.length) :
    pairs (w.take (j + 1)) = pairs (w.take j) ++ [true, w[j]] := by
  simp only [pairs, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

end Put

section Field
variable (cap : ℕ)

/-- One framed pair copied from `CTR` to `CONS`. -/
def fBodyW : HW := .seq (putW sCONS true) (.seq (.ifs sCTR (putW sCONS true) (putW sCONS false)) (.fwd sCTR))

/-- **A position's field**, framed: the `ℓ` raw bits at `CTR`'s head (register `16` holds `ℓ`). -/
def fieldW : HW := .seq (FinalPass.Hash4.wcopyR 16 26 22) (.seq (.whr 26 (.seq (.dec 26) fBodyW)) (putW sCONS false))

theorem fieldW_spec (bits : List Bool) (w B : List Bool) (σ : HS) (x0 : ℕ)
    (hF : ∀ m < bits.length, readTapeBit (σ.st sCTR) (x0 + m) = bits.getD m false) (hCh : σ.sh sCTR = x0)
    (h16 : σ.val 16 = bits.length) (h22 : σ.val 22 = 0) (h26 : σ.val 26 = 0) (hcap : bits.length ≤ cap) :
    WExec cap fieldW (wov σ sCONS w B) (wov (σ.seth sCTR (x0 + bits.length)) sCONS (w ++ frame bits) B)
      (18 * bits.length + 3 + 1 + (bits.length * (10 + 4) + 1) + 1 + 3) := by
  set ℓ := bits.length with hℓ
  have s1 := FinalPass.Hash4.wcopyR_spec cap 16 26 22 (by decide) (by decide) (by decide) (wov σ sCONS w B)
    (by simp [wov, h26]) (by simp [wov, h22]) (by simpa [wov, h16] using hcap)
  have v16 : (wov σ sCONS w B).val 16 = ℓ := by simp [wov, h16]
  rw [v16] at s1
  let S : ℕ → HS := fun j => (wov ((σ.seth sCTR (x0 + j)).setv 26 (ℓ - j)) sCONS (w ++ pairs (bits.take j)) B)
  have hS0 : S 0 = (wov σ sCONS w B).setv 26 ℓ := by
    simp only [S, List.take_zero, Nat.add_zero, Nat.sub_zero]
    simp only [pairs, List.flatMap_nil, List.append_nil]
    rw [← hCh]
    apply WState.eq
    · funext j; simp only [wov, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
    · rfl
    · rfl
  have hloop := UnionMachine.Round.wloop cap 26 fBodyW 10 ℓ S (fun k _ => by simp [S, wov]) hcap
    (fun k hk => by
      set τ := (S k).setv 26 (ℓ - k - 1) with hτ
      have eτ : τ = wov ((σ.seth sCTR (x0 + k)).setv 26 (ℓ - k - 1)) sCONS (w ++ pairs (bits.take k)) B := by
        simp only [τ, S]
        hbeq
      rw [eτ]
      have t1 := putW_spec cap sCONS true (w ++ pairs (bits.take k)) B ((σ.seth sCTR (x0 + k)).setv 26 (ℓ - k - 1))
      have hb : wbit (wov ((σ.seth sCTR (x0 + k)).setv 26 (ℓ - k - 1)) sCONS (w ++ pairs (bits.take k) ++ [true]) B)
          sCTR = bits[k] := by
        simp only [wbit, wov, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh, WState.setv_st,
          WState.setv_sh, Function.update_apply]
        simp only [show (5 : Fin 24) ≠ 10 by decide, if_false, if_true]
        rw [hF k hk, List.getD_eq_getElem _ _ hk]
      have hnext : S (k + 1) = wov (((σ.seth sCTR (x0 + k)).setv 26 (ℓ - k - 1)).seth sCTR (x0 + k + 1)) sCONS
          (w ++ pairs (bits.take k) ++ [true] ++ [bits[k]]) B := by
        simp only [S, pairs_take_succ bits k hk, List.append_assoc]
        hbeq
      rw [hnext]
      cases hbk : bits[k]
      · rw [hbk] at hb
        have t2 := putW_spec cap sCONS false (w ++ pairs (bits.take k) ++ [true]) B
          ((σ.seth sCTR (x0 + k)).setv 26 (ℓ - k - 1))
        have t3 := WExec.fwd (cap := cap) sCTR (wov ((σ.seth sCTR (x0 + k)).setv 26 (ℓ - k - 1)) sCONS
          (w ++ pairs (bits.take k) ++ [true] ++ [false]) B)
        refine WExec.cast cap (WExec.seq t1 (WExec.seq (WExec.ifsF (P := putW sCONS true) hb t2) t3)) ?_ (by omega)
        hbeq
      · rw [hbk] at hb
        have t2 := putW_spec cap sCONS true (w ++ pairs (bits.take k) ++ [true]) B
          ((σ.seth sCTR (x0 + k)).setv 26 (ℓ - k - 1))
        have t3 := WExec.fwd (cap := cap) sCTR (wov ((σ.seth sCTR (x0 + k)).setv 26 (ℓ - k - 1)) sCONS
          (w ++ pairs (bits.take k) ++ [true] ++ [true]) B)
        refine WExec.cast cap (WExec.seq t1 (WExec.seq (WExec.ifsT (Q := putW sCONS false) hb t2) t3)) ?_ (by omega)
        hbeq)
  rw [hS0] at hloop
  have t4 := putW_spec cap sCONS false (w ++ pairs (bits.take ℓ)) B ((σ.seth sCTR (x0 + ℓ)).setv 26 (ℓ - ℓ))
  refine WExec.cast cap (WExec.seq s1 (WExec.seq hloop t4)) ?_ (le_refl _)
  rw [List.take_length, frame_pairs, List.append_assoc]
  hbeq

end Field

section Target
variable (cap : ℕ)

/-- One framed zero of the target. -/
def tBodyW : HW := .seq (putW sCONS true) (putW sCONS false)

/-- **A record's target**, framed: `λ` zeros (register `9`), then at a moment level (`r₂₈ = 1`) the sign bit from
`S2`, then the frame's end. -/
def tgtW : HW := .seq (FinalPass.Hash4.wcopyR 9 26 22) (.seq (.whr 26 (.seq (.dec 26) tBodyW))
  (.seq (.ifr 28 (.seq (putW sCONS true) (.ifs sS2 (putW sCONS true) (putW sCONS false))) .skip) (putW sCONS false)))

/-- The target's framed bits. -/
def tgtBits (lam : ℕ) (lt g : Bool) : List Bool :=
  PrimAsm.FiltRec.reps lam [true, false] ++ ((if lt then [true, g] else []) ++ [false])

def tgtCost (lam : ℕ) : ℕ := 18 * lam + 3 + 1 + (lam * (7 + 4) + 1) + 1 + (9 + 1 + 3)

theorem tgtW_spec (lam : ℕ) (lt g : Bool) (w B : List Bool) (σ : HS) (h9 : σ.val 9 = lam) (h22 : σ.val 22 = 0)
    (h26 : σ.val 26 = 0) (h28 : σ.val 28 = if lt then 1 else 0) (hg : readTapeBit (σ.st sS2) (σ.sh sS2) = g)
    (hcap : lam ≤ cap) :
    WExec cap tgtW (wov σ sCONS w B) (wov σ sCONS (w ++ tgtBits lam lt g) B) (tgtCost lam) := by
  have s1 := FinalPass.Hash4.wcopyR_spec cap 9 26 22 (by decide) (by decide) (by decide) (wov σ sCONS w B)
    (by simp [wov, h26]) (by simp [wov, h22]) (by simpa [wov, h9] using hcap)
  have v9 : (wov σ sCONS w B).val 9 = lam := by simp [wov, h9]
  rw [v9] at s1
  let S : ℕ → HS := fun j => wov (σ.setv 26 (lam - j)) sCONS (w ++ PrimAsm.FiltRec.reps j [true, false]) B
  have hS0 : S 0 = (wov σ sCONS w B).setv 26 lam := by
    simp only [S, Nat.sub_zero, PrimAsm.FiltRec.reps_zero, List.append_nil]
    hbeq
  have hloop := UnionMachine.Round.wloop cap 26 tBodyW 7 lam S (fun k _ => by simp [S, wov]) hcap
    (fun k hk => by
      have eτ : (S k).setv 26 (lam - k - 1) = wov (σ.setv 26 (lam - k - 1)) sCONS
          (w ++ PrimAsm.FiltRec.reps k [true, false]) B := by
        simp only [S]; hbeq
      rw [eτ]
      have t1 := putW_spec cap sCONS true (w ++ PrimAsm.FiltRec.reps k [true, false]) B (σ.setv 26 (lam - k - 1))
      have t2 := putW_spec cap sCONS false (w ++ PrimAsm.FiltRec.reps k [true, false] ++ [true]) B
        (σ.setv 26 (lam - k - 1))
      refine WExec.cast cap (WExec.seq t1 t2) ?_ (le_refl _)
      simp only [S, PrimAsm.FiltRec.reps_succ, List.append_assoc, List.singleton_append]
      hbeq)
  rw [hS0] at hloop
  set σ2 := S lam with hσ2
  have e2 : σ2 = wov (σ.setv 26 0) sCONS (w ++ PrimAsm.FiltRec.reps lam [true, false]) B := by
    simp only [σ2, S, Nat.sub_self]
  have hrest : ∃ n3, n3 ≤ 9 ∧ WExec cap (.ifr 28 (.seq (putW sCONS true) (.ifs sS2 (putW sCONS true)
      (putW sCONS false))) .skip) σ2 (wov (σ.setv 26 0) sCONS (w ++ PrimAsm.FiltRec.reps lam [true, false] ++
        (if lt then [true, g] else [])) B) n3 := by
    rw [e2]
    cases lt
    · refine ⟨1, by omega, WExec.cast cap (WExec.ifrF (P := WM.seq (putW sCONS true) (WM.ifs sS2 (putW sCONS true)
        (putW sCONS false))) (by simp [wov, h28]) (WExec.skip _)) ?_ (le_refl _)⟩
      simp
    · have t1 := putW_spec cap sCONS true (w ++ PrimAsm.FiltRec.reps lam [true, false]) B (σ.setv 26 0)
      have hb : wbit (wov (σ.setv 26 0) sCONS (w ++ PrimAsm.FiltRec.reps lam [true, false] ++ [true]) B) sS2 = g := by
        simp only [wbit, wov, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh, WState.setv_st,
          WState.setv_sh, Function.update_apply]
        simpa using hg
      cases g
      · have t2 := putW_spec cap sCONS false (w ++ PrimAsm.FiltRec.reps lam [true, false] ++ [true]) B (σ.setv 26 0)
        refine ⟨_, by omega, WExec.cast cap (WExec.ifrT (Q := WM.skip) (by simp [wov, h28])
          (WExec.seq t1 (WExec.ifsF (P := putW sCONS true) hb t2))) ?_ (le_refl _)⟩
        simp [List.append_assoc]
      · have t2 := putW_spec cap sCONS true (w ++ PrimAsm.FiltRec.reps lam [true, false] ++ [true]) B (σ.setv 26 0)
        refine ⟨_, by omega, WExec.cast cap (WExec.ifrT (Q := WM.skip) (by simp [wov, h28])
          (WExec.seq t1 (WExec.ifsT (Q := putW sCONS false) hb t2))) ?_ (le_refl _)⟩
        simp [List.append_assoc]
  obtain ⟨n3, hn3, s3⟩ := hrest
  have s4 := putW_spec cap sCONS false (w ++ PrimAsm.FiltRec.reps lam [true, false] ++ (if lt then [true, g] else []))
    B (σ.setv 26 0)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq hloop (WExec.seq (WExec.mono s3 hn3) s4))) ?_ (le_refl _)
  simp only [tgtBits, List.append_assoc]
  hbeq

end Target

section Record
variable (cap : ℕ)

/-- **One constraint record**: `T`, the position's framed field, the framed target; `S2` steps to the next sign. -/
def recW : HW := .seq (putW sCONS true) (.seq fieldW (.seq tgtW (.fwd sS2)))

/-- A record's bits. -/
def recBits (ℓ ι lam : ℕ) (lt g : Bool) : List Bool := [true] ++ frame (binary ℓ ι) ++ tgtBits lam lt g

def recCost (ℓ lam : ℕ) : ℕ := 3 + 1 + ((18 * ℓ + 3 + 1 + (ℓ * (10 + 4) + 1) + 1 + 3) + 1 + (tgtCost lam + 1 + 1))

theorem recW_spec (ℓ ι lam : ℕ) (lt g : Bool) (w B : List Bool) (σ : HS) (x0 : ℕ)
    (hF : ∀ m < ℓ, readTapeBit (σ.st sCTR) (x0 + m) = (binary ℓ ι).getD m false) (hCh : σ.sh sCTR = x0)
    (hg : readTapeBit (σ.st sS2) (σ.sh sS2) = g) (h9 : σ.val 9 = lam) (h16 : σ.val 16 = ℓ) (h22 : σ.val 22 = 0)
    (h26 : σ.val 26 = 0) (h28 : σ.val 28 = if lt then 1 else 0) (hcap : ℓ + lam ≤ cap) :
    WExec cap recW (wov σ sCONS w B)
      (wov ((σ.seth sCTR (x0 + ℓ)).seth sS2 (σ.sh sS2 + 1)) sCONS (w ++ recBits ℓ ι lam lt g) B) (recCost ℓ lam) := by
  have s1 := putW_spec cap sCONS true w B σ
  have s2 := fieldW_spec cap (binary ℓ ι) (w ++ [true]) B σ x0 (by rw [binary_length]; exact hF) hCh
    (by rw [binary_length]; exact h16) h22 h26 (by rw [binary_length]; omega)
  rw [binary_length] at s2
  have s3 := tgtW_spec cap lam lt g (w ++ [true] ++ frame (binary ℓ ι)) B (σ.seth sCTR (x0 + ℓ)) (by simpa using h9)
    (by simpa using h22) (by simpa using h26) (by simpa using h28) (by simpa using hg) (by omega)
  have s4 := WExec.fwd (cap := cap) sS2 (wov (σ.seth sCTR (x0 + ℓ)) sCONS (w ++ [true] ++ frame (binary ℓ ι) ++
    tgtBits lam lt g) B)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ (le_refl _)
  simp only [recBits, List.append_assoc]
  hbeq

end Record

section Gcopy
variable (cap : ℕ)

/-- One sign bit copied from `CTR` to `S2`. -/
def gcBodyW : HW := .seq (.ifs sCTR (.wr sS2 true) (.wr sS2 false)) (.seq (.fwd sCTR) (.fwd sS2))

/-- **The sign copy**: the `2t` sign bits of `CTR` onto the scratch `S2`. -/
def gcopyW : HW := .seq (FinalPass.Hash4.wcopyR 15 25 22) (.whr 25 (.seq (.dec 25) gcBodyW))

theorem gcopy_spec (γs : List Bool) (T2 : ℕ) (hT : γs.length = T2) (oldS : List Bool) (σ : HS)
    (hC : ∀ k < T2, readTapeBit (σ.st sCTR) k = γs.getD k false) (hCh : σ.sh sCTR = 0)
    (hS : σ.st sS2 = oldS) (hSh : σ.sh sS2 = 0) (h15 : σ.val 15 = T2) (h22 : σ.val 22 = 0) (h25 : σ.val 25 = 0)
    (hcap : T2 ≤ cap) :
    WExec cap gcopyW σ (wov (σ.seth sCTR T2) sS2 γs oldS) (18 * T2 + 3 + 1 + (T2 * (6 + 4) + 1)) := by
  have s1 := FinalPass.Hash4.wcopyR_spec cap 15 25 22 (by decide) (by decide) (by decide) σ h25 h22
    (by rw [h15]; exact hcap)
  rw [h15] at s1
  let S : ℕ → HS := fun k => (wov (σ.seth sCTR k) sS2 (γs.take k) oldS).setv 25 (T2 - k)
  have hS0 : S 0 = σ.setv 25 T2 := by
    simp only [S, List.take_zero, Nat.sub_zero]
    have : overlay [] oldS = oldS := by simp [overlay]
    hbeq
  have hloop := UnionMachine.Round.wloop cap 25 gcBodyW 6 T2 S (fun k _ => by simp [S, wov]) hcap
    (fun k hk => by
      have hkl : k < γs.length := by omega
      have hb : wbit ((S k).setv 25 (T2 - k - 1)) sCTR = γs[k] := by
        simp only [wbit, S, wov, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          WState.sets_sh, Function.update_apply]
        simp only [show (5 : Fin 24) ≠ 23 by decide, if_false, if_true]
        rw [hC k hk, List.getD_eq_getElem _ _ hkl]
      have hw : ∀ b : Bool, writeTapeBit (((S k).setv 25 (T2 - k - 1)).st sS2) (((S k).setv 25 (T2 - k - 1)).sh sS2) b
          = overlay (γs.take k ++ [b]) oldS := by
        intro b
        simp only [S, wov, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          WState.sets_sh, Function.update_self, Function.update_apply]
        try simp only [show (23 : Fin 24) ≠ 5 by decide, if_false]
        exact overlay_write (γs.take k) oldS b
      have e1 : γs.take (k + 1) = γs.take k ++ [γs[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkl]; rfl
      cases hg : γs[k]
      · rw [hg] at hb e1
        have t1 := WExec.ifsF (P := WM.wr sS2 true) hb (WExec.wr (cap := cap) sS2 false ((S k).setv 25 (T2 - k - 1)))
        have t2 := WExec.fwd (cap := cap) sCTR (((S k).setv 25 (T2 - k - 1)).sets sS2
          (writeTapeBit (((S k).setv 25 (T2 - k - 1)).st sS2) (((S k).setv 25 (T2 - k - 1)).sh sS2) false))
        refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.fwd (cap := cap) sS2 _))) ?_ (le_refl _)
        rw [hw false]
        simp only [S, e1]
        hbeq
      · rw [hg] at hb e1
        have t1 := WExec.ifsT (Q := WM.wr sS2 false) hb (WExec.wr (cap := cap) sS2 true ((S k).setv 25 (T2 - k - 1)))
        have t2 := WExec.fwd (cap := cap) sCTR (((S k).setv 25 (T2 - k - 1)).sets sS2
          (writeTapeBit (((S k).setv 25 (T2 - k - 1)).st sS2) (((S k).setv 25 (T2 - k - 1)).sh sS2) true))
        refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.fwd (cap := cap) sS2 _))) ?_ (le_refl _)
        rw [hw true]
        simp only [S, e1]
        hbeq)
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq s1 hloop) ?_ (le_refl _)
  simp only [S, Nat.sub_self, List.take_of_length_le (show γs.length ≤ T2 by omega)]
  hbeq

end Gcopy

section Records
variable (cap : ℕ)

/-- The records of the first `r` positions. -/
def recsUpTo (ℓ lam : ℕ) (lt : Bool) (γs : List Bool) (ιs : List ℕ) (r : ℕ) : List Bool :=
  (List.range r).flatMap fun i => recBits ℓ (ιs.getD i 0) lam lt (γs.getD i false)

theorem recsUpTo_succ (ℓ lam : ℕ) (lt : Bool) (γs : List Bool) (ιs : List ℕ) (r : ℕ) :
    recsUpTo ℓ lam lt γs ιs (r + 1) = recsUpTo ℓ lam lt γs ιs r ++ recBits ℓ (ιs.getD r 0) lam lt (γs.getD r false) := by
  simp [recsUpTo, List.range_succ, List.flatMap_append]

/-- **The records loop** over the `2t` positions. -/
def recsW : HW := .seq (FinalPass.Hash4.wcopyR 15 25 22) (.whr 25 (.seq (.dec 25) recW))

theorem recs_spec (γs : List Bool) (ιs : List ℕ) (ℓ T2 lam : ℕ) (lt : Bool) (hγ : γs.length = T2)
    (hι : ιs.length = T2) (oldS oldC : List Bool) (σ : HS)
    (hC : σ.st sCTR = ctrWord γs ιs ℓ) (hCh : σ.sh sCTR = T2) (hS : σ.st sS2 = overlay γs oldS) (hSh : σ.sh sS2 = 0)
    (hK : σ.st sCONS = oldC) (hKh : σ.sh sCONS = 0) (h9 : σ.val 9 = lam) (h15 : σ.val 15 = T2) (h16 : σ.val 16 = ℓ)
    (h22 : σ.val 22 = 0) (h25 : σ.val 25 = 0) (h26 : σ.val 26 = 0) (h28 : σ.val 28 = if lt then 1 else 0)
    (hcap : T2 + ℓ + lam ≤ cap) :
    WExec cap recsW σ (wov ((σ.seth sCTR (T2 + T2 * ℓ)).seth sS2 T2) sCONS (recsUpTo ℓ lam lt γs ιs T2) oldC)
      (18 * T2 + 3 + 1 + (T2 * (recCost ℓ lam + 4) + 1)) := by
  have s1 := FinalPass.Hash4.wcopyR_spec cap 15 25 22 (by decide) (by decide) (by decide) σ h25 h22
    (by rw [h15]; omega)
  rw [h15] at s1
  let S : ℕ → HS := fun r => wov (((σ.seth sCTR (T2 + r * ℓ)).seth sS2 r).setv 25 (T2 - r)) sCONS
    (recsUpTo ℓ lam lt γs ιs r) oldC
  have hS0 : S 0 = σ.setv 25 T2 := by
    simp only [S, Nat.zero_mul, Nat.add_zero, Nat.sub_zero]
    have e0 : recsUpTo ℓ lam lt γs ιs 0 = [] := rfl
    have : overlay [] oldC = oldC := by simp [overlay]
    rw [e0]
    hbeq
  have hloop := UnionMachine.Round.wloop cap 25 recW (recCost ℓ lam) T2 S (fun k _ => by simp [S, wov]) (by omega)
    (fun r hr => by
      set σ' := ((σ.seth sCTR (T2 + r * ℓ)).seth sS2 r).setv 25 (T2 - r - 1) with hσ'
      have eτ : (S r).setv 25 (T2 - r - 1) = wov σ' sCONS (recsUpTo ℓ lam lt γs ιs r) oldC := by
        simp only [S, σ']; hbeq
      rw [eτ]
      have hg : readTapeBit (σ'.st sS2) (σ'.sh sS2) = γs.getD r false := by
        simp only [σ', WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hS]
        simp only [readTapeBit, overlay]
        rw [List.getD_append _ _ _ _ (by omega)]
      have t := recW_spec cap ℓ (ιs.getD r 0) lam lt (γs.getD r false) (recsUpTo ℓ lam lt γs ιs r) oldC σ'
        (T2 + r * ℓ)
        (fun m hm => by
          simp only [σ', WState.setv_st, WState.seth_st, hC]
          have := ctrWord_field γs ιs ℓ r m (by omega) hm
          rw [hγ] at this; exact this)
        (by simp [σ']) hg (by simp [σ', h9]) (by simp [σ', h16]) (by simp [σ', h22]) (by simp [σ', h26])
        (by simp [σ', h28]) (by omega)
      refine WExec.cast cap t ?_ (le_refl _)
      simp only [S, σ', recsUpTo_succ]
      have e2 : T2 + r * ℓ + ℓ = T2 + (r + 1) * ℓ := by ring
      rw [e2]
      hbeq)
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq s1 hloop) ?_ (le_refl _)
  simp only [S, Nat.sub_self]
  hbeq

end Records

section ConsW
variable (cap : ℕ)

/-- The records program's loads: `λ`, `J`, `2t`, `ℓ₀`. -/
def ldC : List (Fin 24 × Fin 40) := [(sLAM, 9), (sJJ, 10), (sTT, 15), (sLL, 16)]

/-- **The records program** (WM1b): loads, the level flag, the sign copy, the records, the end mark, the clears. -/
def consW : HW := .seq (loadsW 26 ldC) (.seq (PrimAsm.UnaryArith.gtFlagW gR) (.seq gcopyW
  (.seq (FinalPass.Hash4.wcopyR 15 25 22) (.seq (WM.rewind sS2 25) (.seq recsW (.seq (.wr sCONS false)
    (clearsW (List.finRange 40))))))))

def consBound (lam J T2 ℓ : ℕ) : ℕ :=
  4 * (16 * (lam + J + T2 + ℓ) + 15) + 1 + (30 * J + 30 * lam + 20) + 1 + (18 * T2 + 3 + 1 + (T2 * (6 + 4) + 1)) + 1 +
    (18 * T2 + 3) + 1 + (5 * T2 + 1) + 1 + (18 * T2 + 3 + 1 + (T2 * (recCost ℓ lam + 4) + 1)) + 1 + 1 + 1 +
    40 * (3 * (lam + J + T2 + ℓ + 1) + 2)

theorem consW_spec (γs : List Bool) (ιs : List ℕ) (ℓ T2 lam J : ℕ) (hγ : γs.length = T2) (hι : ιs.length = T2)
    (oldC oldS : List Bool) (σ : HS) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0)
    (hC : σ.st sCTR = ctrWord γs ιs ℓ) (hLAM : σ.st sLAM = unary lam (J + 1)) (hJJ : σ.st sJJ = List.replicate J true)
    (hTT : σ.st sTT = List.replicate T2 true) (hLL : σ.st sLL = List.replicate ℓ true) (hK : σ.st sCONS = oldC)
    (hS : σ.st sS2 = oldS) (hcap : lam + J + T2 + ℓ + 2 ≤ cap) :
    ∃ τ c, c ≤ consBound lam J T2 ℓ ∧ WExec cap consW σ τ c ∧
      τ.st = Function.update (Function.update σ.st sS2 (overlay γs oldS)) sCONS
        (overlay (recsUpTo ℓ lam (decide (lam < J)) γs ιs T2 ++ [false]) oldC) ∧ τ.val = (fun _ => 0) ∧
      τ.cell = σ.cell := by
  set lt := decide (lam < J) with hlt
  let vs : Fin 24 → ℕ := ![0, 0, 0, 0, 0, 0, lam, 0, 0, 0, 0, 0, 0, 0, 0, T2, ℓ, J, 0, 0, 0, 0, 0, 0]
  let rs : Fin 24 → List Bool := ![[], [], [], [], [], [], List.replicate (J + 1 - 1 - lam) false,
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
  have gz : ∀ n : ℕ, (List.replicate n false).getD 0 false = false := fun n => by cases n <;> rfl
  have hmem : ∀ y ∈ ldC, σ.st y.1 = List.replicate (vs y.1) true ++ rs y.1 ∧ (rs y.1).getD 0 false = false ∧
      σ.sh y.1 = 0 := by
    intro y hy
    simp only [ldC, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨by rw [hLAM]; rfl, gz _, hsh _⟩
    · exact ⟨by rw [hJJ]; exact (List.append_nil _).symm, rfl, hsh _⟩
    · exact ⟨by rw [hTT]; exact (List.append_nil _).symm, rfl, hsh _⟩
    · exact ⟨by rw [hLL]; exact (List.append_nil _).symm, rfl, hsh _⟩
  have hsum : (ldC.map fun y => vs y.1).sum = lam + (J + (T2 + (ℓ + 0))) := rfl
  have s1 := loadsW_spec cap 26 vs rs ldC σ (by decide) (hv 26) hmem
    (fun r => by have := ldv_le_sum vs ldC r; rw [hsum] at this; rw [hv r]; omega)
  have hlc : ldCost vs ldC ≤ 4 * (16 * (lam + J + T2 + ℓ) + 15) := by
    have hb : ∀ y ∈ ldC, vs y.1 ≤ lam + J + T2 + ℓ := by
      intro y hy
      simp only [ldC, List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · show lam ≤ _; omega
      · show J ≤ _; omega
      · show T2 ≤ _; omega
      · show ℓ ≤ _; omega
    have := ldCost_le vs _ ldC hb
    have hl : ldC.length = 4 := rfl
    rw [hl] at this; exact this
  set σ1 : HS := ⟨σ.sh, σ.st, fun r => σ.val r + ldv vs ldC r, σ.cell⟩ with hσ1
  have e1 : ∀ r, σ1.val r = ldv vs ldC r := fun r => by simp [σ1, hv]
  have s2 := PrimAsm.UnaryArith.gtFlagW_spec cap gR σ1 (show σ1.val 28 = 0 by rw [e1]; rfl)
    (show σ1.val 29 = 0 by rw [e1]; rfl) (show σ1.val 30 = 0 by rw [e1]; rfl) (show σ1.val 31 = 0 by rw [e1]; rfl)
    (show σ1.val 10 ≤ cap by rw [e1]; show J + 0 ≤ cap; omega)
    (show σ1.val 9 ≤ cap by rw [e1]; show lam + 0 ≤ cap; omega) (by omega)
  have f9 : σ1.val (gR 1) = lam := show σ1.val 9 = lam by rw [e1]; rfl
  have f10 : σ1.val (gR 0) = J := show σ1.val 10 = J by rw [e1]; rfl
  rw [f9, f10] at s2
  set σ2 := σ1.setv (gR 2) (if lam < J then 1 else 0) with hσ2
  have e2 : ∀ r : Fin 40, σ2.val r = if r = 28 then (if lam < J then 1 else 0) else ldv vs ldC r := by
    intro r; simp only [σ2, WState.setv_val, Function.update_apply, e1]; rfl
  have s3 := gcopy_spec cap γs T2 hγ oldS σ2
    (fun k hk => by
      have := ctrWord_sign γs ιs ℓ k (by omega)
      simpa [σ2, σ1, hC] using this)
    (by simp [σ2, σ1, hsh]) (by simp [σ2, σ1, hS]) (by simp [σ2, σ1, hsh])
    (by rw [e2, if_neg (by decide)]; rfl) (by rw [e2, if_neg (by decide)]; rfl) (by rw [e2, if_neg (by decide)]; rfl)
    (by omega)
  set σ3 := wov (σ2.seth sCTR T2) sS2 γs oldS with hσ3
  have v3 : ∀ r, σ3.val r = σ2.val r := fun r => rfl
  have s4 := FinalPass.Hash4.wcopyR_spec cap 15 25 22 (by decide) (by decide) (by decide) σ3
    (by rw [v3, e2, if_neg (by decide)]; rfl) (by rw [v3, e2, if_neg (by decide)]; rfl)
    (by rw [v3, e2, if_neg (by decide)]; show T2 + 0 ≤ cap; omega)
  have v315 : σ3.val 15 = T2 := by rw [v3, e2, if_neg (by decide)]; rfl
  rw [v315] at s4
  have s5 := wrewind_spec cap sS2 25 T2 (σ3.setv 25 T2) (by simp) (by simp; omega)
  set σ5 := ((σ3.setv 25 T2).setv 25 0).seth sS2 ((σ3.setv 25 T2).sh sS2 - T2) with hσ5
  have v5 : ∀ r, σ5.val r = σ2.val r := by
    intro r; simp only [σ5, WState.seth_val, WState.setv_val, Function.update_apply]
    split_ifs with h
    · subst h; rw [e2, if_neg (by decide)]; rfl
    · rfl
  have s6 := recs_spec cap γs ιs ℓ T2 lam lt hγ hι oldS oldC σ5
    (by simp [σ5, σ3, wov, σ2, σ1, hC]) (by simp [σ5, σ3, wov, σ2, σ1])
    (by simp [σ5, σ3, wov]) (by simp [σ5, σ3, wov, hγ]) (by simp [σ5, σ3, wov, σ2, σ1, hK])
    (by simp [σ5, σ3, wov, σ2, σ1, hsh])
    (by rw [v5, e2, if_neg (by decide)]; rfl) (by rw [v5, e2, if_neg (by decide)]; rfl)
    (by rw [v5, e2, if_neg (by decide)]; rfl) (by rw [v5, e2, if_neg (by decide)]; rfl)
    (by rw [v5, e2, if_neg (by decide)]; rfl) (by rw [v5, e2, if_neg (by decide)]; rfl)
    (by rw [v5, e2, if_pos rfl, hlt]; by_cases h : lam < J <;> simp [h]) (by omega)
  set σ6 := wov ((σ5.seth sCTR (T2 + T2 * ℓ)).seth sS2 T2) sCONS (recsUpTo ℓ lam lt γs ιs T2) oldC with hσ6
  have s7 := WExec.wr (cap := cap) sCONS false σ6
  have hw7 : writeTapeBit (σ6.st sCONS) (σ6.sh sCONS) false = overlay (recsUpTo ℓ lam lt γs ιs T2 ++ [false]) oldC := by
    simp only [σ6, wov, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh, Function.update_self]
    exact overlay_write _ _ _
  rw [hw7] at s7
  set σ7 := σ6.sets sCONS (overlay (recsUpTo ℓ lam lt γs ιs T2 ++ [false]) oldC) with hσ7
  have hv7 : ∀ r, σ7.val r ≤ lam + J + T2 + ℓ + 1 := by
    intro r
    have hld := ldv_le_sum vs ldC r
    rw [hsum] at hld
    have : σ7.val r = σ2.val r := by
      simp only [σ7, σ6, wov, WState.sets_val, WState.seth_val]; exact v5 r
    rw [this, e2]
    split_ifs <;> omega
  have s8 := clearsW_spec cap (List.finRange 40) σ7 (List.nodup_finRange 40) (fun r => by have := hv7 r; omega)
  have hcl := clCost_le σ7.val _ hv7 (List.finRange 40)
  rw [List.length_finRange] at hcl
  refine ⟨_, _, ?_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8)))))), ?_, ?_, ?_⟩
  · unfold consBound; omega
  · funext j
    simp only [σ7, σ6, σ5, σ3, σ2, σ1, wov, WState.sets_st, WState.setv_st, WState.seth_st, Function.update_apply]
    split_ifs <;> simp_all
  · funext r; simp
  · rfl

end ConsW

section Link

/-- The cell's constraint list (`consOf` on lists): the positions and the targets `γ_r·2^λ` (moment level). -/
def consL (lam J : ℕ) (γs : List Bool) (ιs : List ℕ) : List (ℕ × ℕ) :=
  (List.range ιs.length).map fun r => (ιs.getD r 0, if lam < J ∧ γs.getD r false = true then 2 ^ lam else 0)

/-- The cell's constraint width. -/
def kOfL (lam J : ℕ) : ℕ := if lam < J then lam + 1 else J

theorem binary_zero' : ∀ w : ℕ, binary w 0 = List.replicate w false
  | 0 => rfl
  | w + 1 => by simp [SignedSortKey.binary, binary_zero' w, List.replicate_succ]

theorem binary_pow : ∀ lam : ℕ, binary (lam + 1) (2 ^ lam) = List.replicate lam false ++ [true]
  | 0 => rfl
  | lam + 1 => by
    have h1 : 2 ^ (lam + 1) % 2 = 0 := by rw [pow_succ]; simp
    have h2 : 2 ^ (lam + 1) / 2 = 2 ^ lam := by rw [pow_succ]; simp
    show (2 ^ (lam + 1) % 2 == 1) :: binary (lam + 1) (2 ^ (lam + 1) / 2) = _
    rw [h1, h2, binary_pow lam]
    simp [List.replicate_succ]

theorem pairs_rep_false (n : ℕ) : pairs (List.replicate n false) = PrimAsm.FiltRec.reps n [true, false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairs] at ih ⊢
    rw [List.replicate_succ', List.flatMap_append, ih, PrimAsm.FiltRec.reps_succ]
    rfl

theorem tgtBits_eq (lam J : ℕ) (g : Bool) (hlJ : lam ≤ J) :
    tgtBits lam (decide (lam < J)) g = frame (binary (kOfL lam J) (if lam < J ∧ g = true then 2 ^ lam else 0)) := by
  unfold tgtBits kOfL
  by_cases hlt : lam < J
  · simp only [hlt, decide_true, if_true, true_and]
    have eb : binary (lam + 1) (if g = true then 2 ^ lam else 0) = List.replicate lam false ++ [g] := by
      cases g
      · simp only [Bool.false_eq_true, if_false, binary_zero', List.replicate_succ']
      · simp only [if_true, binary_pow]
    rw [eb, frame_pairs, pairs, List.flatMap_append, ← pairs, pairs_rep_false]
    simp
  · have heq : lam = J := by omega
    subst heq
    simp only [hlt, decide_false, Bool.false_eq_true, if_false, false_and, binary_zero', frame_pairs,
      pairs_rep_false]
    simp

theorem recs_consTape (ℓ lam J : ℕ) (γs : List Bool) (ιs : List ℕ) (hlJ : lam ≤ J) (stale : List Bool) :
    recsUpTo ℓ lam (decide (lam < J)) γs ιs ιs.length ++ false :: stale =
      SeedFix.consTape ℓ (kOfL lam J) (consL lam J γs ιs) stale := by
  unfold recsUpTo SeedFix.consTape consL
  rw [List.flatMap_map]
  congr 1
  refine List.flatMap_congr (fun r _ => ?_)
  simp only [recBits, SeedFix.consRec, tgtBits_eq lam J _ hlJ]
  simp

end Link

end NearCubicWires.WireExponent3_5.PrimT.HbM
