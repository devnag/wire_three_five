import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Proof.Wire_3_5.Primitive.Writers.UnaryPow

/-! # C6 front, the C1 dock: one-bit transducers over a field's logical bits

The integer increment of C1's request writer reads a field's bits once or twice and writes bits as it goes (a carry,
a borrow, a flag). This module is the generic loop: a one-bit transducer `g` (**`Mealy`**: from the read bit and the
state bit, the new state and the emitted bits) run over the next `|bs|` logical bits of a framed or raw source (PA's
`enc ε`), the state in a register, the emitted bits appended framed (PA's `emitPair`):
* `run g c bs` (the state and the output), `run_append`;
* **`loop_spec`**: the loop's exact final state (source head past the bits, output extended, counter `0`, state
  register `run`'s state);
* **`ones_spec`** (append `1^k` framed), **`rew_spec`** (move the source head back by `k` logical bits).

Paper quantity: none (bit-serial arithmetic on the gate thresholds of C1's request, P3:1326-1330). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.BitLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- **A one-bit transducer**: from the read bit and the state, the new state and the emitted bits. -/
abbrev Mealy := Bool → Bool → Bool × List Bool

/-- The transducer run over a bit list: the final state and the emitted bits. -/
def run (g : Mealy) : Bool → List Bool → Bool × List Bool
  | c, [] => (c, [])
  | c, b :: t => ((run g (g b c).1 t).1, (g b c).2 ++ (run g (g b c).1 t).2)

theorem run_append (g : Mealy) : ∀ (c : Bool) (l : List Bool) (b : Bool),
    run g c (l ++ [b]) = ((g b (run g c l).1).1, (run g c l).2 ++ (g b (run g c l).1).2)
  | c, [], b => by simp [run]
  | c, a :: t, b => by
    have ih := run_append g (g a c).1 t b
    simp only [List.cons_append, run, ih, List.append_assoc]

theorem run_out_length (g : Mealy) (hg : ∀ b c, (g b c).2.length ≤ 1) :
    ∀ (c : Bool) (l : List Bool), (run g c l).2.length ≤ l.length
  | c, [] => by simp [run]
  | c, a :: t => by
    have := run_out_length g hg (g a c).1 t
    have := hg a c
    simp only [run, List.length_append, List.length_cons]
    omega

theorem marks_nil : marks [] = [] := rfl

theorem marks_cons (b : Bool) (l : List Bool) : marks (b :: l) = true :: b :: marks l := rfl

variable {ns nr : ℕ} (cap : ℕ)

/-- Emit a list of bits, framed, one `emitPair` each. -/
def emitL (o : Fin (ns + 1)) (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | x :: t => .seq (emitPair o OP x) (emitL o OP t)

theorem emitL_spec (o : Fin (ns + 1)) (OP : Fin nr) :
    ∀ (l : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length → σ.val OP + 2 * l.length ≤ cap →
      WExec cap (emitL o OP l) σ (appendO σ o OP (marks l)) (16 * l.length)
  | [], σ, _, _ => by
    rw [show marks [] = [] from rfl, appendO_nil]
    exact WExec.mono (WExec.skip σ) (by simp)
  | x :: t, σ, ho, hc => by
    have h1 := emitPair_spec cap o OP x σ ho (by simp at hc; omega)
    have h2 := emitL_spec o OP t (appendO σ o OP [true, x]) (by simp [ho]) (by simp at hc ⊢; omega)
    rw [appendO_append] at h2
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
    rfl

/-- Set a flag register from `c` to `v`. -/
def setC (C : Fin nr) : Bool → Bool → WM ns nr
  | false, true => .inc C
  | true, false => .dec C
  | _, _ => .skip

theorem setC_spec (C : Fin nr) (c v : Bool) (σ : WState ns nr) (hC : σ.val C = c.toNat) (hcap : 1 ≤ cap) :
    WExec cap (setC C c v) σ (σ.setv C v.toNat) 3 := by
  cases c <;> cases v
  · exact WExec.cast cap (WExec.skip σ) (by rw [show false.toNat = σ.val C by simp [hC]]; exact (wsetv_same σ C).symm)
      (by omega)
  · have h := WExec.inc (cap := cap) C σ (by simp at hC; omega)
    exact WExec.cast cap h (by simp [hC]) le_rfl
  · have h := WExec.dec (cap := cap) C σ (by simp at hC; omega)
    exact WExec.cast cap h (by simp [hC]) (by omega)
  · exact WExec.cast cap (WExec.skip σ) (by rw [show true.toNat = σ.val C by simp [hC]]; exact (wsetv_same σ C).symm)
      (by omega)

section Loop
variable (g : Mealy) (ε : Bool) (s o : Fin (ns + 1)) (T C OP : Fin nr)

/-- The leaf at read bit `b` and state `c`: emit, then set the state. -/
def leaf (b c : Bool) : WM ns nr := .seq (emitL o OP (g b c).2) (setC C c (g b c).1)

/-- One bit: to its payload cell, the four-way leaf, to the next bit. -/
def body : WM ns nr :=
  .seq (.seq (.seq (.dec T) (preE ε s))
    (.ifs s (.ifr C (leaf g o C OP true true) (leaf g o C OP true false))
      (.ifr C (leaf g o C OP false true) (leaf g o C OP false false)))) (.fwd s)

/-- **The transducer loop** over the next `T` logical bits. -/
def loop : WM ns nr := .whr T (body g ε s o T C OP)

/-- The state after `k` bits. -/
def st (σ : WState ns nr) (c : Bool) (bs : List Bool) (k : ℕ) : WState ns nr :=
  (((appendO σ o OP (marks (run g c (bs.take k)).2)).seth s (σ.sh s + stp ε * k)).setv T (bs.length - k)).setv C
    (run g c (bs.take k)).1.toNat

theorem loop_spec (hg : ∀ b c, (g b c).2.length ≤ 1) (hso : s ≠ o) (hTC : T ≠ C) (hTO : T ≠ OP) (hCO : C ≠ OP)
    (σ : WState ns nr) (c : Bool) (bs : List Bool)
    (hread : ∀ k, k < bs.length → readTapeBit (σ.st s) (σ.sh s + stp ε * k + off ε) = bs.getD k false)
    (hT : σ.val T = bs.length) (hC : σ.val C = c.toNat) (ho : σ.sh o = (σ.st o).length)
    (hcap : σ.val OP + 2 * bs.length + bs.length + 2 ≤ cap) :
    WExec cap (loop g ε s o T C OP) σ (st g ε s o T C OP σ c bs bs.length) (bs.length * (40 + 2) + 1) := by
  have hTo : T ≠ OP := hTO
  have hs := stp_eq ε
  have hoff := off_le ε
  have e0 : st g ε s o T C OP σ c bs 0 = σ := by
    apply WState.eq
    · funext j; by_cases hj : j = s
      · subst hj; simp [st, Function.update_apply, Ne.symm hso]
      · by_cases hjo : j = o
        · subst hjo; simp [st, run, Function.update_apply, hj, marks_nil]
        · simp [st, Function.update_apply, hj, hjo]
    · funext j; by_cases hjo : j = o
      · subst hjo; simp [st, run, marks_nil]
      · simp [st, Function.update_apply, hjo]
    · funext r
      by_cases hr : r = C
      · subst hr; simp [st, run, hC]
      · by_cases hr2 : r = T
        · subst hr2; simp [st, hr, hT]
        · by_cases hr3 : r = OP
          · subst hr3; simp [st, run, hr, hr2, marks_nil]
          · simp [st, Function.update_apply, hr, hr2, hr3]
    · simp [st]
  have key := PrimAsm.UnaryPow.flagLoop cap T (body g ε s o T C OP) 40 bs.length (st g ε s o T C OP σ c bs)
    (fun k hk => by simp [st, Function.update_apply, hTC, hTo]; omega)
    (by simp [st, Function.update_apply, hTC])
    (fun k hk => by
      set τ := st g ε s o T C OP σ c bs k with hτ
      obtain ⟨cs, hcs⟩ : ∃ cs, cs = (run g c (bs.take k)).1 := ⟨_, rfl⟩
      obtain ⟨b, hb0⟩ : ∃ b, b = bs.getD k false := ⟨_, rfl⟩
      have hτT : τ.val T = bs.length - k := by simp [τ, st, Function.update_apply, hTC, hTo]
      have hτC : τ.val C = cs.toNat := by simp [τ, st, hcs]
      have hτo : τ.sh o = (τ.st o).length := by simp [τ, st, Function.update_apply, Ne.symm hso, ho]
      have hτs : τ.sh s = σ.sh s + stp ε * k := by simp [τ, st]
      have hτst : τ.st s = σ.st s := by simp [τ, st, Function.update_apply, hso]
      have hlo := run_out_length g hg c (bs.take k)
      have hτOP : τ.val OP = σ.val OP + 2 * (run g c (bs.take k)).2.length := by
        simp [τ, st, Function.update_apply, hTo.symm, hCO.symm]
      have h1 := WExec.dec (cap := cap) T τ (by rw [hτT]; omega)
      set τ1 := τ.setv T (τ.val T - 1) with hτ1
      have h2 := preE_spec cap ε s τ1
      set τ2 := τ1.seth s (τ1.sh s + off ε) with hτ2
      have hbit : wbit τ2 s = b := by
        simp only [wbit, τ2, τ1, WState.seth_st, WState.setv_st, WState.seth_sh, Function.update_self,
          WState.setv_sh, hτs, hτst]
        rw [hb0]; exact hread k hk
      have hτ2C : τ2.val C = cs.toNat := by simp [τ2, τ1, Function.update_apply, Ne.symm hTC, hτC]
      have hτ2o : τ2.sh o = (τ2.st o).length := by simp [τ2, τ1, Function.update_apply, Ne.symm hso, hτo]
      have hτ2OP : τ2.val OP = τ.val OP := by simp [τ2, τ1, Function.update_apply, hTo.symm]
      have hgl := hg b cs
      have hleaf := WExec.seq (emitL_spec cap o OP (g b cs).2 τ2 hτ2o (by
          rw [hτ2OP, hτOP]
          have : (run g c (bs.take k)).2.length ≤ k := le_trans hlo (by simp)
          omega))
        (setC_spec cap C cs (g b cs).1 (appendO τ2 o OP (marks (g b cs).2))
          (by simp [Function.update_apply, hCO, hτ2C]) (by omega))
      have hbr : WExec cap (.ifs s (.ifr C (leaf g o C OP true true) (leaf g o C OP true false))
          (.ifr C (leaf g o C OP false true) (leaf g o C OP false false))) τ2
          ((appendO τ2 o OP (marks (g b cs).2)).setv C (g b cs).1.toNat)
          (16 * (g b cs).2.length + 1 + 3 + 1 + 1) := by
        cases hb : b <;> cases hcs' : cs
        · rw [hb, hcs'] at hleaf
          exact WExec.ifsF (by rw [hbit, hb]) (WExec.ifrF (by rw [hτ2C, hcs']; rfl) hleaf)
        · rw [hb, hcs'] at hleaf
          exact WExec.ifsF (by rw [hbit, hb]) (WExec.ifrT (by rw [hτ2C, hcs']; simp) hleaf)
        · rw [hb, hcs'] at hleaf
          exact WExec.ifsT (by rw [hbit, hb]) (WExec.ifrF (by rw [hτ2C, hcs']; rfl) hleaf)
        · rw [hb, hcs'] at hleaf
          exact WExec.ifsT (by rw [hbit, hb]) (WExec.ifrT (by rw [hτ2C, hcs']; simp) hleaf)
      have h4 := WExec.fwd (cap := cap) s
        ((appendO τ2 o OP (marks (g b cs).2)).setv C (g b cs).1.toNat)
      have hall := WExec.seq (WExec.seq (WExec.seq h1 h2) hbr) h4
      have hgb := hg b cs
      refine WExec.cast cap hall ?_ (by omega)
      have htk : bs.take (k + 1) = bs.take k ++ [b] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, hb0]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      have hrun := run_append g c (bs.take k) b
      rw [← htk, ← hcs] at hrun
      apply WState.eq
      · funext j; by_cases hj : j = s
        · subst hj; simp [st, τ2, τ1, τ, Function.update_apply, hso, Ne.symm hso, Nat.mul_succ]; omega
        · by_cases hjo : j = o
          · subst hjo; simp [st, τ2, τ1, τ, Function.update_apply, hj, hrun, List.length_append]; ring
          · simp [st, τ2, τ1, τ, Function.update_apply, hj, hjo]
      · funext j; by_cases hjo : j = o
        · subst hjo; simp [st, τ2, τ1, τ, Function.update_apply, hso, hrun, List.append_assoc]
        · simp [st, τ2, τ1, τ, Function.update_apply, hjo]
      · funext r
        by_cases hr : r = C
        · subst hr; simp [st, τ2, τ1, τ, Function.update_apply, hrun]
        · by_cases hr2 : r = T
          · subst hr2; simp [st, τ2, τ1, τ, Function.update_apply, hr, hTo]; omega
          · by_cases hr3 : r = OP
            · subst hr3; simp [st, τ2, τ1, τ, Function.update_apply, hr, hr2, hrun, List.length_append]; ring
            · simp [st, τ2, τ1, τ, Function.update_apply, hr, hr2, hr3]
      · simp [st, τ2, τ1, τ])
  rw [e0] at key
  exact key

end Loop

/-- Append `1^k` framed, counting down `T`. -/
def ones (o : Fin (ns + 1)) (T OP : Fin nr) : WM ns nr := .whr T (.seq (.dec T) (emitPair o OP true))

theorem ones_spec (o : Fin (ns + 1)) (T OP : Fin nr) (hTO : T ≠ OP) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val T = k → σ.sh o = (σ.st o).length → σ.val OP + 2 * k + k ≤ cap →
      WExec cap (ones o T OP) σ ((appendO σ o OP (marks (List.replicate k true))).setv T 0) (20 * k + 1)
  | 0, σ, hk, _, _ => by
    have e : (appendO σ o OP (marks (List.replicate 0 true))).setv T 0 = σ := by
      rw [show marks (List.replicate 0 true) = [] from rfl, appendO_nil, ← hk, wsetv_same]
    rw [e]; exact WExec.whrF hk
  | k + 1, σ, hk, ho, hc => by
    have h1 := WExec.dec (cap := cap) T σ (by omega)
    have h2 := emitPair_spec cap o OP true (σ.setv T (σ.val T - 1)) (by simp [ho]) (by simp [Ne.symm hTO]; omega)
    have e1 : (appendO (σ.setv T (σ.val T - 1)) o OP [true, true]).val OP = σ.val OP + 2 := by
      simp [Function.update_apply, Ne.symm hTO]
    have e2 : (appendO (σ.setv T (σ.val T - 1)) o OP [true, true]).val T = k := by
      simp [Function.update_apply, hTO, hk]
    have ih := ones_spec o T OP hTO k (appendO (σ.setv T (σ.val T - 1)) o OP [true, true]) e2
      (by simp [ho]) (by rw [e1]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) ih) ?_ (by omega)
    have hm : marks (List.replicate (k + 1) true) = [true, true] ++ marks (List.replicate k true) := by
      rw [List.replicate_succ, marks_cons]; rfl
    rw [hm, ← appendO_append, appendO_setv _ _ _ _ hTO]
    apply WState.eq
    · simp
    · simp
    · funext r; by_cases hr : r = T
      · subst hr; simp
      · simp [Function.update_apply, hr, Ne.symm hTO]
    · simp

/-- One logical bit back. -/
def bwdE (ε : Bool) (s : Fin (ns + 1)) : WM ns nr := if ε then .seq (.bwd s) (.bwd s) else .bwd s

/-- Move the source head back by `T` logical bits. -/
def rew (ε : Bool) (s : Fin (ns + 1)) (T : Fin nr) : WM ns nr := .whr T (.seq (.dec T) (bwdE ε s))

theorem rew_spec (ε : Bool) (s : Fin (ns + 1)) (T : Fin nr) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val T = k → stp ε * k ≤ σ.sh s → σ.val T ≤ cap →
      WExec cap (rew ε s T) σ ((σ.setv T 0).seth s (σ.sh s - stp ε * k)) (7 * k + 1)
  | 0, σ, hk, _, _ => by
    have e : (σ.setv T 0).seth s (σ.sh s - stp ε * 0) = σ := WState.eq (by simp) rfl (by rw [← hk]; simp) rfl
    rw [e]; exact WExec.whrF hk
  | k + 1, σ, hk, hs, hc => by
    have h1 := WExec.dec (cap := cap) T σ hc
    have h2 : WExec cap (bwdE ε s) (σ.setv T (σ.val T - 1))
        ((σ.setv T (σ.val T - 1)).seth s ((σ.setv T (σ.val T - 1)).sh s - stp ε)) 3 := by
      cases ε
      · exact WExec.mono (WExec.cast cap (WExec.bwd s _) (by simp [stp]) le_rfl) (by omega)
      · have a := WExec.bwd (cap := cap) s (σ.setv T (σ.val T - 1))
        have b := WExec.bwd (cap := cap) s ((σ.setv T (σ.val T - 1)).seth s ((σ.setv T (σ.val T - 1)).sh s - 1))
        refine WExec.cast cap (WExec.seq a b) ?_ (by omega)
        apply WState.eq
        · funext j; by_cases hj : j = s
          · subst hj; simp [stp]; omega
          · simp [Function.update_apply, hj]
        · rfl
        · rfl
        · rfl
    have hsk : stp ε * (k + 1) = stp ε * k + stp ε := Nat.mul_succ _ _
    have ih := rew_spec ε s T k ((σ.setv T (σ.val T - 1)).seth s ((σ.setv T (σ.val T - 1)).sh s - stp ε))
      (by simp; omega) (by simp only [WState.seth_sh, WState.setv_sh, Function.update_self]; omega)
      (by simp; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) ih) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = s
      · subst hj; simp; omega
      · simp [Function.update_apply, hj]
    · rfl
    · funext r; by_cases hr : r = T
      · subst hr; simp
      · simp [Function.update_apply, hr]
    · rfl

end NearCubicWires.WireExponent3_5.UnionMachine.BitLoop
