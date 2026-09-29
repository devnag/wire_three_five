import Proof.Wire_3_5.UnionMachine.RadTrunc
import Proof.Wire_3_5.UnionMachine.EwKit

/-! # RADIX, stage 5a (6): the truncation program and the digit step's register pieces (P3:2604)

Digit `d`'s table word is the table word at `G` with every row cut to its first `L_d` bits (`RadTrunc.rowsOf_take`).
**`truncP`** reads the table word at `G` in place (position counter `SP`, rewound after) and appends the cut table
word to another stream: the modulus field, the record loop (`RadTrunc.recLoop_spec`), the closing `false`.

* `levelWord_eq`, `lw_len`: the table word as the record loop's input;
* **`truncP_spec`**: `appendO σ O OP (levelWord M J W (fun j => (row j).take L))`;
* `fwdN` / **`fwdN_spec`**: `n` cells forward, consuming the count;
* `add4` / `add4_spec`, `capW` / **`capW_spec`**: `V := 4·(A + B + 1)` (the block writer's `capC D L_d`);
* `glW` / **`glW_spec`**: `Gl := G − L`.

Paper quantity of the main type: the fixed hash's level table at the digit's population size (the list data's rows). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadTrunc2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.FinalPass.ListEval NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.UnionMachine.RadFields
open NearCubicWires.WireExponent3_5.UnionMachine.RadWin NearCubicWires.WireExponent3_5.UnionMachine.RadTrunc

variable {ns nr : ℕ} (cap : ℕ)

theorem levelWord_eq (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) :
    levelWord M J W row =
      unary M ++ ((levels J).flatMap (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row) ++ [false]) := by
  unfold levelWord
  rw [List.append_assoc]
  rfl

theorem lw_len (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) :
    (levelWord M J W row).length =
      (M + 1) + ((levels J).flatMap (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length + 1 := by
  rw [levelWord_eq]
  simp only [List.length_append, unary, List.length_replicate, List.length_singleton]
  omega

/-- **Digit `d`'s table word**: the modulus field, the records with their rows cut (by `Lr`, `GLr`), the closing
`false`, the source rewound by `SP`. -/
def truncP (O S : Fin (ns + 1)) (OP SP K T Lr GLr : Fin nr) : WM ns nr :=
  .seq (copyUn O S OP SP) (.seq (recLoop O S OP SP K T Lr GLr) (.seq (emitW O OP [false])
    (.seq (WM.fwdC S SP) (WM.rewind S SP))))

/-- The truncation's cost (`k` the source table word's length). -/
def truncCost (M : ℕ) (a b : ℕ → ℕ) (L G : ℕ) (js : List ℕ) (k : ℕ) : ℕ :=
  (16 * M + 17) + 1 + (loopCost a b L G js + 1 + (8 + 1 + (5 + 1 + (5 * k + 1))))

theorem truncP_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP K T Lr GLr : Fin nr)
    (hd : [OP, SP, K, T, Lr, GLr].Nodup) (σ : WState ns nr) (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool)
    (L G : ℕ) (rest : List Bool) (hLG : L ≤ G) (hrow : ∀ j, (row j).length = G)
    (hrd : (σ.st S).drop (σ.sh S) = levelWord M J W row ++ rest) (ho : σ.sh O = (σ.st O).length)
    (hK : σ.val K = 0) (hT : σ.val T = 0) (hLr : σ.val Lr = L) (hGL : σ.val GLr = G - L) (hSP : σ.val SP = 0)
    (hc : σ.val OP + (levelWord M J W (fun j => (row j).take L)).length ≤ cap)
    (hs : (levelWord M J W row).length ≤ cap) :
    WExec cap (truncP O S OP SP K T Lr GLr) σ (appendO σ O OP (levelWord M J W (fun j => (row j).take L)))
      (truncCost M (fun j => pow (topW J W j)) (fun j => topW J W j) L G (levels J) (levelWord M J W row).length) := by
  have lX := lw_len M J W row
  have lY := lw_len M J W (fun j => (row j).take L)
  have lu : (unary M).length = M + 1 := by simp [unary]
  have hd1 : (σ.st S).drop (σ.sh S) = unary M ++ ((levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row) ++ (false :: rest)) := by
    rw [hrd, levelWord_eq]; simp [List.append_assoc]
  have hd2 : (σ.st S).drop (σ.sh S + (M + 1)) = (levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row) ++ (false :: rest) := by
    rw [← lu]; exact dropAppend hd1
  have f1 : σ.val OP + M + 1 ≤ cap := by omega
  have f2 : σ.val SP + M + 1 < cap := by omega
  have f3 : σ.val OP + (unary M).length + ((levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) fun j => (row j).take L)).length ≤ cap := by omega
  have f4 : σ.val SP + (M + 1) + ((levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length < cap := by omega
  have f5 : σ.val OP + (unary M ++ (levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) fun j => (row j).take L)).length + 1 ≤ cap := by
    rw [List.length_append]; omega
  have f6 : σ.val SP + (M + 1 + ((levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length) < cap := by omega
  have f7 : σ.val SP + (M + 1 + ((levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length + 1) ≤ cap := by omega
  have fk : M + 1 + ((levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length + 1 = (levelWord M J W row).length := by
    omega
  have hnd := hd
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨a1, -, -, -, -⟩, -⟩ := hnd
  have ho0 : ∀ (u : List Bool) (k : ℕ), (St σ O S OP SP u k).sh O = ((St σ O S OP SP u k).st O).length := by
    intro u k; rw [St_sh_O hOS, St_st_O, ho]; simp
  have s1 : WExec cap (copyUn O S OP SP) σ (St σ O S OP SP (unary M) (M + 1)) (16 * M + 17) :=
    copyUn_spec cap O S hOS OP SP a1 M _ σ hd1 ho f1 f2
  have s2 := recLoop_spec cap O S hOS OP SP K T Lr GLr hd σ (fun j => pow (topW J W j)) (fun j => topW J W j) row L G
    rest hLG ho hK hT hLr hGL (levels J) (unary M) (M + 1) (fun j _ => hrow j) hd2 f3 f4
  have s3 := emitW_spec cap O OP [false] (St σ O S OP SP (unary M ++ (levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) fun j => (row j).take L))
      (M + 1 + ((levels J).flatMap (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length))
    (ho0 _ _) (by rw [St_val_OP a1]; simpa using f5)
  rw [St_emit hOS a1] at s3
  have s4 := wfwdC_spec cap S SP (St σ O S OP SP (unary M ++ (levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) fun j => (row j).take L) ++ [false])
      (M + 1 + ((levels J).flatMap (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length))
    (by rw [St_val_SP]; exact f6)
  rw [St_fwd] at s4
  have s5 := wrewind_spec cap S SP (M + 1 + ((levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length + 1)
    (St σ O S OP SP (unary M ++ (levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) fun j => (row j).take L) ++ [false])
      (M + 1 + ((levels J).flatMap (recG (fun j => pow (topW J W j)) (fun j => topW J W j) row)).length + 1))
    (by rw [St_val_SP, hSP, Nat.zero_add]) (by rw [St_val_SP]; exact f7)
  have eu : unary M ++ (levels J).flatMap
      (recG (fun j => pow (topW J W j)) (fun j => topW J W j) fun j => (row j).take L) ++ [false] =
      levelWord M J W (fun j => (row j).take L) := by
    rw [levelWord_eq, List.append_assoc]
  rw [eu] at s5
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · unfold St
    apply WState.eq
    · funext j
      by_cases hj : j = S
      · subst hj; simp [Function.update_apply, Ne.symm hOS]
      · simp [Function.update_apply, hj]
    · simp
    · funext q
      by_cases hq : q = SP
      · subst hq; simp [Function.update_apply, Ne.symm a1, hSP]
      · simp [Function.update_apply, hq]
    · simp
  · unfold truncCost
    rw [← fk]
    simp only [List.length_singleton]
    omega

/-- `n` cells forward on `i`, consuming the count `c`. -/
def fwdN (i : Fin (ns + 1)) (c : Fin nr) : WM ns nr := .whr c (.seq (.dec c) (.fwd i))

theorem fwdN_spec (i : Fin (ns + 1)) (c : Fin nr) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val c = n → σ.val c ≤ cap →
      WExec cap (fwdN i c) σ ((σ.setv c 0).seth i (σ.sh i + n)) (5 * n + 1)
  | 0, σ, h0, _ => by
    have e : (σ.setv c 0).seth i (σ.sh i + 0) = σ := WState.eq (by simp) rfl (by rw [← h0]; simp) rfl
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, hc => by
    have h1 := WExec.dec (cap := cap) c σ hc
    have h2 := WExec.fwd (cap := cap) i (σ.setv c (σ.val c - 1))
    have ih := fwdN_spec i c n ((σ.setv c (σ.val c - 1)).seth i ((σ.setv c (σ.val c - 1)).sh i + 1))
      (by simp; omega) (by simp; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) ih) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hji : j = i
      · subst hji; simp; omega
      · simp [Function.update_of_ne hji]
    · rfl
    · funext j
      by_cases hjc : j = c
      · subst hjc; simp
      · simp [Function.update_of_ne hjc]
    · rfl

/-- `v += 4·p` (`p` kept, scratch `t` at `0`). -/
def add4 (p v t : Fin nr) : WM ns nr :=
  .seq (PrimAsm.ParseNat.addTo p v t) (.seq (PrimAsm.ParseNat.addTo p v t)
    (.seq (PrimAsm.ParseNat.addTo p v t) (PrimAsm.ParseNat.addTo p v t)))

theorem add4_spec (p v t : Fin nr) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (σ : WState ns nr)
    (ht : σ.val t = 0) (hp : σ.val p ≤ cap) (hv : σ.val v + 4 * σ.val p ≤ cap) :
    WExec cap (add4 p v t) σ (σ.setv v (σ.val v + 4 * σ.val p)) (4 * (18 * σ.val p + 3) + 3) := by
  have vp : ∀ x : ℕ, (σ.setv v x).val p = σ.val p := fun x => by simp [Function.update_apply, hpv]
  have vt : ∀ x : ℕ, (σ.setv v x).val t = 0 := fun x => by simp [Function.update_apply, Ne.symm hvt, ht]
  have s1 := PrimAsm.ParseNat.addTo_spec cap p v t hpv hpt hvt σ ht hp (by omega)
  have s2 := PrimAsm.ParseNat.addTo_spec cap p v t hpv hpt hvt (σ.setv v (σ.val v + σ.val p)) (vt _)
    (by rw [vp]; exact hp) (by rw [vp]; simp; omega)
  rw [vp, WState.setv_val, Function.update_self, wsetv_setv] at s2
  have s3 := PrimAsm.ParseNat.addTo_spec cap p v t hpv hpt hvt (σ.setv v (σ.val v + σ.val p + σ.val p)) (vt _)
    (by rw [vp]; exact hp) (by rw [vp]; simp; omega)
  rw [vp, WState.setv_val, Function.update_self, wsetv_setv] at s3
  have s4 := PrimAsm.ParseNat.addTo_spec cap p v t hpv hpt hvt
    (σ.setv v (σ.val v + σ.val p + σ.val p + σ.val p)) (vt _) (by rw [vp]; exact hp) (by rw [vp]; simp; omega)
  rw [vp, WState.setv_val, Function.update_self, wsetv_setv] at s4
  have e : σ.val v + σ.val p + σ.val p + σ.val p + σ.val p = σ.val v + 4 * σ.val p := by ring
  rw [e] at s4
  exact WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega)

/-- `V := 4·(A + B + 1)` (from `V = 0`; `A`, `B` kept, scratch `t`). -/
def capW (A B V t : Fin nr) : WM ns nr :=
  .seq (add4 A V t) (.seq (add4 B V t) (.seq (.inc V) (.seq (.inc V) (.seq (.inc V) (.inc V)))))

/-- The cost of `capW`. -/
def capWCost (a b : ℕ) : ℕ := (4 * (18 * a + 3) + 3) + 1 + ((4 * (18 * b + 3) + 3) + 1 + 15)

theorem capW_spec (A B V t : Fin nr) (hAV : A ≠ V) (hAt : A ≠ t) (hBV : B ≠ V) (hBt : B ≠ t)
    (hVt : V ≠ t) (σ : WState ns nr) (hV : σ.val V = 0) (ht : σ.val t = 0)
    (hc : 4 * (σ.val A + σ.val B + 1) ≤ cap) :
    WExec cap (capW A B V t) σ (σ.setv V (4 * (σ.val A + σ.val B + 1))) (capWCost (σ.val A) (σ.val B)) := by
  have s1 := add4_spec cap A V t hAV hAt hVt σ ht (by omega) (by omega)
  rw [hV, Nat.zero_add] at s1
  set σ1 := σ.setv V (4 * σ.val A) with hσ1
  have s2 := add4_spec cap B V t hBV hBt hVt σ1 (by simp [σ1, Function.update_apply, Ne.symm hVt, ht])
    (by simp [σ1, Function.update_apply, hBV]; omega) (by simp [σ1, Function.update_apply, hBV]; omega)
  have vB : σ1.val B = σ.val B := by simp [σ1, Function.update_apply, hBV]
  rw [vB, WState.setv_val, Function.update_self, hσ1, wsetv_setv] at s2
  have i1 := WExec.inc (cap := cap) V (σ.setv V (4 * σ.val A + 4 * σ.val B)) (by simp; omega)
  rw [WState.setv_val, Function.update_self, wsetv_setv] at i1
  have i2 := WExec.inc (cap := cap) V (σ.setv V (4 * σ.val A + 4 * σ.val B + 1)) (by simp; omega)
  rw [WState.setv_val, Function.update_self, wsetv_setv] at i2
  have i3 := WExec.inc (cap := cap) V (σ.setv V (4 * σ.val A + 4 * σ.val B + 1 + 1)) (by simp; omega)
  rw [WState.setv_val, Function.update_self, wsetv_setv] at i3
  have i4 := WExec.inc (cap := cap) V (σ.setv V (4 * σ.val A + 4 * σ.val B + 1 + 1 + 1)) (by simp; omega)
  rw [WState.setv_val, Function.update_self, wsetv_setv] at i4
  have e : 4 * σ.val A + 4 * σ.val B + 1 + 1 + 1 + 1 = 4 * (σ.val A + σ.val B + 1) := by ring
  rw [e] at i4
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq i1 (WExec.seq i2 (WExec.seq i3 i4))))) ?_
  unfold capWCost
  omega

/-- `Gl := G − L` (from `Gl = 0`; `Gr`, `Lr` kept, scratch `t`, `u`). -/
def glW (Gr Lr Gl t u : Fin nr) : WM ns nr := .seq (wcopyR Gr Gl t) (EwKit.subR Lr Gl t u)

theorem glW_spec (Gr Lr Gl t u : Fin nr) (hd : [Gr, Lr, Gl, t, u].Nodup) (σ : WState ns nr) (hGL : σ.val Gl = 0)
    (ht : σ.val t = 0) (hu : σ.val u = 0) (hG : σ.val Gr ≤ cap) (hL : σ.val Lr ≤ cap) :
    WExec cap (glW Gr Lr Gl t u) σ (σ.setv Gl (σ.val Gr - σ.val Lr))
      (18 * σ.val Gr + 3 + 1 + (18 * σ.val Lr + 3 + 1 + (5 * σ.val Lr + 1))) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1, -⟩ := hd
  have s1 := wcopyR_spec cap Gr Gl t a2 a3 c1 σ hGL ht hG
  have vL : (σ.setv Gl (σ.val Gr)).val Lr = σ.val Lr := by simp [Function.update_apply, b1]
  have s2 := EwKit.subR_spec cap Lr Gl t u b1 b2 b3 c1 c2 d1 (σ.setv Gl (σ.val Gr)) (σ.val Lr) vL
    (by simp [Function.update_apply, Ne.symm c1, ht]) (by simp [Function.update_apply, Ne.symm c2, hu]) hL
    (by simp; exact hG)
  rw [WState.setv_val, Function.update_self, wsetv_setv] at s2
  exact WExec.seq s1 s2

end NearCubicWires.WireExponent3_5.UnionMachine.RadTrunc2
