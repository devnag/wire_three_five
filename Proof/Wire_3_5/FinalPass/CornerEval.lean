import Proof.Wire_3_5.FinalPass.CornerRef
import Proof.Wire_3_5.FinalPass.ListEvalCyc

/-! # Final pass, stage 2: the corner words at a sampled pair (P3:1645-1650, 3046-3053, 3170-3178)

The corner-word writer `cw`, a word program over 7 streams and 7 registers: the gate table `gatesW h G` (stream `G`,
from any origin), the framed assignments `c, u, v` (streams `C, U, V`, from `0`), two `h`-bit accumulators `P, N`
(streams `P, N`, from `0`, stale contents allowed) and the output (stream `O`, from `0`, stale contents allowed). For
every gate and every corner `(bu,bv) ∈ {(1,1),(1,0),(0,1),(0,0)}`, it loads `P := θ⁻`, `N := θ⁺`, adds the P/N parts
of the weights at the coordinates whose corner input `c + [bu]u + [bv]v` is one (the ripple-carry pass `mapS_add`),
compares `N ≤ P` (the borrow pass `mapS_cmp`), and appends the bit, framed, to the output. The gate table is rewound
between corners and at the end, the assignments after every corner, the output at the end.

At every phase boundary the machine state is `CSt.w x` for a record `x` (the counters `I`, `O` equal the heads of
`C/U/V` and `O`; `R` is zero). **`cw_spec`**: the output becomes `frameP (cornerWord (G.map eval) c u v)` over the
stale prefix, when `h` bounds every accumulator. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Pop

/-! ## Layout -/

scoped notation "sG" => (0 : Fin 7)
scoped notation "sC" => (1 : Fin 7)
scoped notation "sU" => (2 : Fin 7)
scoped notation "sV" => (3 : Fin 7)
scoped notation "sP" => (4 : Fin 7)
scoped notation "sN" => (5 : Fin 7)
scoped notation "sO" => (6 : Fin 7)

scoped notation "rF" => (0 : Fin 7)
scoped notation "rR" => (1 : Fin 7)
scoped notation "rX" => (2 : Fin 7)
scoped notation "rT" => (3 : Fin 7)
scoped notation "rG" => (4 : Fin 7)
scoped notation "rI" => (5 : Fin 7)
scoped notation "rO" => (6 : Fin 7)

abbrev CProg := WM 6 7

/-- The writer's state at a phase boundary. -/
structure CSt where
  gw : List Bool
  cw : List Bool
  uw : List Bool
  vw : List Bool
  pos : List Bool
  neg : List Bool
  out : List Bool
  gh : ℕ
  ih : ℕ
  oh : ℕ
  f : ℕ
  x : ℕ
  t : ℕ
  g : ℕ
  cell : Bool

/-- The word state of a phase record. -/
def CSt.w (x : CSt) : WState 6 7 :=
  ⟨![x.gh, x.ih, x.ih, x.ih, 0, 0, x.oh], ![x.gw, x.cw, x.uw, x.vw, x.pos, x.neg, x.out],
   ![x.f, 0, x.x, x.t, x.g, x.ih, x.oh], x.cell⟩

/-- Close an equality of word states against phase records. -/
syntax "cst_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cst_eq) => `(tactic| cst_eq [])
  | `(tactic| cst_eq [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [CSt.w, $ts,*]; done) | (simp [CSt.w, $ts,*] <;> omega))
        | rfl
        | (simp [CSt.w, $ts,*]; done)))

/-! ## Single updates of a phase record -/

section Upd
variable (x : CSt)

theorem c_f (n : ℕ) : x.w.setv rF n = { x with f := n }.w := by cst_eq
theorem c_x (n : ℕ) : x.w.setv rX n = { x with x := n }.w := by cst_eq
theorem c_fwdT : (x.w.seth sG (x.w.sh sG + 1)).setv rT (x.w.val rT + 1) = { x with gh := x.gh + 1, t := x.t + 1 }.w := by
  cst_eq
theorem c_fwdG : (x.w.seth sG (x.w.sh sG + 1)).setv rG (x.w.val rG + 1) = { x with gh := x.gh + 1, g := x.g + 1 }.w := by
  cst_eq
theorem c_fwdO : (x.w.seth sO (x.w.sh sO + 1)).setv rO (x.w.val rO + 1) = { x with oh := x.oh + 1 }.w := by
  cst_eq
theorem c_wrO (b : Bool) : x.w.sets sO (writeTapeBit (x.w.st sO) (x.w.sh sO) b) =
    { x with out := writeTapeBit x.out x.oh b }.w := by
  cst_eq
theorem c_setsP (l : List Bool) (n : ℕ) : (x.w.sets sP l).setv rF n = { x with pos := l, f := n }.w := by cst_eq
theorem c_setsN (l : List Bool) (n : ℕ) : (x.w.sets sN l).setv rF n = { x with neg := l, f := n }.w := by cst_eq
theorem c_rewT' (k : ℕ) : (x.w.setv rT 0).seth sG (x.w.sh sG - k) = { x with gh := x.gh - k, t := 0 }.w := by cst_eq
theorem c_rewG' (k : ℕ) : (x.w.setv rG 0).seth sG (x.w.sh sG - k) = { x with gh := x.gh - k, g := 0 }.w := by cst_eq
theorem c_rewO' (k : ℕ) (hk : x.oh = k) : (x.w.setv rO 0).seth sO (x.w.sh sO - k) = { x with oh := 0 }.w := by
  cst_eq [hk]
theorem c_moveTG : (x.w.setv rT 0).setv rG (x.w.val rG + x.w.val rT) = { x with t := 0, g := x.g + x.t }.w := by
  cst_eq

@[simp] theorem c_valF : x.w.val rF = x.f := rfl
@[simp] theorem c_valX : x.w.val rX = x.x := rfl
@[simp] theorem c_valT : x.w.val rT = x.t := rfl
@[simp] theorem c_valG : x.w.val rG = x.g := rfl
@[simp] theorem c_valI : x.w.val rI = x.ih := rfl
@[simp] theorem c_valO : x.w.val rO = x.oh := rfl
@[simp] theorem c_valR : x.w.val rR = 0 := rfl

end Upd

variable (cap : ℕ)

/-! ## Moves -/

/-- Forward the table, counting in `T`. -/
def fwdT : CProg := WM.fwdC sG rT

theorem fwdT_spec (x : CSt) (ht : x.t < cap) :
    WExec cap fwdT x.w { x with gh := x.gh + 1, t := x.t + 1 }.w 5 := by
  have h := wfwdC_spec cap sG rT x.w ht
  rwa [c_fwdT] at h

/-- Skip a framed word on the table. -/
def skipL : CProg := .whs sG (.seq fwdT fwdT)
def skipW : CProg := .seq skipL fwdT

theorem skipL_spec (rest : List Bool) : ∀ (bs : List Bool) (x : CSt), x.gw.drop x.gh = frameP bs ++ false :: rest →
    x.t + 2 * bs.length ≤ cap →
    WExec cap skipL x.w { x with gh := x.gh + 2 * bs.length, t := x.t + 2 * bs.length }.w (13 * bs.length + 1)
  | [], x, h, _ => by
    have hb : readTapeBit x.gw x.gh = false := ListEval.read_of_cons (by simpa using h)
    exact WExec.cast cap (WExec.whsF hb) (by simp) le_rfl
  | b :: bs, x, h, hc => by
    have h0 : x.gw.drop x.gh = true :: b :: (frameP bs ++ false :: rest) := by simpa using h
    have hb : readTapeBit x.gw x.gh = true := ListEval.read_of_cons h0
    have s1 := fwdT_spec cap x (by simp at hc; omega)
    have s2 := fwdT_spec cap { x with gh := x.gh + 1, t := x.t + 1 } (by simp at hc ⊢; omega)
    have h2 : x.gw.drop (x.gh + 1 + 1) = frameP bs ++ false :: rest :=
      ListEval.drop_succ_of_cons (ListEval.drop_succ_of_cons h0)
    have ih := skipL_spec rest bs { x with gh := x.gh + 1 + 1, t := x.t + 1 + 1 } h2 (by simp at hc ⊢; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq s1 s2) ih) ?_ (by simp; omega)
    congr 1; simp; omega

theorem skipW_spec (bs rest : List Bool) (x : CSt) (h : x.gw.drop x.gh = frameP bs ++ false :: rest)
    (hc : x.t + 2 * bs.length + 1 ≤ cap) :
    WExec cap skipW x.w { x with gh := x.gh + (2 * bs.length + 1), t := x.t + (2 * bs.length + 1) }.w
      (13 * bs.length + 7) := by
  have s1 := skipL_spec cap rest bs x h (by omega)
  have s2 := fwdT_spec cap { x with gh := x.gh + 2 * bs.length, t := x.t + 2 * bs.length } (by simp; omega)
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  congr 1

/-! ## Loading, adding, comparing -/

theorem drop_split (l : List Bool) (p : ℕ) (w : List Bool) (h : l.drop p = w) (hp : p ≤ l.length) :
    l = l.take p ++ w ∧ (l.take p).length = p := by
  refine ⟨by rw [← h, List.take_append_drop], by simp; omega⟩

/-- Load a table word into an accumulator. -/
def loadP : CProg := mapPass copyOut keepS sP sG rF rR
def loadN : CProg := mapPass copyOut keepS sN sG rF rR

theorem loadP_spec (x : CSt) (a bs restP rest : List Bool) (hp : x.pos = frameP a ++ false :: restP)
    (hG : x.gw.drop x.gh = frameP bs ++ rest) (hgh : x.gh ≤ x.gw.length) (hl : a.length = bs.length)
    (hf : x.f = 0) (hc : 1 ≤ cap) (hR : 2 * a.length ≤ cap) :
    WExec cap loadP x.w { x with pos := frameP bs ++ false :: restP }.w (a.length * 41 + 3) := by
  obtain ⟨e1, e2⟩ := drop_split x.gw x.gh _ hG hgh
  have h := mapPassAt_spec cap copyOut keepS sP sG rF rR (by decide) (by decide) hc a bs [] (x.gw.take x.gh) restP rest
    false x.w hl (by simpa [CSt.w] using hp) rfl (by show x.gw = _ ++ _ ++ _; rw [List.append_assoc]; exact e1)
    (by show x.gh = _; rw [e2]) (by simp [hf]) rfl hR
  rw [mapS_copy a bs false hl] at h
  simp only [List.nil_append] at h
  rw [c_setsP] at h
  refine WExec.cast cap h ?_ le_rfl
  congr 1; simp [hf]

theorem loadN_spec (x : CSt) (a bs restN rest : List Bool) (hn : x.neg = frameP a ++ false :: restN)
    (hG : x.gw.drop x.gh = frameP bs ++ rest) (hgh : x.gh ≤ x.gw.length) (hl : a.length = bs.length)
    (hf : x.f = 0) (hc : 1 ≤ cap) (hR : 2 * a.length ≤ cap) :
    WExec cap loadN x.w { x with neg := frameP bs ++ false :: restN }.w (a.length * 41 + 3) := by
  obtain ⟨e1, e2⟩ := drop_split x.gw x.gh _ hG hgh
  have h := mapPassAt_spec cap copyOut keepS sN sG rF rR (by decide) (by decide) hc a bs [] (x.gw.take x.gh) restN rest
    false x.w hl (by simpa [CSt.w] using hn) rfl (by show x.gw = _ ++ _ ++ _; rw [List.append_assoc]; exact e1)
    (by show x.gh = _; rw [e2]) (by simp [hf]) rfl hR
  rw [mapS_copy a bs false hl] at h
  simp only [List.nil_append] at h
  rw [c_setsN] at h
  refine WExec.cast cap h ?_ le_rfl
  congr 1; simp [hf]

/-- Add a table word into an accumulator; lower the carry. -/
def addP : CProg := .seq (mapPass addOut addNxt sP sG rF rR) (setFlag rF false)
def addN : CProg := .seq (mapPass addOut addNxt sN sG rF rR) (setFlag rF false)

theorem addP_spec (h : ℕ) (x : CSt) (a b : ℕ) (restP rest : List Bool) (hp : x.pos = frameP (binary h a) ++ false :: restP)
    (hG : x.gw.drop x.gh = frameP (binary h b) ++ rest) (hgh : x.gh ≤ x.gw.length) (hf : x.f = 0) (hc : 1 ≤ cap)
    (hR : 2 * h ≤ cap) :
    WExec cap addP x.w { x with pos := frameP (binary h (a + b)) ++ false :: restP }.w (h * 41 + 8) := by
  obtain ⟨e1, e2⟩ := drop_split x.gw x.gh _ hG hgh
  have hl : (binary h a).length = (binary h b).length := by rw [binary_length', binary_length']
  have s1 := mapPassAt_spec cap addOut addNxt sP sG rF rR (by decide) (by decide) hc (binary h a) (binary h b) []
    (x.gw.take x.gh) restP rest false x.w hl (by simpa [CSt.w] using hp) rfl
    (by show x.gw = _ ++ _ ++ _; rw [List.append_assoc]; exact e1) (by show x.gh = _; rw [e2]) (by simp [hf]) rfl
    (by rw [binary_length']; exact hR)
  rw [mapS_add, Bool.toNat_false, Nat.add_zero] at s1
  simp only [List.nil_append] at s1
  rw [c_setsP] at s1
  have s2 := setFlag_spec cap rF false (mapS addOut addNxt (binary h a) (binary h b) false).2
    { x with pos := frameP (binary h (a + b)) ++ false :: restP,
             f := (mapS addOut addNxt (binary h a) (binary h b) false).2.toNat }.w rfl hc
  rw [c_f] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [binary_length'])
  congr 1; simp [hf]

theorem addN_spec (h : ℕ) (x : CSt) (a b : ℕ) (restN rest : List Bool) (hn : x.neg = frameP (binary h a) ++ false :: restN)
    (hG : x.gw.drop x.gh = frameP (binary h b) ++ rest) (hgh : x.gh ≤ x.gw.length) (hf : x.f = 0) (hc : 1 ≤ cap)
    (hR : 2 * h ≤ cap) :
    WExec cap addN x.w { x with neg := frameP (binary h (a + b)) ++ false :: restN }.w (h * 41 + 8) := by
  obtain ⟨e1, e2⟩ := drop_split x.gw x.gh _ hG hgh
  have hl : (binary h a).length = (binary h b).length := by rw [binary_length', binary_length']
  have s1 := mapPassAt_spec cap addOut addNxt sN sG rF rR (by decide) (by decide) hc (binary h a) (binary h b) []
    (x.gw.take x.gh) restN rest false x.w hl (by simpa [CSt.w] using hn) rfl
    (by show x.gw = _ ++ _ ++ _; rw [List.append_assoc]; exact e1) (by show x.gh = _; rw [e2]) (by simp [hf]) rfl
    (by rw [binary_length']; exact hR)
  rw [mapS_add, Bool.toNat_false, Nat.add_zero] at s1
  simp only [List.nil_append] at s1
  rw [c_setsN] at s1
  have s2 := setFlag_spec cap rF false (mapS addOut addNxt (binary h a) (binary h b) false).2
    { x with neg := frameP (binary h (a + b)) ++ false :: restN,
             f := (mapS addOut addNxt (binary h a) (binary h b) false).2.toNat }.w rfl hc
  rw [c_f] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [binary_length'])
  congr 1; simp [hf]

/-- Compare: `F := [N ≤ P]`. -/
def cmpP : CProg := .seq (setFlag rF true) (mapPass keepA cmpNxt sP sN rF rR)

theorem cmpP_spec (h : ℕ) (x : CSt) (a b : ℕ) (restP restN : List Bool)
    (hp : x.pos = frameP (binary h a) ++ false :: restP) (hn : x.neg = frameP (binary h b) ++ false :: restN)
    (hf : x.f = 0) (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) :
    WExec cap cmpP x.w { x with f := (decide (b % 2 ^ h ≤ a % 2 ^ h)).toNat }.w (h * 41 + 8) := by
  have s1 := setFlag_spec cap rF true false x.w (by simp [hf]) hc
  rw [c_f] at s1
  have hl : (binary h a).length = (binary h b).length := by rw [binary_length', binary_length']
  have s2 := mapPassAt_spec cap keepA cmpNxt sP sN rF rR (by decide) (by decide) hc (binary h a) (binary h b) [] []
    restP (false :: restN) true { x with f := (true).toNat }.w hl (by simpa [CSt.w] using hp) rfl
    (by simpa [CSt.w] using hn) rfl rfl rfl (by rw [binary_length']; exact hR)
  rw [mapS_keep cmpNxt _ _ true hl, mapS_cmp] at s2
  simp only [List.nil_append, Bool.not_true, Bool.toNat_false, Nat.add_zero] at s2
  rw [c_setsP] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by rw [binary_length']; omega)
  congr 1; simp [hp]

/-! ## The output bit -/

/-- Append the flag, framed, to the output; lower the flag. -/
def emitP : CProg :=
  .seq (.wr sO true) (.seq (WM.fwdC sO rO) (.seq (.ifr rF (.wr sO true) (.wr sO false))
    (.seq (WM.fwdC sO rO) (setFlag rF false))))

theorem frameP_app (l l' : List Bool) : frameP (l ++ l') = frameP l ++ frameP l' := by
  simp [frameP, List.flatMap_append]

theorem writeTapeBit_app (pre r : List Bool) (b v : Bool) :
    writeTapeBit (pre ++ b :: r) pre.length v = pre ++ v :: r := writeTapeBit_mid' pre r b v

theorem emitP_spec (x : CSt) (d r : List Bool) (b0 b1 : Bool) (bit : Bool) (hout : x.out = frameP d ++ b0 :: b1 :: r)
    (hoh : x.oh = 2 * d.length) (hf : x.f = bit.toNat) (hc : 1 ≤ cap) (ho : x.oh + 2 ≤ cap) :
    WExec cap emitP x.w { x with out := frameP (d ++ [bit]) ++ r, oh := x.oh + 2, f := 0 }.w 22 := by
  have hlen : (frameP d).length = x.oh := by simp [hoh]
  have s1 := WExec.wr (cap := cap) sO true x.w
  rw [c_wrO] at s1
  have e1 : writeTapeBit x.out x.oh true = frameP d ++ true :: b1 :: r := by
    rw [hout, ← hlen, writeTapeBit_app]
  rw [e1] at s1
  have s2 := wfwdC_spec cap sO rO { x with out := frameP d ++ true :: b1 :: r }.w (by simp; omega)
  rw [c_fwdO] at s2
  have e2 : ∀ v : Bool, writeTapeBit (frameP d ++ true :: b1 :: r) (x.oh + 1) v = frameP (d ++ [v]) ++ r := by
    intro v
    have := writeTapeBit_app (frameP d ++ [true]) r b1 v
    rw [show frameP d ++ true :: b1 :: r = frameP d ++ [true] ++ b1 :: r by simp,
      show x.oh + 1 = (frameP d ++ [true]).length by simp [hlen]]
    rw [this, frameP_app]
    simp
  have s3 : WExec cap (.ifr rF (.wr sO true) (.wr sO false))
      { { x with out := frameP d ++ true :: b1 :: r } with oh := x.oh + 1 }.w
      { { x with out := frameP (d ++ [bit]) ++ r } with oh := x.oh + 1 }.w 2 := by
    cases bit
    · have w := WExec.wr (cap := cap) sO false { { x with out := frameP d ++ true :: b1 :: r } with oh := x.oh + 1 }.w
      rw [c_wrO] at w
      simp only [] at w
      rw [e2] at w
      exact WExec.cast cap (WExec.ifrF (by simp [hf]) w) rfl le_rfl
    · have w := WExec.wr (cap := cap) sO true { { x with out := frameP d ++ true :: b1 :: r } with oh := x.oh + 1 }.w
      rw [c_wrO] at w
      simp only [] at w
      rw [e2] at w
      exact WExec.cast cap (WExec.ifrT (by simp [hf]) w) rfl le_rfl
  have s4 := wfwdC_spec cap sO rO { { x with out := frameP (d ++ [bit]) ++ r } with oh := x.oh + 1 }.w (by simp; omega)
  rw [c_fwdO] at s4
  have s5 := setFlag_spec cap rF false bit { { { x with out := frameP (d ++ [bit]) ++ r } with oh := x.oh + 1 } with
    oh := x.oh + 1 + 1 }.w (by simp [hf]) hc
  rw [c_f] at s5
  exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) (by congr 1) (by omega)

/-! ## The corner input bit -/

/-- Advance `C, U, V` together, counting in `I`. -/
def fwdI : CProg := .seq (.fwd sC) (.seq (.fwd sU) (.seq (.fwd sV) (.inc rI)))

theorem fwdI_spec (x : CSt) (hi : x.ih < cap) : WExec cap fwdI x.w { x with ih := x.ih + 1 }.w 9 := by
  have s1 := WExec.fwd (cap := cap) sC x.w
  have s2 := WExec.fwd (cap := cap) sU (x.w.seth sC (x.w.sh sC + 1))
  have s3 := WExec.fwd (cap := cap) sV ((x.w.seth sC (x.w.sh sC + 1)).seth sU ((x.w.seth sC (x.w.sh sC + 1)).sh sU + 1))
  have s4 := WExec.inc (cap := cap) rI (((x.w.seth sC (x.w.sh sC + 1)).seth sU ((x.w.seth sC (x.w.sh sC + 1)).sh sU + 1)).seth
    sV (((x.w.seth sC (x.w.sh sC + 1)).seth sU ((x.w.seth sC (x.w.sh sC + 1)).sh sU + 1)).sh sV + 1)) (by
      simp [CSt.w]; omega)
  exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by cst_eq) le_rfl

/-- Flip the input bit `X`. -/
def flipX : CProg := .ifr rX (.dec rX) (.inc rX)

theorem flipX_spec (x : CSt) (b : Bool) (hx : x.x = b.toNat) (hc : 1 ≤ cap) :
    WExec cap flipX x.w { x with x := (!b).toNat }.w 4 := by
  cases b
  · have d := WExec.inc (cap := cap) rX x.w (by simp [hx]; omega)
    rw [c_valX, c_x, hx] at d
    exact WExec.ifrF (by simp [hx]) d
  · have d := WExec.dec (cap := cap) rX x.w (by simp [hx]; omega)
    rw [c_valX, c_x, hx] at d
    exact WExec.mono (WExec.ifrT (by simp [hx]) d) (by omega)

/-- Flip `X` when the scanned bit of stream `i` is one. -/
def condFlip (i : Fin 7) : CProg := .ifs i flipX .skip

theorem condFlip_spec (i : Fin 7) (x : CSt) (b bit : Bool) (hbit : wbit x.w i = bit) (hx : x.x = b.toNat)
    (hc : 1 ≤ cap) : WExec cap (condFlip i) x.w { x with x := (xor b bit).toNat }.w 5 := by
  cases bit
  · exact WExec.cast cap (WExec.ifsF hbit (WExec.skip _)) (by congr 1; simp [← hx]) (by omega)
  · exact WExec.cast cap (WExec.ifsT hbit (flipX_spec cap x b hx hc)) (by congr 1; simp) le_rfl

/-- `X := c + [bu]u + [bv]v` from `X = 0`. -/
def setX (bu bv : Bool) : CProg :=
  .seq (condFlip sC) (.seq (if bu then condFlip sU else .skip) (if bv then condFlip sV else .skip))

theorem setX_spec (bu bv : Bool) (x : CSt) (c u v : Bool) (hcb : wbit x.w sC = c) (hub : wbit x.w sU = u)
    (hvb : wbit x.w sV = v) (hx : x.x = 0) (hc : 1 ≤ cap) :
    WExec cap (setX bu bv) x.w { x with x := (xor (xor c (bu && u)) (bv && v)).toNat }.w 17 := by
  have s1 := condFlip_spec cap sC x false c hcb (by simp [hx]) hc
  simp only [Bool.false_xor] at s1
  have hu' : wbit { x with x := c.toNat }.w sU = u := hub
  have hv' : wbit { x with x := c.toNat }.w sV = v := hvb
  cases bu <;> cases bv
  · exact WExec.cast cap (WExec.seq s1 (WExec.seq (WExec.skip _) (WExec.skip _))) (by congr 1; simp) (by omega)
  · have s3 := condFlip_spec cap sV { x with x := c.toNat } c v hv' rfl hc
    exact WExec.cast cap (WExec.seq s1 (WExec.seq (WExec.skip _) s3)) (by congr 1; simp) (by omega)
  · have s2 := condFlip_spec cap sU { x with x := c.toNat } c u hu' rfl hc
    exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.skip _))) (by congr 1; simp) (by omega)
  · have s2 := condFlip_spec cap sU { x with x := c.toNat } c u hu' rfl hc
    have hv'' : wbit { { x with x := c.toNat } with x := (xor c u).toNat }.w sV = v := hvb
    have s3 := condFlip_spec cap sV { { x with x := c.toNat } with x := (xor c u).toNat } (xor c u) v hv'' rfl hc
    exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) (by congr 1) (by omega)

/-- Lower `X`. -/
def clrX : CProg := .ifr rX (.dec rX) .skip

theorem clrX_spec (x : CSt) (b : Bool) (hx : x.x = b.toNat) (hc : 1 ≤ cap) :
    WExec cap clrX x.w { x with x := 0 }.w 2 := by
  cases b
  · have e : ({ x with x := 0 } : CSt) = x := by cases x; simp at hx; simp [hx]
    rw [e]
    exact WExec.mono (WExec.ifrF (by simp [hx]) (WExec.skip _)) (by omega)
  · have d := WExec.dec (cap := cap) rX x.w (by simp [hx]; omega)
    rw [c_valX, c_x, hx] at d
    exact WExec.ifrT (by simp [hx]) d

/-! ## One coordinate, all coordinates -/

/-- Add both parts of the weight at the table head. -/
def addBoth : CProg := .seq addP (.seq skipW (.seq addN skipW))
/-- Skip the weight at the table head. -/
def skipBoth : CProg := .seq skipW skipW

/-- One coordinate of corner `(bu,bv)`: read `c_i, u_i, v_i`, add the weight when the corner input is one. -/
def coordBody (bu bv : Bool) : CProg :=
  .seq fwdI (.seq (setX bu bv) (.seq (.ifr rX addBoth skipBoth) (.seq clrX fwdI)))

theorem pairW_eq (h : ℕ) (w : ℤ) (rest : List Bool) :
    pairW h w ++ rest =
      frameP (binary h w.toNat) ++ false :: (frameP (binary h (-w).toNat) ++ false :: rest) := by
  simp [pairW, frame_eq_frameP]

theorem coordBody_spec (h : ℕ) (bu bv : Bool) (x : CSt) (w : ℤ) (c u v u0 v0 : Bool)
    (restC restU restV rest restP restN : List Bool) (P N : ℕ)
    (hC : x.cw.drop x.ih = true :: c :: restC) (hU : x.uw.drop x.ih = u0 :: u :: restU)
    (hV : x.vw.drop x.ih = v0 :: v :: restV) (hG : x.gw.drop x.gh = pairW h w ++ rest)
    (hgh : x.gh + 2 * (2 * h + 1) ≤ x.gw.length)
    (hp : x.pos = frameP (binary h P) ++ false :: restP) (hn : x.neg = frameP (binary h N) ++ false :: restN)
    (hf : x.f = 0) (hx : x.x = 0) (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) (hi : x.ih + 2 ≤ cap)
    (ht : x.t + 2 * (2 * h + 1) ≤ cap) :
    WExec cap (coordBody bu bv) x.w
      { x with
        ih := x.ih + 2
        gh := x.gh + 2 * (2 * h + 1)
        t := x.t + 2 * (2 * h + 1)
        pos := frameP (binary h (P + if xor (xor c (bu && u)) (bv && v) then w.toNat else 0)) ++ false :: restP
        neg := frameP (binary h (N + if xor (xor c (bu && u)) (bv && v) then (-w).toNat else 0)) ++ false :: restN }.w
      (110 * h + 90) := by
  have s1 := fwdI_spec cap x (by omega)
  have hcb : wbit { x with ih := x.ih + 1 }.w sC = c := by
    show readTapeBit x.cw (x.ih + 1) = c; exact ListEval.read_of_cons (ListEval.drop_succ_of_cons hC)
  have hub : wbit { x with ih := x.ih + 1 }.w sU = u := by
    show readTapeBit x.uw (x.ih + 1) = u; exact ListEval.read_of_cons (ListEval.drop_succ_of_cons hU)
  have hvb : wbit { x with ih := x.ih + 1 }.w sV = v := by
    show readTapeBit x.vw (x.ih + 1) = v; exact ListEval.read_of_cons (ListEval.drop_succ_of_cons hV)
  have s2 := setX_spec cap bu bv { x with ih := x.ih + 1 } c u v hcb hub hvb hx hc
  generalize hxb : xor (xor c (bu && u)) (bv && v) = xb at s2 ⊢
  obtain ⟨y2, hy2⟩ : ∃ y, y = { { x with ih := x.ih + 1 } with x := xb.toNat } := ⟨_, rfl⟩
  rw [← hy2] at s2
  have hG2 : y2.gw.drop y2.gh = frameP (binary h w.toNat) ++
      false :: (frameP (binary h (-w).toNat) ++ false :: rest) := by
    rw [hy2]; simp only []; rw [hG, pairW_eq]
  have hbl : ∀ z : ℕ, (binary h z).length = h := fun z => binary_length' h z
  -- the weight
  have e_gw : y2.gw = x.gw := by rw [hy2]
  have e_gh : y2.gh = x.gh := by rw [hy2]
  have e_t : y2.t = x.t := by rw [hy2]
  have e_pos : y2.pos = x.pos := by rw [hy2]
  have e_neg : y2.neg = x.neg := by rw [hy2]
  have e_f : y2.f = 0 := by rw [hy2]; exact hf
  have e_x : y2.x = xb.toNat := by rw [hy2]
  have hG3 : y2.gw.drop (y2.gh + (2 * h + 1)) = frameP (binary h (-w).toNat) ++ false :: rest := by
    have := ListEval.drop_add_of_append hG2
    rw [show y2.gh + (2 * h + 1) = y2.gh + (frameP (binary h w.toNat)).length + 1 by simp [hbl]; ring]
    exact ListEval.drop_succ_of_cons this
  have hG4 : y2.gw.drop (y2.gh + (2 * h + 1) + (2 * h + 1)) = rest := by
    have := ListEval.drop_add_of_append hG3
    rw [show y2.gh + (2 * h + 1) + (2 * h + 1) = y2.gh + (2 * h + 1) + (frameP (binary h (-w).toNat)).length + 1 by
      simp [hbl]; ring]
    exact ListEval.drop_succ_of_cons this
  obtain ⟨y6, hy6, s3⟩ : ∃ y6 : CSt,
      y6 = { y2 with
             gh := y2.gh + 2 * (2 * h + 1)
             t := y2.t + 2 * (2 * h + 1)
             pos := frameP (binary h (P + if xb then w.toNat else 0)) ++ false :: restP
             neg := frameP (binary h (N + if xb then (-w).toNat else 0)) ++ false :: restN } ∧
      WExec cap (.ifr rX addBoth skipBoth) y2.w y6.w (108 * h + 38) := by
    refine ⟨_, rfl, ?_⟩
    cases xb
    · have k1 := skipW_spec cap (binary h w.toNat) (frameP (binary h (-w).toNat) ++ false :: rest) y2 hG2
        (by rw [hbl, e_t]; omega)
      rw [hbl] at k1
      obtain ⟨y3, hy3⟩ : ∃ y, y = { y2 with gh := y2.gh + (2 * h + 1), t := y2.t + (2 * h + 1) } := ⟨_, rfl⟩
      rw [← hy3] at k1
      have k2 := skipW_spec cap (binary h (-w).toNat) rest y3 (by rw [hy3]; exact hG3)
        (by rw [hy3]; simp only [hbl, e_t]; omega)
      rw [hbl] at k2
      refine WExec.cast cap (WExec.ifrF (by rw [c_valX, e_x]; rfl) (WExec.seq k1 k2)) ?_ (by omega)
      rw [hy3]; congr 1; simp [e_pos, e_neg, hp, hn]; omega
    · have k1 := addP_spec cap h y2 P w.toNat restP (false :: (frameP (binary h (-w).toNat) ++ false :: rest))
        (by rw [e_pos]; exact hp) hG2 (by rw [e_gh, e_gw]; omega) e_f hc hR
      obtain ⟨y3, hy3⟩ : ∃ y, y = { y2 with pos := frameP (binary h (P + w.toNat)) ++ false :: restP } := ⟨_, rfl⟩
      rw [← hy3] at k1
      have k2 := skipW_spec cap (binary h w.toNat) (frameP (binary h (-w).toNat) ++ false :: rest) y3
        (by rw [hy3]; exact hG2) (by rw [hy3]; simp only [hbl, e_t]; omega)
      rw [hbl] at k2
      obtain ⟨y4, hy4⟩ : ∃ y, y = { y3 with gh := y3.gh + (2 * h + 1), t := y3.t + (2 * h + 1) } := ⟨_, rfl⟩
      rw [← hy4] at k2
      have k3 := addN_spec cap h y4 N (-w).toNat restN (false :: rest) (by rw [hy4, hy3]; exact e_neg.trans hn)
        (by rw [hy4, hy3]; exact hG3) (by rw [hy4, hy3]; simp only [e_gh, e_gw]; omega)
        (by rw [hy4, hy3]; exact e_f) hc hR
      obtain ⟨y5, hy5⟩ : ∃ y, y = { y4 with neg := frameP (binary h (N + (-w).toNat)) ++ false :: restN } := ⟨_, rfl⟩
      rw [← hy5] at k3
      have k4 := skipW_spec cap (binary h (-w).toNat) rest y5 (by rw [hy5, hy4, hy3]; exact hG3)
        (by rw [hy5, hy4, hy3]; simp only [hbl, e_t]; omega)
      rw [hbl] at k4
      refine WExec.cast cap (WExec.ifrT (by rw [c_valX, e_x]; decide) (WExec.seq k1 (WExec.seq k2 (WExec.seq k3 k4))))
        ?_ (by omega)
      rw [hy5, hy4, hy3]; congr 1; simp; omega
  have s4 := clrX_spec cap y6 xb (by rw [hy6, e_x]) hc
  have s5 := fwdI_spec cap { y6 with x := 0 } (by rw [hy6, hy2]; simp; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ (by omega)
  rw [hy6, hy2]; congr 1; simp [hx]

/-- All coordinates of corner `(bu,bv)`. -/
def coordLoop (bu bv : Bool) : CProg := .whs sC (coordBody bu bv)

theorem pairW_length (h : ℕ) (w : ℤ) : (pairW h w).length = 2 * (2 * h + 1) := by
  simp [pairW, frame_eq_frameP]; ring

theorem coordLoop_spec (h : ℕ) (bu bv : Bool) (restC restU restV rest restP restN : List Bool) (hc : 1 ≤ cap)
    (hR : 2 * h ≤ cap) :
    ∀ (ws : List ℤ) (cs us vs : List Bool) (x : CSt) (P N : ℕ), cs.length = ws.length → us.length = ws.length →
      vs.length = ws.length →
      x.cw.drop x.ih = frameP cs ++ false :: restC → x.uw.drop x.ih = frameP us ++ restU →
      x.vw.drop x.ih = frameP vs ++ restV → x.gw.drop x.gh = ws.flatMap (pairW h) ++ rest →
      x.gh + ws.length * (2 * (2 * h + 1)) ≤ x.gw.length →
      x.pos = frameP (binary h P) ++ false :: restP → x.neg = frameP (binary h N) ++ false :: restN →
      x.f = 0 → x.x = 0 → x.ih + 2 * ws.length ≤ cap → x.t + ws.length * (2 * (2 * h + 1)) ≤ cap →
      WExec cap (coordLoop bu bv) x.w
        { x with
          ih := x.ih + 2 * ws.length
          gh := x.gh + ws.length * (2 * (2 * h + 1))
          t := x.t + ws.length * (2 * (2 * h + 1))
          pos := frameP (binary h (P + posAcc ws (cornerIn bu bv cs us vs))) ++ false :: restP
          neg := frameP (binary h (N + negAcc ws (cornerIn bu bv cs us vs))) ++ false :: restN }.w
        (ws.length * (110 * h + 92) + 1)
  | [], cs, us, vs, x, P, N, hcl, _, _, hC, _, _, _, _, hp, hn, _, _, _, _ => by
    have e : cs = [] := List.eq_nil_of_length_eq_zero hcl
    subst e
    have hb : readTapeBit x.cw x.ih = false := ListEval.read_of_cons (by simpa using hC)
    refine WExec.cast cap (WExec.whsF hb) ?_ (by simp)
    congr 1
    cases x
    simp only [] at hp hn
    simp [hp, hn, posAcc, negAcc]
  | w :: ws, cs, us, vs, x, P, N, hcl, hul, hvl, hC, hU, hV, hG, hgh, hp, hn, hf, hx, hi, ht => by
    obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
      rcases cs with _ | ⟨c, cs'⟩
      · simp at hcl
      · exact ⟨c, cs', rfl⟩
    obtain ⟨u, us', rfl⟩ : ∃ u us', us = u :: us' := by
      rcases us with _ | ⟨u, us'⟩
      · simp at hul
      · exact ⟨u, us', rfl⟩
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
      rcases vs with _ | ⟨v, vs'⟩
      · simp at hvl
      · exact ⟨v, vs', rfl⟩
    simp only [List.length_cons] at hcl hul hvl hi ht hgh
    have hC0 : x.cw.drop x.ih = true :: c :: (frameP cs' ++ false :: restC) := by simpa using hC
    have hU0 : x.uw.drop x.ih = true :: u :: (frameP us' ++ restU) := by simpa using hU
    have hV0 : x.vw.drop x.ih = true :: v :: (frameP vs' ++ restV) := by simpa using hV
    have hG0 : x.gw.drop x.gh = pairW h w ++ (ws.flatMap (pairW h) ++ rest) := by simpa using hG
    have s1 := coordBody_spec cap h bu bv x w c u v true true _ _ _ _ restP restN P N hC0 hU0 hV0 hG0 (by nlinarith) hp
      hn hf hx hc hR (by omega) (by nlinarith)
    generalize hxb : xor (xor c (bu && u)) (bv && v) = xb at s1
    obtain ⟨y, hy⟩ : ∃ y : CSt,
        y = { x with
              ih := x.ih + 2
              gh := x.gh + 2 * (2 * h + 1)
              t := x.t + 2 * (2 * h + 1)
              pos := frameP (binary h (P + if xb then w.toNat else 0)) ++ false :: restP
              neg := frameP (binary h (N + if xb then (-w).toNat else 0)) ++ false :: restN } := ⟨_, rfl⟩
    rw [← hy] at s1
    have hCy : y.cw.drop y.ih = frameP cs' ++ false :: restC := by
      rw [hy]; exact ListEval.drop_succ_of_cons (ListEval.drop_succ_of_cons hC0)
    have hUy : y.uw.drop y.ih = frameP us' ++ restU := by
      rw [hy]; exact ListEval.drop_succ_of_cons (ListEval.drop_succ_of_cons hU0)
    have hVy : y.vw.drop y.ih = frameP vs' ++ restV := by
      rw [hy]; exact ListEval.drop_succ_of_cons (ListEval.drop_succ_of_cons hV0)
    have hGy : y.gw.drop y.gh = ws.flatMap (pairW h) ++ rest := by
      rw [hy]
      have := ListEval.drop_add_of_append hG0
      rwa [pairW_length] at this
    have ih := coordLoop_spec h bu bv restC restU restV rest restP restN hc hR ws cs' us' vs' y
      (P + if xb then w.toNat else 0) (N + if xb then (-w).toNat else 0) (by omega) (by omega) (by omega) hCy hUy hVy hGy
      (by rw [hy]; simp only []; nlinarith) (by rw [hy]) (by rw [hy]) (by rw [hy]; exact hf) (by rw [hy]; exact hx)
      (by rw [hy]; simp only []; omega) (by rw [hy]; simp only []; nlinarith)
    have hb : readTapeBit x.cw x.ih = true := ListEval.read_of_cons hC0
    refine WExec.cast cap (WExec.whsT hb s1 ih) ?_ (by simp only [List.length_cons]; nlinarith)
    rw [hy]
    have ec : cornerIn bu bv (c :: cs') (u :: us') (v :: vs') = xb :: cornerIn bu bv cs' us' vs' := by
      rw [← hxb]; rfl
    rw [ec]
    simp only [posAcc, negAcc, List.length_cons, Nat.add_assoc]
    congr 1
    congr 1 <;> ring

/-! ## One corner -/

/-- Return `C, U, V` by the counter `I`. -/
def rewI : CProg := .whr rI (.seq (.dec rI) (.seq (.bwd sC) (.seq (.bwd sU) (.bwd sV))))

theorem rewI_spec : ∀ (k : ℕ) (x : CSt), x.ih = k → k ≤ cap → WExec cap rewI x.w { x with ih := 0 }.w (9 * k + 1)
  | 0, x, hk, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [hk])) ?_ le_rfl
    congr 1; cases x; simp_all
  | k + 1, x, hk, hc => by
    have d1 := WExec.dec (cap := cap) rI x.w (by simp; omega)
    have d2 := WExec.bwd (cap := cap) sC (x.w.setv rI (x.w.val rI - 1))
    have d3 := WExec.bwd (cap := cap) sU ((x.w.setv rI (x.w.val rI - 1)).seth sC ((x.w.setv rI (x.w.val rI - 1)).sh sC - 1))
    have d4 := WExec.bwd (cap := cap) sV (((x.w.setv rI (x.w.val rI - 1)).seth sC ((x.w.setv rI (x.w.val rI - 1)).sh sC - 1)).seth
      sU (((x.w.setv rI (x.w.val rI - 1)).seth sC ((x.w.setv rI (x.w.val rI - 1)).sh sC - 1)).sh sU - 1))
    have e : (((x.w.setv rI (x.w.val rI - 1)).seth sC ((x.w.setv rI (x.w.val rI - 1)).sh sC - 1)).seth
        sU (((x.w.setv rI (x.w.val rI - 1)).seth sC ((x.w.setv rI (x.w.val rI - 1)).sh sC - 1)).sh sU - 1)).seth sV
        ((((x.w.setv rI (x.w.val rI - 1)).seth sC ((x.w.setv rI (x.w.val rI - 1)).sh sC - 1)).seth
        sU (((x.w.setv rI (x.w.val rI - 1)).seth sC ((x.w.setv rI (x.w.val rI - 1)).sh sC - 1)).sh sU - 1)).sh sV - 1) =
        { x with ih := k }.w := by
      cst_eq [hk]
    rw [e] at d4
    have ih := rewI_spec k { x with ih := k } rfl (by omega)
    refine WExec.cast cap (WExec.whrT (by simp [hk]) (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) ih) ?_ (by omega)
    congr 1

/-- One corner: load `θ⁻, θ⁺`, add the weights at the corner's input, compare, append the bit, return `C, U, V`. -/
def core (bu bv : Bool) : CProg :=
  .seq loadP (.seq skipW (.seq loadN (.seq skipW (.seq (coordLoop bu bv) (.seq cmpP (.seq emitP rewI))))))

/-- The corner cost. -/
def coreCost (h n : ℕ) : ℕ := n * (110 * h + 110) + 160 * h + 80

theorem core_spec (h : ℕ) (bu bv : Bool) {n : ℕ} (g : NormalizedThresholdGate n) (c u v : BitInput n) (x : CSt)
    (a b restP restN rest restC restU restV d r : List Bool) (b0 b1 : Bool)
    (hG : x.gw.drop x.gh = pairW h (-g.threshold) ++ ((List.ofFn g.weight).flatMap (pairW h) ++ rest))
    (hgh : x.gh + (n + 1) * (2 * (2 * h + 1)) ≤ x.gw.length)
    (hC : x.cw = frameP (List.ofFn c) ++ false :: restC) (hU : x.uw = frameP (List.ofFn u) ++ restU)
    (hV : x.vw = frameP (List.ofFn v) ++ restV) (hih : x.ih = 0)
    (hp : x.pos = frameP a ++ false :: restP) (hn : x.neg = frameP b ++ false :: restN) (ha : a.length = h)
    (hb : b.length = h) (hout : x.out = frameP d ++ b0 :: b1 :: r) (hoh : x.oh = 2 * d.length)
    (hf : x.f = 0) (hx : x.x = 0) (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) (hnc : 2 * n ≤ cap)
    (ht : x.t + (n + 1) * (2 * (2 * h + 1)) ≤ cap) (ho : x.oh + 2 ≤ cap)
    (hov : (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) :
    ∃ A B : ℕ, WExec cap (core bu bv) x.w
      { x with
        gh := x.gh + (n + 1) * (2 * (2 * h + 1))
        t := x.t + (n + 1) * (2 * (2 * h + 1))
        pos := frameP (binary h A) ++ false :: restP
        neg := frameP (binary h B) ++ false :: restN
        out := frameP (d ++ [g.eval (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i))]) ++ r
        oh := x.oh + 2 }.w (coreCost h n) := by
  have hbl : ∀ z : ℕ, (binary h z).length = h := fun z => binary_length' h z
  have hwl : (List.ofFn g.weight).length = n := List.length_ofFn
  obtain ⟨M, hM⟩ : ∃ M, M = n * (2 * (2 * h + 1)) := ⟨_, rfl⟩
  have eM : (n + 1) * (2 * (2 * h + 1)) = M + 2 * (2 * h + 1) := by rw [hM]; ring
  rw [eM] at hgh ht ⊢
  have hG1 : x.gw.drop x.gh = frameP (binary h (-g.threshold).toNat) ++
      (false :: (frameP (binary h (-(-g.threshold)).toNat) ++ false :: ((List.ofFn g.weight).flatMap (pairW h) ++ rest))) := by
    rw [hG, pairW_eq]
  -- load θ⁻
  have l1 := loadP_spec cap x a (binary h (-g.threshold).toNat) restP _ hp hG1 (by omega) (by rw [ha, hbl]) hf hc
    (by rw [ha]; exact hR)
  obtain ⟨y1, hy1⟩ : ∃ y, y = { x with pos := frameP (binary h (-g.threshold).toNat) ++ false :: restP } := ⟨_, rfl⟩
  rw [← hy1] at l1
  have hG1' : y1.gw.drop y1.gh = frameP (binary h (-g.threshold).toNat) ++ false ::
      (frameP (binary h (-(-g.threshold)).toNat) ++ false :: ((List.ofFn g.weight).flatMap (pairW h) ++ rest)) := by
    rw [hy1]; exact hG1
  have k1 := skipW_spec cap _ _ y1 hG1' (by rw [hy1, hbl]; simp only []; omega)
  rw [hbl] at k1
  obtain ⟨y2, hy2⟩ : ∃ y, y = { y1 with gh := y1.gh + (2 * h + 1), t := y1.t + (2 * h + 1) } := ⟨_, rfl⟩
  rw [← hy2] at k1
  have hG2 : y2.gw.drop y2.gh = frameP (binary h (-(-g.threshold)).toNat) ++
      (false :: ((List.ofFn g.weight).flatMap (pairW h) ++ rest)) := by
    rw [hy2, hy1]
    have := ListEval.drop_add_of_append hG1
    rw [show x.gh + (2 * h + 1) = x.gh + (frameP (binary h (-g.threshold).toNat)).length + 1 by simp [hbl]; ring]
    exact ListEval.drop_succ_of_cons this
  -- load θ⁺
  have l2 := loadN_spec cap y2 b (binary h (-(-g.threshold)).toNat) restN _ (by rw [hy2, hy1]; exact hn) hG2
    (by rw [hy2, hy1]; simp only []; omega) (by rw [hb, hbl]) (by rw [hy2, hy1]; exact hf) hc (by rw [hb]; exact hR)
  obtain ⟨y3, hy3⟩ : ∃ y, y = { y2 with neg := frameP (binary h (-(-g.threshold)).toNat) ++ false :: restN } :=
    ⟨_, rfl⟩
  rw [← hy3] at l2
  have k2 := skipW_spec cap _ _ y3 (by rw [hy3]; exact hG2) (by rw [hy3, hy2, hy1, hbl]; simp only []; omega)
  rw [hbl] at k2
  obtain ⟨y4, hy4⟩ : ∃ y, y = { y3 with gh := y3.gh + (2 * h + 1), t := y3.t + (2 * h + 1) } := ⟨_, rfl⟩
  rw [← hy4] at k2
  have hG4 : y4.gw.drop y4.gh = (List.ofFn g.weight).flatMap (pairW h) ++ rest := by
    rw [hy4, hy3]
    have := ListEval.drop_add_of_append hG2
    rw [show y2.gh + (2 * h + 1) = y2.gh + (frameP (binary h (-(-g.threshold)).toNat)).length + 1 by simp [hbl]; ring]
    exact ListEval.drop_succ_of_cons this
  -- the coordinates
  have cl := coordLoop_spec cap h bu bv restC restU restV rest restP restN hc hR (List.ofFn g.weight) (List.ofFn c)
    (List.ofFn u) (List.ofFn v) y4 (-g.threshold).toNat (-(-g.threshold)).toNat (by simp) (by simp) (by simp)
    (by rw [hy4, hy3, hy2, hy1]; simp only []; rw [hih, hC]; simp)
    (by rw [hy4, hy3, hy2, hy1]; simp only []; rw [hih, hU]; simp)
    (by rw [hy4, hy3, hy2, hy1]; simp only []; rw [hih, hV]; simp)
    hG4 (by rw [hy4, hy3, hy2, hy1, hwl, ← hM]; simp only []; omega) (by rw [hy4, hy3, hy2, hy1])
    (by rw [hy4, hy3]) (by rw [hy4, hy3, hy2, hy1]; exact hf) (by rw [hy4, hy3, hy2, hy1]; exact hx)
    (by rw [hy4, hy3, hy2, hy1, hwl]; simp only []; omega) (by rw [hy4, hy3, hy2, hy1, hwl, ← hM]; simp only []; omega)
  rw [hwl, cornerIn_ofFn] at cl
  generalize hPP : (-g.threshold).toNat + posAcc (List.ofFn g.weight)
    (List.ofFn (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i))) = PP at cl
  generalize hNN : (-(-g.threshold)).toNat + negAcc (List.ofFn g.weight)
    (List.ofFn (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i))) = NN at cl
  rw [← hM] at cl
  obtain ⟨y5, hy5⟩ : ∃ y, y = { y4 with
                                 ih := y4.ih + 2 * n
                                 gh := y4.gh + M
                                 t := y4.t + M
                                 pos := frameP (binary h PP) ++ false :: restP
                                 neg := frameP (binary h NN) ++ false :: restN } := ⟨_, rfl⟩
  rw [← hy5] at cl
  -- compare
  have cm := cmpP_spec cap h y5 PP NN restP restN (by rw [hy5]) (by rw [hy5])
    (by rw [hy5, hy4, hy3, hy2, hy1]; exact hf) hc hR
  have hPPl : PP < 2 ^ h := by
    rw [← hPP]; have := posAcc_le (List.ofFn g.weight) (List.ofFn (xorInput (xorInput c (fun i => bu && u i))
      (fun i => bv && v i))); omega
  have hNNl : NN < 2 ^ h := by
    rw [← hNN]; have := negAcc_le (List.ofFn g.weight) (List.ofFn (xorInput (xorInput c (fun i => bu && u i))
      (fun i => bv && v i))); omega
  have hbit : decide (NN % 2 ^ h ≤ PP % 2 ^ h) =
      g.eval (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i)) := by
    rw [Nat.mod_eq_of_lt hPPl, Nat.mod_eq_of_lt hNNl, eval_acc, hPP, hNN]
  rw [hbit] at cm
  generalize hbt : g.eval (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i)) = bit at cm
  -- emit
  have em := emitP_spec cap { y5 with f := bit.toNat } d r b0 b1 bit
    (by rw [hy5, hy4, hy3, hy2, hy1]; exact hout) (by rw [hy5, hy4, hy3, hy2, hy1]; exact hoh) rfl hc
    (by rw [hy5, hy4, hy3, hy2, hy1]; simp only []; omega)
  -- return C, U, V
  have rw1 := rewI_spec cap (2 * n) { { y5 with f := bit.toNat } with
    out := frameP (d ++ [bit]) ++ r, oh := ({ y5 with f := bit.toNat } : CSt).oh + 2, f := 0 }
    (by rw [hy5, hy4, hy3, hy2, hy1]; simp only []; omega) hnc
  refine ⟨PP, NN, WExec.cast cap (WExec.seq l1 (WExec.seq k1 (WExec.seq l2 (WExec.seq k2 (WExec.seq cl
    (WExec.seq cm (WExec.seq em rw1))))))) ?_ ?_⟩
  · rw [hy5, hy4, hy3, hy2, hy1]
    congr 1
    simp only [hih, hf]
    congr 1 <;> ring
  · unfold coreCost; rw [hM] at *; nlinarith

/-! ## One gate -/

/-- A corner that returns the table to the gate's record. -/
def cornerR (bu bv : Bool) : CProg := .seq (core bu bv) (WM.rewind sG rT)

/-- The last corner: the table stays past the record, its offset joins `G`. -/
def cornerL : CProg := .seq (core false false) (WM.move rT rG)

theorem cornerR_spec (h : ℕ) (bu bv : Bool) {n : ℕ} (g : NormalizedThresholdGate n) (c u v : BitInput n) (x : CSt)
    (A B : ℕ) (restP restN rest restC restU restV d r : List Bool) (b0 b1 : Bool)
    (hG : x.gw.drop x.gh = pairW h (-g.threshold) ++ ((List.ofFn g.weight).flatMap (pairW h) ++ rest))
    (hgh : x.gh + (n + 1) * (2 * (2 * h + 1)) ≤ x.gw.length)
    (hC : x.cw = frameP (List.ofFn c) ++ false :: restC) (hU : x.uw = frameP (List.ofFn u) ++ restU)
    (hV : x.vw = frameP (List.ofFn v) ++ restV) (hih : x.ih = 0)
    (hp : x.pos = frameP (binary h A) ++ false :: restP) (hn : x.neg = frameP (binary h B) ++ false :: restN)
    (hout : x.out = frameP d ++ b0 :: b1 :: r) (hoh : x.oh = 2 * d.length)
    (hf : x.f = 0) (hx : x.x = 0) (ht : x.t = 0) (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) (hnc : 2 * n ≤ cap)
    (hK : (n + 1) * (2 * (2 * h + 1)) ≤ cap) (ho : x.oh + 2 ≤ cap)
    (hov : (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) :
    ∃ A' B' : ℕ, WExec cap (cornerR bu bv) x.w
      { x with
        pos := frameP (binary h A') ++ false :: restP
        neg := frameP (binary h B') ++ false :: restN
        out := frameP (d ++ [g.eval (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i))]) ++ r
        oh := x.oh + 2 }.w (coreCost h n + 5 * ((n + 1) * (2 * (2 * h + 1))) + 2) := by
  obtain ⟨A', B', s1⟩ := core_spec cap h bu bv g c u v x (binary h A) (binary h B) restP restN rest restC restU restV
    d r b0 b1 hG hgh hC hU hV hih hp hn (binary_length' h A) (binary_length' h B) hout hoh hf hx hc hR hnc
    (by rw [ht]; omega) ho hov
  refine ⟨A', B', ?_⟩
  have s2 := wrewind_spec cap sG rT ((n + 1) * (2 * (2 * h + 1)))
    { x with
      gh := x.gh + (n + 1) * (2 * (2 * h + 1))
      t := x.t + (n + 1) * (2 * (2 * h + 1))
      pos := frameP (binary h A') ++ false :: restP
      neg := frameP (binary h B') ++ false :: restN
      out := frameP (d ++ [g.eval (xorInput (xorInput c (fun i => bu && u i)) (fun i => bv && v i))]) ++ r
      oh := x.oh + 2 }.w (by simp [ht]) (by simp [ht]; omega)
  rw [c_rewT'] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  congr 1; simp [ht]

theorem cornerL_spec (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) (c u v : BitInput n) (x : CSt)
    (A B : ℕ) (restP restN rest restC restU restV d r : List Bool) (b0 b1 : Bool)
    (hG : x.gw.drop x.gh = pairW h (-g.threshold) ++ ((List.ofFn g.weight).flatMap (pairW h) ++ rest))
    (hgh : x.gh + (n + 1) * (2 * (2 * h + 1)) ≤ x.gw.length)
    (hC : x.cw = frameP (List.ofFn c) ++ false :: restC) (hU : x.uw = frameP (List.ofFn u) ++ restU)
    (hV : x.vw = frameP (List.ofFn v) ++ restV) (hih : x.ih = 0)
    (hp : x.pos = frameP (binary h A) ++ false :: restP) (hn : x.neg = frameP (binary h B) ++ false :: restN)
    (hout : x.out = frameP d ++ b0 :: b1 :: r) (hoh : x.oh = 2 * d.length)
    (hf : x.f = 0) (hx : x.x = 0) (ht : x.t = 0) (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) (hnc : 2 * n ≤ cap)
    (hK : x.g + (n + 1) * (2 * (2 * h + 1)) ≤ cap) (ho : x.oh + 2 ≤ cap)
    (hov : (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) :
    ∃ A' B' : ℕ, WExec cap cornerL x.w
      { x with
        gh := x.gh + (n + 1) * (2 * (2 * h + 1))
        g := x.g + (n + 1) * (2 * (2 * h + 1))
        pos := frameP (binary h A') ++ false :: restP
        neg := frameP (binary h B') ++ false :: restN
        out := frameP (d ++ [g.eval (xorInput (xorInput c (fun i => false && u i)) (fun i => false && v i))]) ++ r
        oh := x.oh + 2 }.w (coreCost h n + 7 * ((n + 1) * (2 * (2 * h + 1))) + 2) := by
  obtain ⟨A', B', s1⟩ := core_spec cap h false false g c u v x (binary h A) (binary h B) restP restN rest restC restU
    restV d r b0 b1 hG hgh hC hU hV hih hp hn (binary_length' h A) (binary_length' h B) hout hoh hf hx hc hR hnc
    (by rw [ht]; omega) ho hov
  refine ⟨A', B', ?_⟩
  have s2 := wmove_spec cap rT rG (by decide) ((n + 1) * (2 * (2 * h + 1)))
    { x with
      gh := x.gh + (n + 1) * (2 * (2 * h + 1))
      t := x.t + (n + 1) * (2 * (2 * h + 1))
      pos := frameP (binary h A') ++ false :: restP
      neg := frameP (binary h B') ++ false :: restN
      out := frameP (d ++ [g.eval (xorInput (xorInput c (fun i => false && u i)) (fun i => false && v i))]) ++ r
      oh := x.oh + 2 }.w (by simp [ht]) (by simp [ht]; omega) (by simp [ht]; omega)
  rw [c_moveTG] at s2
  refine WExec.cast cap (WExec.seq s1 s2) ?_ (by omega)
  congr 1; simp [ht]

/-- One gate: the marker, then its four corners. -/
def gateP : CProg :=
  .seq (WM.fwdC sG rG) (.seq (cornerR true true) (.seq (cornerR true false) (.seq (cornerR false true) cornerL)))

/-- The gate cost. -/
def gateCost (h n : ℕ) : ℕ := 4 * coreCost h n + 22 * ((n + 1) * (2 * (2 * h + 1))) + 20

theorem ofFn_corners {n : ℕ} (T : BitInput n → Bool) (c u v : BitInput n) :
    List.ofFn (corners T c u v) =
      [T (xorInput (xorInput c (fun i => true && u i)) (fun i => true && v i)),
       T (xorInput (xorInput c (fun i => true && u i)) (fun i => false && v i)),
       T (xorInput (xorInput c (fun i => false && u i)) (fun i => true && v i)),
       T (xorInput (xorInput c (fun i => false && u i)) (fun i => false && v i))] := by
  obtain ⟨e0, e1, e2, e3⟩ := corner_in T c u v
  simp [List.ofFn_succ, e0, e1, e2, e3]

theorem gate_spec (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) (c u v : BitInput n) (x : CSt)
    (A B : ℕ) (restP restN rest restC restU restV d r : List Bool) (y0 y1 y2 y3 y4 y5 y6 y7 : Bool)
    (hG : x.gw.drop x.gh = gateW h g ++ rest)
    (hgh : x.gh + 1 + (n + 1) * (2 * (2 * h + 1)) ≤ x.gw.length)
    (hC : x.cw = frameP (List.ofFn c) ++ false :: restC) (hU : x.uw = frameP (List.ofFn u) ++ restU)
    (hV : x.vw = frameP (List.ofFn v) ++ restV) (hih : x.ih = 0)
    (hp : x.pos = frameP (binary h A) ++ false :: restP) (hn : x.neg = frameP (binary h B) ++ false :: restN)
    (hout : x.out = frameP d ++ y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: r) (hoh : x.oh = 2 * d.length)
    (hf : x.f = 0) (hx : x.x = 0) (ht : x.t = 0) (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) (hnc : 2 * n ≤ cap)
    (hK : x.g + 1 + (n + 1) * (2 * (2 * h + 1)) ≤ cap) (ho : x.oh + 8 ≤ cap)
    (hov : (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) :
    ∃ A' B' : ℕ, WExec cap gateP x.w
      { x with
        gh := x.gh + (1 + (n + 1) * (2 * (2 * h + 1)))
        g := x.g + (1 + (n + 1) * (2 * (2 * h + 1)))
        pos := frameP (binary h A') ++ false :: restP
        neg := frameP (binary h B') ++ false :: restN
        out := frameP (d ++ List.ofFn (corners g.eval c u v)) ++ r
        oh := x.oh + 8 }.w (gateCost h n) := by
  have s0 := wfwdC_spec cap sG rG x.w (by simp; omega)
  rw [c_fwdG] at s0
  obtain ⟨z0, hz0⟩ : ∃ z, z = { x with gh := x.gh + 1, g := x.g + 1 } := ⟨_, rfl⟩
  rw [← hz0] at s0
  have hG0 : z0.gw.drop z0.gh = pairW h (-g.threshold) ++ ((List.ofFn g.weight).flatMap (pairW h) ++ rest) := by
    rw [hz0]
    have h1 : x.gw.drop x.gh = true :: (pairW h (-g.threshold) ++ ((List.ofFn g.weight).flatMap (pairW h) ++ rest)) := by
      rw [hG]; simp [gateW]
    exact ListEval.drop_succ_of_cons h1
  -- corner (1,1)
  obtain ⟨A1, B1, c1⟩ := cornerR_spec cap h true true g c u v z0 A B restP restN rest restC restU restV d
    (y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: r) y0 y1 hG0 (by rw [hz0]; simp only []; omega) (by rw [hz0]; exact hC)
    (by rw [hz0]; exact hU) (by rw [hz0]; exact hV) (by rw [hz0]; exact hih) (by rw [hz0]; exact hp)
    (by rw [hz0]; exact hn) (by rw [hz0]; exact hout) (by rw [hz0]; exact hoh) (by rw [hz0]; exact hf)
    (by rw [hz0]; exact hx) (by rw [hz0]; exact ht) hc hR hnc (by omega) (by rw [hz0]; simp only []; omega) hov
  generalize he0 : g.eval (xorInput (xorInput c (fun i => true && u i)) (fun i => true && v i)) = e0 at c1
  obtain ⟨z1, hz1⟩ : ∃ z, z = { z0 with
                                pos := frameP (binary h A1) ++ false :: restP
                                neg := frameP (binary h B1) ++ false :: restN
                                out := frameP (d ++ [e0]) ++ y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: r
                                oh := z0.oh + 2 } := ⟨_, rfl⟩
  rw [← hz1] at c1
  -- corner (1,0)
  obtain ⟨A2, B2, c2⟩ := cornerR_spec cap h true false g c u v z1 A1 B1 restP restN rest restC restU restV (d ++ [e0])
    (y4 :: y5 :: y6 :: y7 :: r) y2 y3 (by rw [hz1]; exact hG0) (by rw [hz1, hz0]; simp only []; omega)
    (by rw [hz1, hz0]; exact hC) (by rw [hz1, hz0]; exact hU) (by rw [hz1, hz0]; exact hV)
    (by rw [hz1, hz0]; exact hih) (by rw [hz1]) (by rw [hz1]) (by rw [hz1]) (by rw [hz1, hz0]; simp [hoh]; omega)
    (by rw [hz1, hz0]; exact hf) (by rw [hz1, hz0]; exact hx) (by rw [hz1, hz0]; exact ht) hc hR hnc (by omega)
    (by rw [hz1, hz0]; simp only []; omega) hov
  generalize he1 : g.eval (xorInput (xorInput c (fun i => true && u i)) (fun i => false && v i)) = e1 at c2
  obtain ⟨z2, hz2⟩ : ∃ z, z = { z1 with
                                pos := frameP (binary h A2) ++ false :: restP
                                neg := frameP (binary h B2) ++ false :: restN
                                out := frameP (d ++ [e0] ++ [e1]) ++ y4 :: y5 :: y6 :: y7 :: r
                                oh := z1.oh + 2 } := ⟨_, rfl⟩
  rw [← hz2] at c2
  -- corner (0,1)
  obtain ⟨A3, B3, c3⟩ := cornerR_spec cap h false true g c u v z2 A2 B2 restP restN rest restC restU restV
    (d ++ [e0] ++ [e1]) (y6 :: y7 :: r) y4 y5 (by rw [hz2, hz1]; exact hG0) (by rw [hz2, hz1, hz0]; simp only []; omega)
    (by rw [hz2, hz1, hz0]; exact hC) (by rw [hz2, hz1, hz0]; exact hU) (by rw [hz2, hz1, hz0]; exact hV)
    (by rw [hz2, hz1, hz0]; exact hih) (by rw [hz2]) (by rw [hz2]) (by rw [hz2])
    (by rw [hz2, hz1, hz0]; simp [hoh]; omega) (by rw [hz2, hz1, hz0]; exact hf) (by rw [hz2, hz1, hz0]; exact hx)
    (by rw [hz2, hz1, hz0]; exact ht) hc hR hnc (by omega) (by rw [hz2, hz1, hz0]; simp only []; omega) hov
  generalize he2 : g.eval (xorInput (xorInput c (fun i => false && u i)) (fun i => true && v i)) = e2 at c3
  obtain ⟨z3, hz3⟩ : ∃ z, z = { z2 with
                                pos := frameP (binary h A3) ++ false :: restP
                                neg := frameP (binary h B3) ++ false :: restN
                                out := frameP (d ++ [e0] ++ [e1] ++ [e2]) ++ y6 :: y7 :: r
                                oh := z2.oh + 2 } := ⟨_, rfl⟩
  rw [← hz3] at c3
  -- corner (0,0)
  obtain ⟨A4, B4, c4⟩ := cornerL_spec cap h g c u v z3 A3 B3 restP restN rest restC restU restV
    (d ++ [e0] ++ [e1] ++ [e2]) r y6 y7 (by rw [hz3, hz2, hz1]; exact hG0)
    (by rw [hz3, hz2, hz1, hz0]; simp only []; omega) (by rw [hz3, hz2, hz1, hz0]; exact hC)
    (by rw [hz3, hz2, hz1, hz0]; exact hU) (by rw [hz3, hz2, hz1, hz0]; exact hV)
    (by rw [hz3, hz2, hz1, hz0]; exact hih) (by rw [hz3]) (by rw [hz3]) (by rw [hz3])
    (by rw [hz3, hz2, hz1, hz0]; simp [hoh]; omega) (by rw [hz3, hz2, hz1, hz0]; exact hf)
    (by rw [hz3, hz2, hz1, hz0]; exact hx) (by rw [hz3, hz2, hz1, hz0]; exact ht) hc hR hnc
    (by rw [hz3, hz2, hz1, hz0]; simp only []; omega) (by rw [hz3, hz2, hz1, hz0]; simp only []; omega) hov
  generalize he3 : g.eval (xorInput (xorInput c (fun i => false && u i)) (fun i => false && v i)) = e3 at c4
  refine ⟨A4, B4, WExec.cast cap (WExec.seq s0 (WExec.seq c1 (WExec.seq c2 (WExec.seq c3 c4)))) ?_ ?_⟩
  · rw [hz3, hz2, hz1, hz0, ofFn_corners, he0, he1, he2, he3]
    congr 1
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    congr 1 <;> omega
  · unfold gateCost; omega

/-! ## All gates -/

theorem gateW_length (h : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) :
    (gateW h g).length = 1 + (n + 1) * (2 * (2 * h + 1)) := by
  unfold gateW
  rw [List.length_cons, List.length_append, pairW_length, List.length_flatMap]
  simp only [pairW_length, List.map_const', List.length_ofFn, List.sum_replicate, smul_eq_mul]
  ring

/-- The gate loop. -/
def gatesL : CProg := .whs sG gateP

theorem gatesL_spec (h : ℕ) {n : ℕ} (c u v : BitInput n) (restP restN rest restC restU restV r : List Bool)
    (hc : 1 ≤ cap) (hR : 2 * h ≤ cap) (hnc : 2 * n ≤ cap) :
    ∀ (G : List (NormalizedThresholdGate n)) (x : CSt) (A B : ℕ) (d ys : List Bool),
      x.gw.drop x.gh = G.flatMap (gateW h) ++ false :: rest →
      x.gh + G.length * (1 + (n + 1) * (2 * (2 * h + 1))) + 1 ≤ x.gw.length →
      x.cw = frameP (List.ofFn c) ++ false :: restC → x.uw = frameP (List.ofFn u) ++ restU →
      x.vw = frameP (List.ofFn v) ++ restV → x.ih = 0 →
      x.pos = frameP (binary h A) ++ false :: restP → x.neg = frameP (binary h B) ++ false :: restN →
      x.out = frameP d ++ ys ++ r → ys.length = 8 * G.length → x.oh = 2 * d.length →
      x.f = 0 → x.x = 0 → x.t = 0 →
      x.g + G.length * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ cap → x.oh + 8 * G.length ≤ cap →
      (∀ g ∈ G, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
        (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) →
      ∃ A' B' : ℕ, WExec cap gatesL x.w
        { x with
          gh := x.gh + G.length * (1 + (n + 1) * (2 * (2 * h + 1)))
          g := x.g + G.length * (1 + (n + 1) * (2 * (2 * h + 1)))
          pos := frameP (binary h A') ++ false :: restP
          neg := frameP (binary h B') ++ false :: restN
          out := frameP (d ++ cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ r
          oh := x.oh + 8 * G.length }.w (G.length * (gateCost h n + 2) + 1)
  | [], x, A, B, d, ys, hG, _, _, _, _, _, hp, hn, hout, hys, _, _, _, _, _, _, _ => by
    have e : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hys)
    subst e
    have hb : readTapeBit x.gw x.gh = false := ListEval.read_of_cons (by simpa using hG)
    refine ⟨A, B, WExec.cast cap (WExec.whsF hb) ?_ (by simp)⟩
    congr 1
    cases x
    simp only [] at hp hn hout
    simp [hp, hn, hout, cornerWord]
  | g :: G, x, A, B, d, ys, hG, hgh, hC, hU, hV, hih, hp, hn, hout, hys, hoh, hf, hx, ht, hK, ho, hov => by
    obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, ys', rfl⟩ :
        ∃ y0 y1 y2 y3 y4 y5 y6 y7 ys', ys = y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: ys' := by
      rcases ys with _ | ⟨y0, _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, _ | ⟨y5, _ | ⟨y6, _ | ⟨y7, ys'⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        simp at hys <;> try omega
      exact ⟨y0, y1, y2, y3, y4, y5, y6, y7, ys', rfl⟩
    simp only [List.length_cons] at hys hgh hK ho
    rw [Nat.succ_mul] at hgh hK
    have hG0 : x.gw.drop x.gh = gateW h g ++ (G.flatMap (gateW h) ++ false :: rest) := by simpa using hG
    obtain ⟨A1, B1, s1⟩ := gate_spec cap h g c u v x A B restP restN (G.flatMap (gateW h) ++ false :: rest) restC restU
      restV d (ys' ++ r) y0 y1 y2 y3 y4 y5 y6 y7 hG0 (by omega) hC hU hV hih hp hn (by rw [hout]; simp) hoh hf hx ht
      hc hR hnc (by omega) (by omega) (hov g List.mem_cons_self)
    obtain ⟨z, hz⟩ : ∃ z, z = { x with
                                gh := x.gh + (1 + (n + 1) * (2 * (2 * h + 1)))
                                g := x.g + (1 + (n + 1) * (2 * (2 * h + 1)))
                                pos := frameP (binary h A1) ++ false :: restP
                                neg := frameP (binary h B1) ++ false :: restN
                                out := frameP (d ++ List.ofFn (corners g.eval c u v)) ++ (ys' ++ r)
                                oh := x.oh + 8 } := ⟨_, rfl⟩
    rw [← hz] at s1
    have hGz : z.gw.drop z.gh = G.flatMap (gateW h) ++ false :: rest := by
      rw [hz]
      have := ListEval.drop_add_of_append hG0
      rwa [gateW_length] at this
    obtain ⟨A2, B2, s2⟩ := gatesL_spec h c u v restP restN rest restC restU restV r hc hR hnc G z A1 B1
      (d ++ List.ofFn (corners g.eval c u v)) ys' hGz (by rw [hz]; simp only []; omega)
      (by rw [hz]; exact hC) (by rw [hz]; exact hU) (by rw [hz]; exact hV) (by rw [hz]; exact hih) (by rw [hz])
      (by rw [hz]) (by rw [hz, List.append_assoc]) (by omega) (by rw [hz]; simp [hoh]; omega) (by rw [hz]; exact hf)
      (by rw [hz]; exact hx) (by rw [hz]; exact ht) (by rw [hz]; simp only []; omega)
      (by rw [hz]; simp only []; omega) (fun g' hg' => hov g' (List.mem_cons_of_mem g hg'))
    have hb : readTapeBit x.gw x.gh = true := ListEval.read_of_cons (by simpa [gateW] using hG0)
    refine ⟨A2, B2, WExec.cast cap (WExec.whsT hb s1 s2) ?_ ?_⟩
    · rw [hz]
      congr 1
      simp only [List.map_cons, cornerWord, List.flatMap_cons, List.append_assoc, List.length_cons, Nat.succ_mul]
      congr 1 <;> omega
    · simp only [List.length_cons, Nat.succ_mul]; omega

/-- **The corner-word writer**: all gates, then the table and the output are rewound. -/
def cw : CProg := .seq gatesL (.seq (WM.rewind sG rG) (WM.rewind sO rO))

/-- The writer's cost for `m` gates on `n` inputs with `h`-bit accumulators. -/
def cwCost (h n m : ℕ) : ℕ := m * (gateCost h n + 2) + 5 * (m * (1 + (n + 1) * (2 * (2 * h + 1)))) + 40 * m + 10

/-- **Stage 2, the corner word of a gate list at a sampled pair**: from the gate table `gatesW h G` (stream `G`, at
any origin), the framed assignments `c, u, v` (from `0`), stale `h`-bit accumulators and a stale output of `8|G|`
cells before a `false`, the output becomes `frameP (cornerWord (G.map eval) c u v)` before that `false`; the table and
the output are rewound, the counters and flags are `0` again. `h` must bound `θ^∓ + Σ|w_i|` for every gate. -/
theorem cw_spec (h : ℕ) {n : ℕ} (G : List (NormalizedThresholdGate n)) (c u v : BitInput n) (x : CSt) (A B : ℕ)
    (restP restN rest restC restU restV r ys : List Bool)
    (hG : x.gw.drop x.gh = gatesW h G ++ rest)
    (hgh : x.gh + G.length * (1 + (n + 1) * (2 * (2 * h + 1))) + 1 ≤ x.gw.length)
    (hC : x.cw = frameP (List.ofFn c) ++ false :: restC) (hU : x.uw = frameP (List.ofFn u) ++ restU)
    (hV : x.vw = frameP (List.ofFn v) ++ restV) (hih : x.ih = 0)
    (hp : x.pos = frameP (binary h A) ++ false :: restP) (hn : x.neg = frameP (binary h B) ++ false :: restN)
    (hout : x.out = ys ++ false :: r) (hys : ys.length = 8 * G.length) (hoh : x.oh = 0)
    (hf : x.f = 0) (hx : x.x = 0) (ht : x.t = 0) (hg : x.g = 0) (hc : 1 ≤ cap) (hR : 2 * h ≤ cap)
    (hnc : 2 * n ≤ cap) (hK : G.length * (1 + (n + 1) * (2 * (2 * h + 1))) ≤ cap) (ho : 8 * G.length ≤ cap)
    (hov : ∀ g ∈ G, (-g.threshold).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h ∧
      (-(-g.threshold)).toNat + ((List.ofFn g.weight).map Int.natAbs).sum < 2 ^ h) :
    ∃ A' B' : ℕ, WExec cap cw x.w
      { x with
        pos := frameP (binary h A') ++ false :: restP
        neg := frameP (binary h B') ++ false :: restN
        out := frameP (cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ false :: r }.w
      (cwCost h n G.length) := by
  obtain ⟨A', B', s1⟩ := gatesL_spec cap h c u v restP restN rest restC restU restV (false :: r) hc hR hnc G x A B [] ys
    (by rw [hG]; simp [gatesW]) hgh hC hU hV hih hp hn (by rw [hout]; simp) hys (by rw [hoh]; rfl) hf hx ht
    (by rw [hg]; omega) (by rw [hoh]; omega) hov
  refine ⟨A', B', ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, z = { x with
                              gh := x.gh + G.length * (1 + (n + 1) * (2 * (2 * h + 1)))
                              g := x.g + G.length * (1 + (n + 1) * (2 * (2 * h + 1)))
                              pos := frameP (binary h A') ++ false :: restP
                              neg := frameP (binary h B') ++ false :: restN
                              out := frameP ([] ++ cornerWord (G.map NormalizedThresholdGate.eval) c u v) ++ false :: r
                              oh := x.oh + 8 * G.length } := ⟨_, rfl⟩
  rw [← hz] at s1
  have s2 := wrewind_spec cap sG rG (G.length * (1 + (n + 1) * (2 * (2 * h + 1)))) z.w (by rw [hz]; simp [hg])
    (by rw [hz]; simp [hg]; omega)
  rw [c_rewG'] at s2
  obtain ⟨z2, hz2⟩ : ∃ y, y = { z with gh := z.gh - G.length * (1 + (n + 1) * (2 * (2 * h + 1))), g := 0 } :=
    ⟨_, rfl⟩
  rw [← hz2] at s2
  have s3 := wrewind_spec cap sO rO (8 * G.length) z2.w (by rw [hz2, hz]; simp [hoh]) (by rw [hz2, hz]; simp [hoh]; omega)
  rw [c_rewO' _ _ (by rw [hz2, hz]; simp [hoh])] at s3
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by unfold cwCost; omega)
  rw [hz2, hz]; congr 1; simp [hg, hoh]

end NearCubicWires.WireExponent3_5.FinalPass.Corner
