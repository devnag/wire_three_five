import Proof.Wire_3_5.Primitive.SeedFix.NwB6
import Proof.Wire_3_5.Primitive.Writers.GapNums

/-! # NW phase (b), part 7: W6's four numbers and `2^{sb}` in registers

* **`portW s c`** (`port_spec`): a unary port `1^v` read into `c`, the stream rewound; **`ports4W`**
  (`ports4_spec`): four ports into `|𝒢|, cut, #primes, Σp` (`440 … 443`).
* **`gapW`** (`gap_spec`): the gap block `K = 400 … 431` set to `(cap_T, 2(n+1)^{26}, f_e·L)` from `Hb 13`, `dN`,
  `sFL`, then `gapNumsW`: `2^{sb}` in `rSB = K 21`, every register outside `K` and `rK5` kept.

Paper quantity of the main types: the inputs `|𝒢|`, `cut`, `#primes`, `Σp`, `|E| = 2^{sb}` of phase (b)'s value
`V = |PrimeIndex(cut)|·|E|·Q` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine

def rR : Fin LNR := ⟨463, by decide⟩
def rK5 : Fin LNR := ⟨464, by decide⟩

/-- The gap numbers' block `K = 400 … 431`. -/
def K32 : Fin 32 ↪ Fin LNR :=
  ⟨fun i => ⟨400 + i.val, by have := i.isLt; show 400 + i.val < 512; omega⟩, fun i j h => by
    have := congrArg Fin.val h; exact Fin.ext (by simp at this; omega)⟩

theorem K32_val (i : Fin 32) : (K32 i).val = 400 + i.val := rfl

theorem K32_21 : K32 21 = rSB := rfl

theorem K32_ne (r : Fin LNR) (hr : r.val < 400 ∨ 432 ≤ r.val) (i : Fin 32) : r ≠ K32 i := fun h => by
  have := congrArg Fin.val h; rw [K32_val] at this; have := i.isLt; omega

def r465 : Fin LNR := ⟨465, by decide⟩
def r466 : Fin LNR := ⟨466, by decide⟩
def r467 : Fin LNR := ⟨467, by decide⟩

/-- The power block `(n+1, K₁, t, u, w)`. -/
def PW : Fin 5 ↪ Fin LNR := ⟨![rK5, K32 1, r465, r466, r467], by decide⟩

theorem PW_0 : PW 0 = rK5 := rfl
theorem PW_1 : PW 1 = K32 1 := rfl
theorem PW_2 : PW 2 = r465 := rfl
theorem PW_3 : PW 3 = r466 := rfl
theorem PW_4 : PW 4 = r467 := rfl

variable (cap : ℕ) (x : ℕ)

/-- Register bookkeeping: `setv` chains at the literal registers. -/
local macro "vsimp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := {decide := true}) [WState.setv_val, Function.update_apply, $hs,*])

/-- Read the unary port `s` into `c`, rewind it. -/
def portW (s : Fin (LNS x + 1)) (c : Fin LNR) : WM (LNS x) LNR :=
  .seq (SymDec.readUW s c) (.seq (FinalPass.Hash4.wcopyR c rR rTm) (WM.rewind s rR))

theorem port_spec (s : Fin (LNS x + 1)) (c : Fin LNR) (hcR : c ≠ rR) (hcT : c ≠ rTm) (v : ℕ)
    (σ : WState (LNS x) LNR) (hst : σ.st s = List.replicate v true) (hsh : σ.sh s = 0) (hc : σ.val c = 0)
    (hR : σ.val rR = 0) (hT : σ.val rTm = 0) (hv : v ≤ cap) :
    WExec cap (portW x s c) σ (σ.setv c v) (7 * v + 1 + 1 + (UnaryPow.sq cap + 1 + (5 * v + 1))) := by
  have dRT : rR ≠ rTm := by decide
  have e1 := SymDec.readU_spec cap s c v 0 σ hst hsh hc (by omega)
  rw [Nat.zero_add] at e1
  have e2 := SparseNum.copy1 cap c rR rTm hcR hcT dRT v ((σ.seth s v).setv c v) (by simp)
    (by simp [Function.update_apply, Ne.symm hcR, hR]) (by simp [Function.update_apply, Ne.symm hcT, hT]) hv
  have e3 := wrewind_spec cap s rR v (((σ.seth s v).setv c v).setv rR v) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i = s
    · subst hi; simp [hsh]
    · simp [Function.update_apply, hi]
  · rfl
  · funext r
    by_cases hr : r = rR
    · subst hr; simp [Function.update_apply, hR, Ne.symm hcR]
    · simp [Function.update_apply, hr]
  · rfl

/-- Four ports into `|𝒢|, cut, #primes, Σp`. -/
def ports4W (s1 s2 s3 s4 : Fin (LNS x + 1)) : WM (LNS x) LNR :=
  .seq (portW x s1 rG) (.seq (portW x s2 rCU) (.seq (portW x s3 rNP) (portW x s4 rPS)))

theorem ports4_spec (s1 s2 s3 s4 : Fin (LNS x + 1)) (v1 v2 v3 v4 : ℕ) (σ : WState (LNS x) LNR)
    (h1 : σ.st s1 = List.replicate v1 true) (h2 : σ.st s2 = List.replicate v2 true)
    (h3 : σ.st s3 = List.replicate v3 true) (h4 : σ.st s4 = List.replicate v4 true)
    (k1 : σ.sh s1 = 0) (k2 : σ.sh s2 = 0) (k3 : σ.sh s3 = 0) (k4 : σ.sh s4 = 0)
    (z1 : σ.val rG = 0) (z2 : σ.val rCU = 0) (z3 : σ.val rNP = 0) (z4 : σ.val rPS = 0) (zR : σ.val rR = 0)
    (zT : σ.val rTm = 0) (c1 : v1 ≤ cap) (c2 : v2 ≤ cap) (c3 : v3 ≤ cap) (c4 : v4 ≤ cap) :
    ∃ c, WExec cap (ports4W x s1 s2 s3 s4) σ ((((σ.setv rG v1).setv rCU v2).setv rNP v3).setv rPS v4) c ∧
      c ≤ 4 * UnaryPow.sq cap + 48 * cap + 20 := by
  have e1 := port_spec cap x s1 rG (by decide) (by decide) v1 σ h1 k1 z1 zR zT c1
  have e2 := port_spec cap x s2 rCU (by decide) (by decide) v2 (σ.setv rG v1) (by simpa using h2) (by simpa using k2)
    (by vsimp [z2]) (by vsimp [zR]) (by vsimp [zT]) c2
  have e3 := port_spec cap x s3 rNP (by decide) (by decide) v3 ((σ.setv rG v1).setv rCU v2) (by simpa using h3)
    (by simpa using k3) (by vsimp [z3]) (by vsimp [zR]) (by vsimp [zT]) c3
  have e4 := port_spec cap x s4 rPS (by decide) (by decide) v4 (((σ.setv rG v1).setv rCU v2).setv rNP v3)
    (by simpa using h4) (by simpa using k4) (by vsimp [z4]) (by vsimp [zR]) (by vsimp [zT]) c4
  exact ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), by omega⟩

/-- The gap block's inputs: `K₀ := cap_T`, `K₁ := 2(n+1)^{26}`, `K₂ := f_e·L`. -/
def kSetW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR (Hb 13) (K32 0) rTm) (.seq (FinalPass.Hash4.wcopyR dN rK5 rTm) (.seq (.inc rK5)
  (.seq (UnaryPow.powConstW PW 26) (.seq (ParseNat.dbl (K32 1) rTm) (.seq (WM.clear rK5)
  (FinalPass.Hash4.wcopyR sFL (K32 2) rTm))))))

/-- **`2^{sb}` into `rSB`.** -/
def gapW : WM (LNS x) LNR := .seq (kSetW x) (GapNums.gapNumsW K32)

/-- **The gap block's inputs, run.** -/
theorem kSet_spec (σ : WState (LNS x) LNR) (capT n feL : ℕ) (hC : σ.val (Hb 13) = capT) (hN : σ.val dN = n)
    (hF : σ.val sFL = feL) (zK : ∀ i : Fin 32, σ.val (K32 i) = 0) (z5 : σ.val rK5 = 0) (z65 : σ.val r465 = 0)
    (z66 : σ.val r466 = 0) (z67 : σ.val r467 = 0) (zT : σ.val rTm = 0)
    (hcT : capT ≤ cap) (hcN : 2 * (n + 1) ^ 26 + 8 ≤ cap) (hcF : feL ≤ cap) :
    ∃ τ c, WExec cap (kSetW x) σ τ c ∧ c ≤ 130 * UnaryPow.sq cap ∧ τ.val (K32 0) = capT ∧
      τ.val (K32 1) = 2 * (n + 1) ^ 26 ∧ τ.val (K32 2) = feL ∧ (∀ i : Fin 32, 3 ≤ i.val → τ.val (K32 i) = 0) ∧
      (∀ r : Fin LNR, (r.val < 400 ∨ 432 ≤ r.val) → r ≠ rK5 → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell := by
  have hs := UnaryPow.lin_le_sq cap
  have hsq := UnaryPow.sq_ge cap
  have hp1 : 1 ≤ (n + 1) ^ 26 := Nat.one_le_pow _ _ (by omega)
  have hn1 : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have e1 := SparseNum.copy1 cap (Hb 13) (K32 0) rTm (by decide) (by decide) (by decide) capT σ hC (zK 0) zT
    (by omega)
  have e2 := SparseNum.copy1 cap dN rK5 rTm (by decide) (by decide) (by decide) n (σ.setv (K32 0) capT)
    (by vsimp [hN]) (by vsimp [z5]) (by vsimp [zT]) (by omega)
  have v2 : ((σ.setv (K32 0) capT).setv rK5 n).val rK5 = n := by vsimp []
  have e3 := WExec.inc (cap := cap) rK5 ((σ.setv (K32 0) capT).setv rK5 n) (by rw [v2]; omega)
  rw [v2] at e3
  have e4 := UnaryPow.powConstW_spec cap PW 26 (((σ.setv (K32 0) capT).setv rK5 n).setv rK5 (n + 1))
    (by rw [PW_1]; vsimp [zK 1]) (by rw [PW_2]; vsimp [z65]) (by rw [PW_3]; vsimp [z66]) (by rw [PW_4]; vsimp [z67])
    (by omega) (by rw [PW_0]; vsimp []; omega)
    (fun k hk => by
      rw [PW_0]; vsimp []
      exact le_trans (Nat.pow_le_pow_right (by omega) hk) (by omega))
  have v3 : (((σ.setv (K32 0) capT).setv rK5 n).setv rK5 (n + 1)).val rK5 = n + 1 := by vsimp []
  rw [PW_0, PW_1, v3] at e4
  have e5 := FiltNum.dbl1 cap (K32 1) rTm (by decide) ((n + 1) ^ 26)
    ((((σ.setv (K32 0) capT).setv rK5 n).setv rK5 (n + 1)).setv (K32 1) ((n + 1) ^ 26)) (by vsimp [])
    (by vsimp [zT]) (by omega)
  have e6 := wclear_spec cap rK5 (n + 1)
    (((((σ.setv (K32 0) capT).setv rK5 n).setv rK5 (n + 1)).setv (K32 1) ((n + 1) ^ 26)).setv (K32 1)
      (2 * (n + 1) ^ 26)) (by vsimp []) (by vsimp []; omega)
  have e7 := SparseNum.copy1 cap sFL (K32 2) rTm (by decide) (by decide) (by decide) feL
    ((((((σ.setv (K32 0) capT).setv rK5 n).setv rK5 (n + 1)).setv (K32 1) ((n + 1) ^ 26)).setv (K32 1)
      (2 * (n + 1) ^ 26)).setv rK5 0) (by vsimp [hF]) (by vsimp [zK 2]) (by vsimp [zT]) (by omega)
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))),
    by omega, by vsimp [], by vsimp [], by vsimp [], fun i hi => ?_, fun r hr hk => ?_, rfl, rfl, rfl⟩
  · have hne : ∀ j : Fin 32, j.val < 3 → K32 i ≠ K32 j := fun j hj h => by
      have := congrArg Fin.val h; rw [K32_val, K32_val] at this; omega
    have hk5 : K32 i ≠ rK5 := fun h => by
      have h2 := congrArg Fin.val h; rw [K32_val] at h2; have := i.isLt
      exact absurd h2 (by show 400 + i.val ≠ 464; omega)
    simp [WState.setv_val, Function.update_apply, hne 0 (by decide), hne 1 (by decide), hne 2 (by decide), hk5,
      zK i]
  · have hK := K32_ne r hr
    simp [WState.setv_val, Function.update_apply, hK, hk]

/-- **The gap numbers run**: `rSB = 2^{sb}` at `gP n cap_T (f_e·L)`; every register outside `K` and `rK5` kept. -/
theorem gap_spec (σ : WState (LNS x) LNR) (capT n feL : ℕ) (hC : σ.val (Hb 13) = capT) (hN : σ.val dN = n)
    (hF : σ.val sFL = feL) (zK : ∀ i : Fin 32, σ.val (K32 i) = 0) (z5 : σ.val rK5 = 0) (z65 : σ.val r465 = 0)
    (z66 : σ.val r466 = 0) (z67 : σ.val r467 = 0) (zT : σ.val rTm = 0) (hB1 : 1 ≤ capT)
    (hcT : capT * 32 + 2 ≤ cap) (hcN : 2 * (n + 1) ^ 26 + 8 ≤ cap) (hcF : feL + 4 ≤ cap)
    (hsc : 2 ^ ((SymDec.gP n capT feL).seedBits + 1) ≤ cap)
    (hlc : (SymDec.gP n capT feL).labelBits + (SymDec.gP n capT feL).fieldBits + (SymDec.gP n capT feL).walkLen + 512
      ≤ cap) :
    ∃ τ c, WExec cap (gapW x) σ τ c ∧ c ≤ 250 * UnaryPow.sq cap ∧ τ.val rSB = 2 ^ (SymDec.gP n capT feL).seedBits ∧
      (∀ r : Fin LNR, (r.val < 400 ∨ 432 ≤ r.val) → r ≠ rK5 → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell := by
  have hp1 : 1 ≤ (n + 1) ^ 26 := Nat.one_le_pow _ _ (by omega)
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨τ, c1, e1, c1le, k0, k1, k2, kz, kfr, kst, ksh, kcl⟩ :=
    kSet_spec cap x σ capT n feL hC hN hF zK z5 z65 z66 z67 zT (by omega) hcN (by omega)
  have e2 := GapNums.gapNums_spec cap K32 τ (SymDec.gP n capT feL) k0 k1 k2 kz hB1
    (by show 2 ≤ 2 * (n + 1) ^ 26; omega) (by omega) hcT hcN hcF hsc hlc
  refine ⟨_, _, WExec.seq e1 e2, by omega, ?_, fun r hr hk => ?_, kst, ksh, kcl⟩
  · rw [← K32_21]; simp [WState.setv_val]
  · have hK := K32_ne r hr
    rw [← kfr r hr hk]
    simp [WState.setv_val, Function.update_apply, hK]

end NearCubicWires.WireExponent3_5.PrimT.NwB
