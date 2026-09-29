import Proof.Wire_3_5.FinalPass.HashBuild

/-! # Final pass, X5: the fixed hash's seed word from its frame (P3:2150-2157)

A THR call's seed word ends with the fixed hash's bits `frame (List.ofFn s)` (`PrimAsm.Plan.seedWord`); the list-table
builder (stage 4, `Hash4.build_spec`) reads the hash's coefficients `f(2t−1), …, f(0)` as
`Hash4.seedWord ℓ₀ (coefsRev (coefVal MP s))`. **`revWord_eq`**: that word is the frame's `ℓ₀`-bit chunks read
backwards, each as `1 :: frame chunk` (`revWord`). **`seedW_spec`**: the word program `seedW` writes it from the
frame. Main declarations: `chunk`, `revWord`, **`revWord_eq`**, `seedW`, **`seedW_spec`**. Paper quantity: the fixed
hash's coefficients. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists

/-! ## The value -/

/-- Chunk `r` of a word: its bits `L·r, …, L·r + L − 1`. -/
def chunk (l : List Bool) (L r : ℕ) : List Bool := (l.drop (L * r)).take L

/-- The chunks `T−1, …, 0` of a word, each as `1 :: frame chunk`, then `0`. -/
def revWord (l : List Bool) (L T : ℕ) : List Bool :=
  ((List.range T).reverse.flatMap fun r => true :: frame (chunk l L r)) ++ [false]

theorem binary_decodeVal : ∀ (ℓ : ℕ) (G : Fin ℓ → ZMod 2),
    binary ℓ (decodeVal ℓ G) = List.ofFn fun b => decide ((G b).val = 1)
  | 0, _ => rfl
  | ℓ + 1, G => by
    have h0 : (G 0).val ≤ 1 := zmod2_val_le_one (G 0)
    have ih := binary_decodeVal ℓ (fun h => G h.succ)
    rw [decodeVal, binary, List.ofFn_succ]
    congr 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h | h <;> rw [h] <;> simp [Nat.add_mod]
    · rw [show ((G 0).val + 2 * decodeVal ℓ fun h => G h.succ) / 2 = decodeVal ℓ fun h => G h.succ by omega]
      exact ih

theorem binary_coefVal (MP : MajorantParams) (s : Fin (2 * MP.t * MP.ell0) → Bool) (r : Fin (2 * MP.t)) :
    binary MP.ell0 (MajorantBits.coefVal MP s r) = List.ofFn fun b : Fin MP.ell0 => s (finProdFinEquiv (r, b)) := by
  unfold MajorantBits.coefVal
  rw [binary_decodeVal]
  congr 1
  funext b
  cases s (finProdFinEquiv (r, b)) <;> rfl

theorem chunk_ofFn (T L : ℕ) (s : Fin (T * L) → Bool) (r : Fin T) :
    chunk (List.ofFn s) L r = List.ofFn fun b : Fin L => s (finProdFinEquiv (r, b)) := by
  have hr := r.isLt
  have hle : L * r.val + L ≤ T * L := by
    have := Nat.mul_le_mul_right L (show r.val + 1 ≤ T by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm r.val L] at this
    exact this
  apply List.ext_getElem
  · simp [chunk]; omega
  · intro i h1 h2
    simp only [chunk, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv]
    ring

theorem flatMap_range_reverse {β : Type} (f : ℕ → List β) : ∀ T : ℕ,
    (List.range T).reverse.flatMap f = (List.range T).flatMap fun i => f (T - 1 - i)
  | 0 => rfl
  | T + 1 => by
    conv_lhs => rw [List.range_succ, List.reverse_append, List.flatMap_append, flatMap_range_reverse f T]
    conv_rhs => rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Nat.add_sub_cancel, Nat.sub_zero]
    congr 1
    apply List.flatMap_congr
    intro i _
    congr 1
    omega

theorem finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

/-- **The stage-4 seed word is the frame's chunks read backwards.** -/
theorem revWord_eq (MP : MajorantParams) (s : Fin (2 * MP.t * MP.ell0) → Bool) :
    revWord (List.ofFn s) MP.ell0 (2 * MP.t) = seedWord MP.ell0 (coefsRev (MajorantBits.coefVal MP s)) := by
  unfold revWord seedWord coefsRev
  congr 1
  conv_rhs => rw [List.ofFn_eq_map, ← List.map_reverse, List.flatMap_map]
  conv_lhs => rw [← finRange_val, ← List.map_reverse, List.flatMap_map]
  apply List.flatMap_congr
  intro r _
  rw [chunk_ofFn (2 * MP.t) MP.ell0 s r, binary_coefVal]

/-! ## The frame, read two cells per bit -/

theorem frame_length' : ∀ c : List Bool, (frame c).length = 2 * c.length + 1
  | [] => rfl
  | b :: c => by rw [frame, List.length_cons, List.length_cons, frame_length' c, List.length_cons]; ring

theorem frame_pairs : ∀ c : List Bool, frame c = c.flatMap (fun b => [true, b]) ++ [false]
  | [] => rfl
  | b :: c => by rw [frame, frame_pairs c]; rfl

theorem read_frame_even : ∀ (l : List Bool) (i : ℕ), readTapeBit (frame l) (2 * i) = decide (i < l.length)
  | [], 0 => rfl
  | [], i + 1 => by simp [frame, readTapeBit]
  | b :: l, 0 => by simp [frame, readTapeBit]
  | b :: l, i + 1 => by
    have h := read_frame_even l i
    simp only [readTapeBit] at h ⊢
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, frame, List.getD_cons_succ, List.getD_cons_succ, h]
    simp

theorem read_frame_odd : ∀ (l : List Bool) (i : ℕ), i < l.length → readTapeBit (frame l) (2 * i + 1) = l.getD i false
  | [], _, h => absurd h (by simp)
  | b :: l, 0, _ => by simp [frame, readTapeBit]
  | b :: l, i + 1, h => by
    have h' := read_frame_odd l i (by simp at h; omega)
    simp only [readTapeBit] at h' ⊢
    rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring, frame, List.getD_cons_succ, List.getD_cons_succ, h']
    simp

/-- The bit pairs `[1, l_{p+i}]` for `i < k`. -/
def bitsOut (l : List Bool) (p k : ℕ) : List Bool := (List.range k).flatMap fun i => [true, l.getD (p + i) false]

theorem bitsOut_succ (l : List Bool) (p k : ℕ) :
    bitsOut l p (k + 1) = [true, l.getD p false] ++ bitsOut l (p + 1) k := by
  unfold bitsOut
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro i _
  simp only [Function.comp, Nat.succ_eq_add_one]
  congr 3
  omega

theorem bitsOut_chunk (l : List Bool) : ∀ (L p : ℕ), p + L ≤ l.length →
    bitsOut l p L = ((l.drop p).take L).flatMap (fun b => [true, b])
  | 0, p, _ => by simp [bitsOut]
  | L + 1, p, h => by
    rw [bitsOut_succ, bitsOut_chunk l L (p + 1) (by omega)]
    have hp : p < l.length := by omega
    rw [List.drop_eq_getElem_cons hp, List.take_succ_cons, List.flatMap_cons]
    simp [List.getD_eq_getElem?_getD, hp]

/-! ## The word program -/

section Prog
variable {ns nr : ℕ} (cap : ℕ)

/-- `u` appended to stream `O`, its head at the new end. -/
def appW (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) : WState ns nr :=
  (σ.sets O (σ.st O ++ u)).seth O ((σ.st O).length + u.length)

@[simp] theorem appW_st (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) :
    (appW σ O u).st = Function.update σ.st O (σ.st O ++ u) := rfl
@[simp] theorem appW_sh (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) :
    (appW σ O u).sh = Function.update σ.sh O ((σ.st O).length + u.length) := rfl
@[simp] theorem appW_val (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) : (appW σ O u).val = σ.val := rfl
@[simp] theorem appW_cell (σ : WState ns nr) (O : Fin (ns + 1)) (u : List Bool) : (appW σ O u).cell = σ.cell := rfl

theorem appW_appW (σ : WState ns nr) (O : Fin (ns + 1)) (u v : List Bool) :
    appW (appW σ O u) O v = appW σ O (u ++ v) := by
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp; ring
    · simp [Function.update_apply, hj]
  · funext j; by_cases hj : j = O
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · rfl
  · rfl

theorem appW_nil (σ : WState ns nr) (O : Fin (ns + 1)) (hO : σ.sh O = (σ.st O).length) : appW σ O [] = σ := by
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [hO]
    · simp [Function.update_apply, hj]
  · funext j; by_cases hj : j = O
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · rfl
  · rfl

theorem seth_seth (σ : WState ns nr) (i : Fin (ns + 1)) (x y : ℕ) : (σ.seth i x).seth i y = σ.seth i y :=
  WState.eq (by simp) rfl rfl rfl

theorem seth_same (σ : WState ns nr) (i : Fin (ns + 1)) : σ.seth i (σ.sh i) = σ :=
  WState.eq (by simp) rfl rfl rfl

/-- One cell appended. -/
def emit1 (O : Fin (ns + 1)) (b : Bool) : WM ns nr := .seq (.wr O b) (.fwd O)

theorem emit1_spec (O : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) :
    WExec cap (emit1 O b) σ (appW σ O [b]) 3 := by
  have h1 := WExec.wr (cap := cap) O b σ
  rw [hO, writeTapeBit_end] at h1
  have h2 := WExec.fwd (cap := cap) O (σ.sets O (σ.st O ++ [b]))
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = O
    · subst hj; simp [hO]
    · simp [Function.update_apply, hj]
  · rfl
  · rfl
  · rfl

variable (I O : Fin (ns + 1)) (rL rT C K Q N : Fin nr)

/-- The head of `I` to the end of its frame (two cells per bit). -/
def toEndW : WM ns nr := .whs I (.seq (.fwd I) (.fwd I))

theorem toEnd_spec (l : List Bool) : ∀ (k : ℕ) (σ : WState ns nr), σ.st I = frame l →
    σ.sh I + 2 * k = 2 * l.length → WExec cap (toEndW I) σ (σ.seth I (2 * l.length)) (5 * k + 1)
  | 0, σ, hs, hh => by
    have hb : wbit σ I = false := by
      unfold wbit; rw [hs, show σ.sh I = 2 * l.length by omega, read_frame_even]; simp
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    rw [show 2 * l.length = σ.sh I by omega, seth_same]
  | k + 1, σ, hs, hh => by
    have hb : wbit σ I = true := by
      unfold wbit
      rw [hs, show σ.sh I = 2 * (l.length - (k + 1)) by omega, read_frame_even]
      simp; omega
    have h1 := WExec.seq (WExec.fwd (cap := cap) I σ) (WExec.fwd (cap := cap) I (σ.seth I (σ.sh I + 1)))
    have ih := toEnd_spec l k ((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1)) (by simpa using hs)
      (by simp; omega)
    refine WExec.cast cap (WExec.whsT hb h1 ih) ?_ (by omega)
    simp [seth_seth]

/-- `2·k` cells back, `k` from `K`. -/
def backW : WM ns nr := .whr K (.seq (.dec K) (.seq (.bwd I) (.bwd I)))

theorem back_spec : ∀ (k : ℕ) (σ : WState ns nr), σ.val K = k → k ≤ cap → 2 * k ≤ σ.sh I →
    WExec cap (backW I K) σ ((σ.seth I (σ.sh I - 2 * k)).setv K 0) (7 * k + 1)
  | 0, σ, hv, _, _ => by
    refine WExec.cast cap (WExec.whrF hv) ?_ le_rfl
    rw [Nat.mul_zero, Nat.sub_zero, seth_same, ← hv, wsetv_same]
  | k + 1, σ, hv, hc, hh => by
    have d1 := WExec.dec (cap := cap) K σ (by omega)
    have d2 := WExec.bwd (cap := cap) I (σ.setv K (σ.val K - 1))
    have d3 := WExec.bwd (cap := cap) I ((σ.setv K (σ.val K - 1)).seth I ((σ.setv K (σ.val K - 1)).sh I - 1))
    have body := WExec.seq d1 (WExec.seq d2 d3)
    have ih := back_spec k (((σ.setv K (σ.val K - 1)).seth I ((σ.setv K (σ.val K - 1)).sh I - 1)).seth I
      (((σ.setv K (σ.val K - 1)).seth I ((σ.setv K (σ.val K - 1)).sh I - 1)).sh I - 1)) (by simp [hv]) (by omega)
      (by simp; omega)
    refine WExec.cast cap (WExec.whrT (by omega) body ih) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = I
      · subst hj; simp; omega
      · simp [Function.update_apply, hj]
    · rfl
    · funext j; by_cases hj : j = K
      · subst hj; simp
      · simp [Function.update_apply, hj]
    · rfl

/-- One bit pair `[1, b]` of the chunk, the head of `I` two cells on, `N` up by two. -/
def bitW : WM ns nr :=
  .seq (.dec K) (.seq (emit1 O true) (.seq (.fwd I) (.seq (.ifs I (emit1 O true) (emit1 O false))
    (.seq (.fwd I) (.seq (.inc N) (.inc N))))))

/-- `K` bit pairs. -/
def bitsW : WM ns nr := .whr K (bitW I O K N)

/-- The state after the bit pairs `p, …, p + k − 1`. -/
def bitsSt (l : List Bool) (σ : WState ns nr) (p k : ℕ) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh O ((σ.st O).length + (bitsOut l p k).length)) I (2 * (p + k)),
    Function.update σ.st O (σ.st O ++ bitsOut l p k), Function.update (Function.update σ.val K 0) N (σ.val N + 2 * k),
    σ.cell⟩

theorem bitsOut_length (l : List Bool) (p k : ℕ) : (bitsOut l p k).length = 2 * k := by
  unfold bitsOut; induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; ring

theorem bits_spec (l : List Bool) (hIO : I ≠ O) (hKN : K ≠ N) : ∀ (k : ℕ) (σ : WState ns nr) (p : ℕ),
    σ.val K = k → k ≤ cap → σ.st I = frame l → σ.sh I = 2 * p → p + k ≤ l.length →
    σ.sh O = (σ.st O).length → σ.val N + 2 * k ≤ cap →
    WExec cap (bitsW I O K N) σ (bitsSt I O K N l σ p k) (24 * k + 1)
  | 0, σ, p, hv, _, _, hh, _, hO, _ => by
    refine WExec.cast cap (WExec.whrF hv) ?_ le_rfl
    apply WState.eq
    · funext j; unfold bitsSt; by_cases h1 : j = I
      · subst h1; simp [Function.update_apply, hIO, hh]
      · by_cases h2 : j = O
        · subst h2; simp [Function.update_apply, h1, hO, bitsOut]
        · simp [Function.update_apply, h1, h2]
    · funext j; unfold bitsSt; by_cases h2 : j = O
      · subst h2; simp [bitsOut]
      · simp [Function.update_apply, h2]
    · funext r; unfold bitsSt; by_cases h1 : r = N
      · subst h1; simp [Function.update_apply]
      · by_cases h2 : r = K
        · subst h2; simp [Function.update_apply, h1, hv]
        · simp [Function.update_apply, h1, h2]
    · rfl
  | k + 1, σ, p, hv, hc, hs, hh, hl, hO, hN => by
    have hp : p < l.length := by omega
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv K k := ⟨_, rfl⟩
    have d1 : WExec cap (WM.dec K) σ σ1 1 := by
      have := WExec.dec (cap := cap) K σ (by omega); rw [hv] at this; rw [e1]; simpa using this
    have d2 := emit1_spec cap O true σ1 (by rw [e1]; simpa using hO)
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = appW σ1 O [true] := ⟨_, rfl⟩
    rw [← e2] at d2
    have d3 := WExec.fwd (cap := cap) I σ2
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.seth I (σ2.sh I + 1) := ⟨_, rfl⟩
    rw [← e3] at d3
    have h3I : σ3.st I = frame l := by rw [e3, e2, e1]; simp [Function.update_apply, hIO, hs]
    have h3h : σ3.sh I = 2 * p + 1 := by rw [e3, e2, e1]; simp [Function.update_apply, hIO, hh]
    have hb : wbit σ3 I = l.getD p false := by unfold wbit; rw [h3I, h3h, read_frame_odd l p hp]
    have h3O : σ3.sh O = (σ3.st O).length := by rw [e3, e2, e1]; simp [Function.update_apply, Ne.symm hIO]
    have d4 : WExec cap (WM.ifs I (emit1 O true) (emit1 O false)) σ3 (appW σ3 O [l.getD p false]) 4 := by
      cases hbv : l.getD p false
      · exact WExec.ifsF (by rw [hb, hbv]) (emit1_spec cap O false σ3 h3O)
      · exact WExec.ifsT (by rw [hb, hbv]) (emit1_spec cap O true σ3 h3O)
    obtain ⟨σ4, e4⟩ : ∃ τ, τ = appW σ3 O [l.getD p false] := ⟨_, rfl⟩
    rw [← e4] at d4
    have d5 := WExec.fwd (cap := cap) I σ4
    obtain ⟨σ5, e5⟩ : ∃ τ, τ = σ4.seth I (σ4.sh I + 1) := ⟨_, rfl⟩
    rw [← e5] at d5
    have h5N : σ5.val N = σ.val N := by rw [e5, e4, e3, e2, e1]; simp [Function.update_apply, Ne.symm hKN]
    have d6 := WExec.inc (cap := cap) N σ5 (by omega)
    obtain ⟨σ6, e6⟩ : ∃ τ, τ = σ5.setv N (σ5.val N + 1) := ⟨_, rfl⟩
    rw [← e6] at d6
    have d7 := WExec.inc (cap := cap) N σ6 (by rw [e6]; simp; omega)
    obtain ⟨σ7, e7⟩ : ∃ τ, τ = σ6.setv N (σ6.val N + 1) := ⟨_, rfl⟩
    rw [← e7] at d7
    have body : WExec cap (bitW I O K N) σ σ7 22 :=
      WExec.mono (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 (WExec.seq d6 d7)))))) (by omega)
    have f7K : σ7.val K = k := by rw [e7, e6, e5, e4, e3, e2, e1]; simp [Function.update_apply, hKN]
    have f7I : σ7.st I = frame l := by rw [e7, e6, e5, e4, e3, e2, e1]; simp [Function.update_apply, hIO, hs]
    have f7h : σ7.sh I = 2 * (p + 1) := by rw [e7, e6, e5, e4, e3, e2, e1]; simp [Function.update_apply, hIO, hh]; omega
    have f7O : σ7.sh O = (σ7.st O).length := by
      rw [e7, e6, e5, e4, e3, e2, e1]; simp [Function.update_apply, Ne.symm hIO]
    have f7N : σ7.val N = σ.val N + 2 := by rw [e7, e6, h5N]; simp
    have ih := bits_spec l hIO hKN k σ7 (p + 1) f7K (by omega) f7I f7h (by omega) f7O (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) body ih) ?_ (by omega)
    have eo : σ7.st O = σ.st O ++ [true, l.getD p false] := by
      rw [e7, e6, e5, e4, e3, e2, e1]; simp [Function.update_apply, Ne.symm hIO]
    have bs := bitsOut_succ l p k
    apply WState.eq
    · funext j; unfold bitsSt; by_cases h1 : j = I
      · subst h1; simp [Function.update_apply, hIO]; ring
      · by_cases h2 : j = O
        · subst h2; simp [Function.update_apply, h1, eo, bs, bitsOut_length]; ring
        · simp [Function.update_apply, h1, h2, e7, e6, e5, e4, e3, e2, e1]
    · funext j; unfold bitsSt; by_cases h2 : j = O
      · subst h2; simp [eo, bs]
      · simp [Function.update_apply, h2, e7, e6, e5, e4, e3, e2, e1]
    · funext r; unfold bitsSt; by_cases h1 : r = N
      · subst h1; simp [Function.update_apply, f7N]; ring
      · by_cases h2 : r = K
        · subst h2; simp [Function.update_apply, h1]
        · simp [Function.update_apply, h1, h2, e7, e6, e5, e4, e3, e2, e1]
    · show σ7.cell = σ.cell
      rw [e7, e6, e5, e4, e3, e2, e1]; rfl

/-- One chunk read backwards: back `2L` cells, `1`, the chunk's bit pairs, `0`, back `2L` cells. -/
def chunkW : WM ns nr :=
  .seq (Hash4.wcopyR rL K Q) (.seq (backW I K) (.seq (emit1 O true) (.seq (.inc N) (.seq (Hash4.wcopyR rL K Q)
    (.seq (bitsW I O K N) (.seq (emit1 O false) (.seq (.inc N) (.seq (Hash4.wcopyR rL K Q) (backW I K)))))))))

/-- One chunk's step count. -/
def chunkCost (L : ℕ) : ℕ := 92 * L + 33

/-- The output after `m` chunks: the chunks `T−1, …, T−m`. -/
def pre (l : List Bool) (L T m : ℕ) : List Bool :=
  (List.range m).flatMap fun i => true :: frame (chunk l L (T - 1 - i))

theorem chunk_length (l : List Bool) (L r : ℕ) (h : L * r + L ≤ l.length) : (chunk l L r).length = L := by
  simp [chunk]; omega

theorem pre_succ (l : List Bool) (L T m : ℕ) :
    pre l L T (m + 1) = pre l L T m ++ (true :: frame (chunk l L (T - 1 - m))) := by
  simp [pre, List.range_succ, List.flatMap_append]

theorem pre_length (l : List Bool) (L T : ℕ) (hl : l.length = T * L) : ∀ m, m ≤ T →
    (pre l L T m).length = m * (2 * L + 2)
  | 0, _ => by simp [pre]
  | m + 1, h => by
    rw [pre_succ, List.length_append, pre_length l L T hl m (by omega), List.length_cons, frame_length',
      chunk_length l L _ ?_]
    · ring
    · have : L * (T - 1 - m) + L = L * (T - m) := by
        rw [show T - m = T - 1 - m + 1 by omega, Nat.mul_add, Nat.mul_one]
      rw [this, hl, Nat.mul_comm T L]
      exact Nat.mul_le_mul_left _ (by omega)

/-- The state after `m` chunks. -/
def chunkSt (l : List Bool) (L T : ℕ) (σ : WState ns nr) (m : ℕ) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh O ((σ.st O).length + (pre l L T m).length)) I (2 * (L * (T - m))),
    Function.update σ.st O (σ.st O ++ pre l L T m), Function.update σ.val N (σ.val N + (pre l L T m).length),
    σ.cell⟩

theorem chunkPairs (l : List Bool) (L T m : ℕ) (hl : l.length = T * L) (hm : m < T) :
    [true] ++ bitsOut l (L * (T - m - 1)) L ++ [false] = true :: frame (chunk l L (T - 1 - m)) := by
  have hle : L * (T - m - 1) + L ≤ l.length := by
    have e : L * (T - m - 1) + L = L * (T - m) := by
      have : T - m = (T - m - 1) + 1 := by omega
      conv_rhs => rw [this, Nat.mul_add, Nat.mul_one]
    rw [e, hl, Nat.mul_comm T L]; exact Nat.mul_le_mul_left _ (by omega)
  rw [bitsOut_chunk l L _ hle, frame_pairs, chunk, show T - 1 - m = T - m - 1 by omega]
  simp

/-- The general state of the conversion: `u` appended to `O`, the head of `I` at `h`, `N` up by `v`. -/
def gSt (σ : WState ns nr) (u : List Bool) (h v : ℕ) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh O ((σ.st O).length + u.length)) I h,
    Function.update σ.st O (σ.st O ++ u), Function.update σ.val N (σ.val N + v), σ.cell⟩

theorem chunkSt_eq (l : List Bool) (L T : ℕ) (σ : WState ns nr) (m : ℕ) :
    chunkSt I O N l L T σ m = gSt I O N σ (pre l L T m) (2 * (L * (T - m))) (pre l L T m).length := rfl

section G
variable {I O N} (hIO : I ≠ O)
include hIO

theorem gSt_app (σ : WState ns nr) (u w : List Bool) (h v : ℕ) :
    appW (gSt I O N σ u h v) O w = gSt I O N σ (u ++ w) h v := by
  apply WState.eq
  · funext j; by_cases h1 : j = I
    · subst h1; simp [gSt, Function.update_apply, hIO]
    · by_cases h2 : j = O
      · subst h2; simp [gSt, Function.update_apply, h1]; ring
      · simp [gSt, Function.update_apply, h1, h2]
  · funext j; by_cases h2 : j = O
    · subst h2; simp [gSt]
    · simp [gSt, Function.update_apply, h2]
  · rfl
  · rfl

theorem gSt_inc (σ : WState ns nr) (u : List Bool) (h v : ℕ) :
    (gSt I O N σ u h v).setv N ((gSt I O N σ u h v).val N + 1) = gSt I O N σ u h (v + 1) :=
  WState.eq rfl rfl (by funext r; by_cases h1 : r = N <;> simp [gSt, Function.update_apply, h1]; ring) rfl

theorem gSt_back (K : Fin nr) (hKN : K ≠ N) (σ : WState ns nr) (hK : σ.val K = 0) (u : List Bool) (h v L : ℕ) :
    (((gSt I O N σ u h v).setv K L).seth I (((gSt I O N σ u h v).setv K L).sh I - 2 * L)).setv K 0 =
      gSt I O N σ u (h - 2 * L) v := by
  apply WState.eq
  · funext j; by_cases h1 : j = I
    · subst h1; simp [gSt, Function.update_apply, hIO]
    · simp [gSt, Function.update_apply, h1]
  · rfl
  · funext r; by_cases h1 : r = K
    · subst h1; simp [gSt, Function.update_apply, hKN, hK]
    · simp [gSt, Function.update_apply, h1]
  · rfl

theorem gSt_bits (K : Fin nr) (hKN : K ≠ N) (l : List Bool) (σ : WState ns nr) (hK : σ.val K = 0) (u : List Bool)
    (p v L : ℕ) :
    bitsSt I O K N l ((gSt I O N σ u (2 * p) v).setv K L) p L = gSt I O N σ (u ++ bitsOut l p L) (2 * (p + L)) (v + 2 * L) := by
  apply WState.eq
  · funext j; by_cases h1 : j = I
    · subst h1; simp [bitsSt, gSt, Function.update_apply, hIO]
    · by_cases h2 : j = O
      · subst h2; simp [bitsSt, gSt, Function.update_apply, h1]; ring
      · simp [bitsSt, gSt, Function.update_apply, h1, h2]
  · funext j; by_cases h2 : j = O
    · subst h2; simp [bitsSt, gSt]
    · simp [bitsSt, gSt, Function.update_apply, h2]
  · funext r; by_cases h1 : r = N
    · subst h1; simp [bitsSt, gSt, Function.update_apply, Ne.symm hKN]; ring
    · by_cases h2 : r = K
      · subst h2; simp [bitsSt, gSt, Function.update_apply, hKN, hK]
      · simp [bitsSt, gSt, Function.update_apply, h1, h2]
  · rfl

end G

section Steps
variable {I O rL K Q N} (hIO : I ≠ O) (hLK : rL ≠ K) (hLQ : rL ≠ Q) (hKQ : K ≠ Q) (hKN : K ≠ N) (hQN : Q ≠ N)
  (hLN : rL ≠ N) (l : List Bool) (L : ℕ) (σ : WState ns nr) (hs : σ.st I = frame l) (hK : σ.val K = 0)
  (hQ : σ.val Q = 0) (hL : σ.val rL = L) (hLc : L ≤ cap) (hO : σ.sh O = (σ.st O).length)
include hIO hLK hLQ hKQ hKN hQN hLN hs hK hQ hL hLc hO

theorem g_facts (u : List Bool) (h v : ℕ) :
    (gSt I O N σ u h v).val K = 0 ∧ (gSt I O N σ u h v).val Q = 0 ∧ (gSt I O N σ u h v).val rL = L ∧
      (gSt I O N σ u h v).st I = frame l ∧ (gSt I O N σ u h v).sh I = h ∧
      (gSt I O N σ u h v).sh O = ((gSt I O N σ u h v).st O).length ∧ (gSt I O N σ u h v).val N = σ.val N + v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [gSt, Function.update_apply, hKN, hQN, hLN, hK, hQ, hL, hIO, hs, Ne.symm hIO, hO]

/-- Steps 1–4 of a chunk (back `2L`, then `1`), then any continuation. -/
theorem stepA (u : List Bool) (h v : ℕ) (hh : 2 * L ≤ h) (hN : σ.val N + v < cap) (X : WM ns nr) (τ : WState ns nr)
    (c : ℕ) (hX : WExec cap X (gSt I O N σ (u ++ [true]) (h - 2 * L) (v + 1)) τ c) :
    WExec cap (.seq (Hash4.wcopyR rL K Q) (.seq (backW I K) (.seq (emit1 O true) (.seq (.inc N) X))))
      (gSt I O N σ u h v) τ (18 * L + 3 + 1 + (7 * L + 1 + 1 + (3 + 1 + (3 + 1 + c)))) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := g_facts cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO u h v
  have d1 := Hash4.wcopyR_spec cap rL K Q hLK hLQ hKQ (gSt I O N σ u h v) f1 f2 (by rw [f3]; exact hLc)
  rw [f3] at d1
  have d2 := back_spec cap I K L ((gSt I O N σ u h v).setv K L) (by simp) hLc (by simp [f5]; exact hh)
  rw [gSt_back hIO K hKN σ hK u h v L] at d2
  have d3 := emit1_spec cap O true (gSt I O N σ u (h - 2 * L) v)
    (g_facts cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO u (h - 2 * L) v).2.2.2.2.2.1
  rw [gSt_app hIO] at d3
  have d4 := WExec.inc (cap := cap) N (gSt I O N σ (u ++ [true]) (h - 2 * L) v)
    (by rw [(g_facts cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO _ _ v).2.2.2.2.2.2]; exact hN)
  rw [gSt_inc hIO] at d4
  exact WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 hX)))

/-- Steps 5–6 of a chunk (the `L` bit pairs), then any continuation. -/
theorem stepB (u : List Bool) (p v : ℕ) (hp : p + L ≤ l.length) (hN : σ.val N + v + 2 * L ≤ cap) (X : WM ns nr)
    (τ : WState ns nr) (c : ℕ) (hX : WExec cap X (gSt I O N σ (u ++ bitsOut l p L) (2 * (p + L)) (v + 2 * L)) τ c) :
    WExec cap (.seq (Hash4.wcopyR rL K Q) (.seq (bitsW I O K N) X)) (gSt I O N σ u (2 * p) v) τ
      (18 * L + 3 + 1 + (24 * L + 1 + 1 + c)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := g_facts cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO u (2 * p) v
  have d1 := Hash4.wcopyR_spec cap rL K Q hLK hLQ hKQ (gSt I O N σ u (2 * p) v) f1 f2 (by rw [f3]; exact hLc)
  rw [f3] at d1
  have d2 := bits_spec cap I O K N l hIO hKN L ((gSt I O N σ u (2 * p) v).setv K L) p (by simp) hLc
    (by simpa using f4) (by simpa using f5) hp (by simpa using f6) (by simp [Function.update_apply, Ne.symm hKN, f7]; omega)
  rw [gSt_bits hIO K hKN l σ hK u p v L] at d2
  exact WExec.seq d1 (WExec.seq d2 hX)

/-- Steps 7–10 of a chunk (`0`, back `2L`). -/
theorem stepC (u : List Bool) (h v : ℕ) (hh : 2 * L ≤ h) (hN : σ.val N + v < cap) :
    WExec cap (.seq (emit1 O false) (.seq (.inc N) (.seq (Hash4.wcopyR rL K Q) (backW I K))))
      (gSt I O N σ u h v) (gSt I O N σ (u ++ [false]) (h - 2 * L) (v + 1))
      (3 + 1 + (3 + 1 + (18 * L + 3 + 1 + (7 * L + 1)))) := by
  have f6 := (g_facts cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO u h v).2.2.2.2.2.1
  have d1 := emit1_spec cap O false (gSt I O N σ u h v) f6
  rw [gSt_app hIO] at d1
  have d2 := WExec.inc (cap := cap) N (gSt I O N σ (u ++ [false]) h v)
    (by rw [(g_facts cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO _ _ v).2.2.2.2.2.2]; exact hN)
  rw [gSt_inc hIO] at d2
  obtain ⟨f1, f2, f3, f4, f5, -, -⟩ := g_facts cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO (u ++ [false]) h
    (v + 1)
  have d3 := Hash4.wcopyR_spec cap rL K Q hLK hLQ hKQ (gSt I O N σ (u ++ [false]) h (v + 1)) f1 f2
    (by rw [f3]; exact hLc)
  rw [f3] at d3
  have d4 := back_spec cap I K L ((gSt I O N σ (u ++ [false]) h (v + 1)).setv K L) (by simp) hLc (by simp [f5]; exact hh)
  rw [gSt_back hIO K hKN σ hK _ h (v + 1) L] at d4
  exact WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))

/-- **One chunk.** -/
theorem chunk_spec (T : ℕ) (hl : l.length = T * L) (m : ℕ) (hm : m < T)
    (hN : σ.val N + (pre l L T (m + 1)).length ≤ cap) :
    WExec cap (chunkW I O rL K Q N) (chunkSt I O N l L T σ m) (chunkSt I O N l L T σ (m + 1)) (chunkCost L) := by
  have hpl := pre_length l L T hl (m + 1) (by omega)
  have hpl0 := pre_length l L T hl m (by omega)
  have hTm : 2 * (L * (T - m)) = 2 * (L * (T - m - 1)) + 2 * L := by
    have : T - m = (T - m - 1) + 1 := by omega
    conv_lhs => rw [this, Nat.mul_add, Nat.mul_one]
    ring
  have hle : L * (T - m - 1) + L ≤ l.length := by
    have e : L * (T - m - 1) + L = L * (T - m) := by
      have : T - m = (T - m - 1) + 1 := by omega
      conv_rhs => rw [this, Nat.mul_add, Nat.mul_one]
    rw [e, hl, Nat.mul_comm T L]; exact Nat.mul_le_mul_left _ (by omega)
  rw [hpl] at hN
  have hC := stepC cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO
    (pre l L T m ++ [true] ++ bitsOut l (L * (T - m - 1)) L) (2 * (L * (T - m - 1) + L))
    ((pre l L T m).length + 1 + 2 * L) (by omega) (by rw [hpl0]; nlinarith)
  have hB := stepB cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO (pre l L T m ++ [true])
    (L * (T - m - 1)) ((pre l L T m).length + 1) hle (by rw [hpl0]; nlinarith) _ _ _ hC
  have hA := stepA cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc hO (pre l L T m) (2 * (L * (T - m)))
    ((pre l L T m).length) (by rw [hTm]; omega) (by rw [hpl0]; nlinarith) _ _ _
    (by rw [show 2 * (L * (T - m)) - 2 * L = 2 * (L * (T - m - 1)) by omega]; exact hB)
  rw [chunkSt_eq, chunkSt_eq]
  refine WExec.cast cap hA ?_ (by unfold chunkCost; omega)
  have cp := chunkPairs l L T m hl hm
  have ps := pre_succ l L T m
  have hu : pre l L T m ++ [true] ++ bitsOut l (L * (T - m - 1)) L ++ [false] = pre l L T (m + 1) := by
    rw [ps, ← cp]; simp
  rw [hu, show 2 * (L * (T - m - 1) + L) - 2 * L = 2 * (L * (T - (m + 1))) by
    rw [show T - (m + 1) = T - m - 1 by omega]; omega]
  congr 1
  rw [hpl, hpl0]; ring

end Steps

/-- The chunks, `C` of them. -/
def chunksW : WM ns nr := .whr C (.seq (.dec C) (chunkW I O rL K Q N))

/-- `O`'s head `N` cells back. -/
def rewW : WM ns nr := .whr N (.seq (.dec N) (.bwd O))

/-- **The converter**: to the frame's end, `t` chunks, `t` more chunks, the final `0`, rewind. -/
def seedW : WM ns nr :=
  .seq (toEndW I) (.seq (Hash4.wcopyR rT C Q) (.seq (chunksW I O rL C K Q N) (.seq (Hash4.wcopyR rT C Q)
    (.seq (chunksW I O rL C K Q N) (.seq (emit1 O false) (.seq (.inc N) (rewW O N)))))))

theorem chunkSt_setv (l : List Bool) (L T : ℕ) (σ : WState ns nr) (m : ℕ) (r : Fin nr) (hr : r ≠ N) (x : ℕ) :
    (chunkSt I O N l L T σ m).setv r x = chunkSt I O N l L T (σ.setv r x) m := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; by_cases h1 : q = N
  · subst h1; simp [chunkSt, Function.update_apply, Ne.symm hr]
  · simp [chunkSt, Function.update_apply, h1]

theorem chunks_spec (hIO : I ≠ O) (hLK : rL ≠ K) (hLQ : rL ≠ Q) (hKQ : K ≠ Q) (hKN : K ≠ N) (hQN : Q ≠ N)
    (hLN : rL ≠ N) (hCN : C ≠ N) (hCK : C ≠ K) (hCQ : C ≠ Q) (hCL : C ≠ rL) (l : List Bool) (L T : ℕ)
    (hl : l.length = T * L) (hLc : L ≤ cap) : ∀ (c : ℕ) (σ : WState ns nr) (m : ℕ),
    σ.st I = frame l → σ.val K = 0 → σ.val Q = 0 → σ.val rL = L → σ.sh O = (σ.st O).length →
    σ.val C = c → c ≤ cap → m + c ≤ T → σ.val N + T * (2 * L + 2) ≤ cap →
    WExec cap (chunksW I O rL C K Q N) (chunkSt I O N l L T σ m) (chunkSt I O N l L T (σ.setv C 0) (m + c))
      (c * (chunkCost L + 4) + 1)
  | 0, σ, m, _, _, _, _, _, hC, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by simp [chunkSt, Function.update_apply, hCN, hC])) ?_ (by omega)
    rw [Nat.add_zero, ← chunkSt_setv I O N l L T σ m C hCN, ← hC]
    exact (wsetv_same _ C).symm.trans (by simp [chunkSt, Function.update_apply, hCN])
  | c + 1, σ, m, hs, hK, hQ, hL, hO, hC, hc, hm, hN => by
    have hpl := pre_length l L T hl (m + 1) (by omega)
    have d1 := WExec.dec (cap := cap) C (chunkSt I O N l L T σ m) (by simp [chunkSt, Function.update_apply, hCN]; omega)
    have hv : (chunkSt I O N l L T σ m).val C - 1 = c := by simp [chunkSt, Function.update_apply, hCN, hC]
    rw [hv, chunkSt_setv I O N l L T σ m C hCN] at d1
    have d2 := chunk_spec cap hIO hLK hLQ hKQ hKN hQN hLN l L (σ.setv C c) (by simpa using hs)
      (by simp [Function.update_apply, hCK.symm, hK]) (by simp [Function.update_apply, hCQ.symm, hQ])
      (by simp [Function.update_apply, hCL.symm, hL]) hLc (by simpa using hO) T hl m (by omega)
      (by simp [Function.update_apply, hCN.symm]; rw [hpl]; nlinarith)
    have ih := chunks_spec hIO hLK hLQ hKQ hKN hQN hLN hCN hCK hCQ hCL l L T hl hLc c (σ.setv C c) (m + 1)
      (by simpa using hs) (by simp [Function.update_apply, hCK.symm, hK]) (by simp [Function.update_apply, hCQ.symm, hQ])
      (by simp [Function.update_apply, hCL.symm, hL]) (by simpa using hO) (by simp) (by omega) (by omega)
      (by simp [Function.update_apply, hCN.symm]; exact hN)
    rw [wsetv_setv, show m + 1 + c = m + (c + 1) by omega] at ih
    refine WExec.cast cap (WExec.whrT (by simp [chunkSt, Function.update_apply, hCN, hC]) (WExec.seq d1 d2) ih) rfl
      (by ring_nf; omega)

theorem rew_spec : ∀ (k : ℕ) (σ : WState ns nr), σ.val N = k → k ≤ cap → k ≤ σ.sh O →
    WExec cap (rewW O N) σ ((σ.seth O (σ.sh O - k)).setv N 0) (5 * k + 1)
  | 0, σ, hv, _, _ => by
    refine WExec.cast cap (WExec.whrF hv) ?_ le_rfl
    rw [Nat.sub_zero, seth_same, ← hv, wsetv_same]
  | k + 1, σ, hv, hc, hh => by
    have d1 := WExec.dec (cap := cap) N σ (by omega)
    have d2 := WExec.bwd (cap := cap) O (σ.setv N (σ.val N - 1))
    have ih := rew_spec k ((σ.setv N (σ.val N - 1)).seth O ((σ.setv N (σ.val N - 1)).sh O - 1)) (by simp [hv])
      (by omega) (by simp; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 d2) ih) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = O
      · subst hj; simp; omega
      · simp [Function.update_apply, hj]
    · rfl
    · funext r; by_cases hr : r = N
      · subst hr; simp
      · simp [Function.update_apply, hr]
    · rfl

/-- The converter's step count. -/
def seedCost (L t : ℕ) : ℕ :=
  2 * (18 * t + 3 + (t * (92 * L + 37) + 1)) + 5 * (2 * t * L) + 5 * (2 * t * (2 * L + 2) + 1) + 30

/-- **The converter's run**: from the frame of `l` (`|l| = 2t·L`) on `I` and a blank `O`, `O` becomes `revWord l L (2t)`
with its head at `0`; everything else is kept. -/
theorem seed_spec (hIO : I ≠ O) (hLK : rL ≠ K) (hLQ : rL ≠ Q) (hKQ : K ≠ Q) (hKN : K ≠ N) (hQN : Q ≠ N)
    (hLN : rL ≠ N) (hCN : C ≠ N) (hCK : C ≠ K) (hCQ : C ≠ Q) (hCL : C ≠ rL) (hTC : rT ≠ C) (hTQ : rT ≠ Q)
    (hTN : rT ≠ N) (l : List Bool) (L t : ℕ) (hl : l.length = 2 * t * L) (σ : WState ns nr)
    (hs : σ.st I = frame l) (hsh : σ.sh I = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0) (hL : σ.val rL = L)
    (hT : σ.val rT = t) (hC : σ.val C = 0) (hK : σ.val K = 0) (hQ : σ.val Q = 0) (hN : σ.val N = 0)
    (hcap : 2 * t * (2 * L + 2) + 1 + L + t ≤ cap) :
    WExec cap (seedW I O rL rT C K Q N) σ (σ.sets O (revWord l L (2 * t))) (seedCost L t) := by
  have hLc : L ≤ cap := by omega
  have hl' : l.length = (2 * t) * L := hl
  -- 1: to the end
  have d1 := toEnd_spec cap I l l.length σ hs (by omega)
  have e1 : σ.seth I (2 * l.length) = chunkSt I O N l L (2 * t) σ 0 := by
    apply WState.eq
    · funext j; by_cases h1 : j = I
      · subst h1; simp [chunkSt, Function.update_apply, hIO, hl]; ring
      · by_cases h2 : j = O
        · subst h2; simp [chunkSt, Function.update_apply, h1, hO, hOh, pre]
        · simp [chunkSt, Function.update_apply, h1, h2]
    · funext j; by_cases h2 : j = O
      · subst h2; simp [chunkSt, pre]
      · simp [chunkSt, Function.update_apply, h2]
    · funext r; by_cases h1 : r = N
      · subst h1; simp [chunkSt, pre]
      · simp [chunkSt, Function.update_apply, h1]
    · rfl
  rw [e1] at d1
  -- 2, 3
  have d2 := Hash4.wcopyR_spec cap rT C Q hTC hTQ hCQ (chunkSt I O N l L (2 * t) σ 0)
    (by simp [chunkSt, Function.update_apply, hCN, hC]) (by simp [chunkSt, Function.update_apply, hQN, hQ])
    (by simp [chunkSt, Function.update_apply, hTN, hT]; omega)
  rw [show (chunkSt I O N l L (2 * t) σ 0).val rT = t by simp [chunkSt, Function.update_apply, hTN, hT],
    chunkSt_setv I O N l L (2 * t) σ 0 C hCN] at d2
  have hNc : ∀ τ : WState ns nr, τ.val N = 0 → τ.val N + 2 * t * (2 * L + 2) ≤ cap := fun τ h => by rw [h]; omega
  have d3 := chunks_spec cap I O rL C K Q N hIO hLK hLQ hKQ hKN hQN hLN hCN hCK hCQ hCL l L (2 * t) hl' hLc t
    (σ.setv C t) 0 (by simpa using hs) (by simp [Function.update_apply, hCK.symm, hK])
    (by simp [Function.update_apply, hCQ.symm, hQ]) (by simp [Function.update_apply, hCL.symm, hL])
    (by simp [hO, hOh]) (by simp) (by omega) (by omega) (hNc _ (by simp [Function.update_apply, hCN.symm, hN]))
  have hσ : (σ.setv C t).setv C 0 = σ := by
    rw [wsetv_setv]; conv_rhs => rw [← wsetv_same σ C]
    rw [hC]
  rw [hσ, Nat.zero_add] at d3
  -- 4, 5
  have d4 := Hash4.wcopyR_spec cap rT C Q hTC hTQ hCQ (chunkSt I O N l L (2 * t) σ t)
    (by simp [chunkSt, Function.update_apply, hCN, hC]) (by simp [chunkSt, Function.update_apply, hQN, hQ])
    (by simp [chunkSt, Function.update_apply, hTN, hT]; omega)
  rw [show (chunkSt I O N l L (2 * t) σ t).val rT = t by simp [chunkSt, Function.update_apply, hTN, hT],
    chunkSt_setv I O N l L (2 * t) σ t C hCN] at d4
  have d5 := chunks_spec cap I O rL C K Q N hIO hLK hLQ hKQ hKN hQN hLN hCN hCK hCQ hCL l L (2 * t) hl' hLc t
    (σ.setv C t) t (by simpa using hs) (by simp [Function.update_apply, hCK.symm, hK])
    (by simp [Function.update_apply, hCQ.symm, hQ]) (by simp [Function.update_apply, hCL.symm, hL])
    (by simp [hO, hOh]) (by simp) (by omega) (by omega) (hNc _ (by simp [Function.update_apply, hCN.symm, hN]))
  rw [hσ, show t + t = 2 * t by ring] at d5
  -- 6, 7, 8
  rw [chunkSt_eq] at d5
  have hO5 := (g_facts cap hIO hLK hLQ hKQ hKN hQN hLN l L σ hs hK hQ hL hLc (by simp [hO, hOh])
    (pre l L (2 * t) (2 * t)) (2 * (L * (2 * t - 2 * t))) (pre l L (2 * t) (2 * t)).length).2.2.2.2.2.1
  have d6 := emit1_spec cap O false _ hO5
  rw [gSt_app hIO] at d6
  have hpl := pre_length l L (2 * t) hl' (2 * t) le_rfl
  have d7 := WExec.inc (cap := cap) N (gSt I O N σ (pre l L (2 * t) (2 * t) ++ [false]) (2 * (L * (2 * t - 2 * t)))
    (pre l L (2 * t) (2 * t)).length) (by simp [gSt, hN, hpl]; omega)
  rw [gSt_inc hIO] at d7
  have hk : (gSt I O N σ (pre l L (2 * t) (2 * t) ++ [false]) (2 * (L * (2 * t - 2 * t)))
      ((pre l L (2 * t) (2 * t)).length + 1)).val N = (pre l L (2 * t) (2 * t)).length + 1 := by simp [gSt, hN]
  have d8 := rew_spec cap O N _ _ hk (by rw [hpl]; omega) (by simp [gSt, Function.update_apply, Ne.symm hIO, hO])
  have run := WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 (WExec.seq d6 (WExec.seq d7 d8))))))
  refine WExec.cast cap run ?_ (by unfold seedCost chunkCost; nlinarith)
  have hrev : revWord l L (2 * t) = pre l L (2 * t) (2 * t) ++ [false] := by
    unfold revWord pre; rw [flatMap_range_reverse]
  rw [hrev]
  apply WState.eq
  · funext j; by_cases h1 : j = I
    · subst h1; simp [gSt, Function.update_apply, hIO, hsh]
    · by_cases h2 : j = O
      · subst h2; simp [gSt, Function.update_apply, h1, hO, hOh]
      · simp [gSt, Function.update_apply, h1, h2]
  · funext j; by_cases h2 : j = O
    · subst h2; simp [gSt, hO]
    · simp [gSt, Function.update_apply, h2]
  · funext r; by_cases h1 : r = N
    · subst h1; simp [gSt, hN]
    · simp [gSt, Function.update_apply, h1]
  · rfl

/-- **The fixed hash's seed word for stage 4**: from `frame (List.ofFn s)` on `I`, `O` becomes
`Hash4.seedWord ℓ₀ (coefsRev (coefVal MP s))` (the hash coefficients `f(2t−1), …, f(0)`), its head at `0`. -/
theorem seed_hash (hIO : I ≠ O) (hLK : rL ≠ K) (hLQ : rL ≠ Q) (hKQ : K ≠ Q) (hKN : K ≠ N) (hQN : Q ≠ N)
    (hLN : rL ≠ N) (hCN : C ≠ N) (hCK : C ≠ K) (hCQ : C ≠ Q) (hCL : C ≠ rL) (hTC : rT ≠ C) (hTQ : rT ≠ Q)
    (hTN : rT ≠ N) (MP : MajorantParams) (s : Fin (2 * MP.t * MP.ell0) → Bool) (σ : WState ns nr)
    (hs : σ.st I = frame (List.ofFn s)) (hsh : σ.sh I = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0)
    (hL : σ.val rL = MP.ell0) (hT : σ.val rT = MP.t) (hC : σ.val C = 0) (hK : σ.val K = 0) (hQ : σ.val Q = 0)
    (hN : σ.val N = 0) (hcap : 2 * MP.t * (2 * MP.ell0 + 2) + 1 + MP.ell0 + MP.t ≤ cap) :
    WExec cap (seedW I O rL rT C K Q N) σ (σ.sets O (seedWord MP.ell0 (coefsRev (MajorantBits.coefVal MP s))))
      (seedCost MP.ell0 MP.t) := by
  rw [← revWord_eq]
  exact seed_spec cap I O rL rT C K Q N hIO hLK hLQ hKQ hKN hQN hLN hCN hCK hCQ hCL hTC hTQ hTN (List.ofFn s) MP.ell0
    MP.t (by simp) σ hs hsh hO hOh hL hT hC hK hQ hN hcap

end Prog

end NearCubicWires.WireExponent3_5.FinalPass.HashSeed
