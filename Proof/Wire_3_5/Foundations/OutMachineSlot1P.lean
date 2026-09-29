import Proof.Wire_3_5.Foundations.OutMachineReqSkip
import Proof.Wire_3_5.Foundations.OutMachineSlot1M

/-! # SA's slot 1, part 3: the program

On `WState 2 14` (streams: the input `I`, the output `O`, the scratch `Sx`): count `|fpIn|` six times; skip the
request word (the mode bit into `rM`); copy the seed's frames to the scratch, counting them; drop the hash frame's
count at THR; rewind; skip the request word again; copy the counted frames to the output; close with `false`;
rewind everything, every register back at `0`:

* the layout (`I`, `O`, `Sx`, registers `rf … rR`), `Vg` (the registers' values), `slot1P`;
* **`slot1_spec`**: from `frame (r.word ++ seed)` with `seed = flatten (map frame (fs ++ ex))` (`ex` one frame at
  THR, none at SYM), the output holds `flatten (map frame fs) ++ [false]`, the input is kept, the scratch holds at
  most `|fpIn|` bits, every head and register is `0`, within `5000·(|fpIn|+1)^2` steps at the capacity
  `28·(|fpIn|+1)`.

Paper quantity of the main type: S4's sample word (P3:3044-3048, 3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.FinalPass.Out.ReqSkip
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)
open NearCubicWires.RepairRepresentation (natWord natListWord)

/-! ## The layout -/

def I : Fin 3 := 0
def O : Fin 3 := 1
def Sx : Fin 3 := 2
def rf : Fin 14 := 0
def rc : Fin 14 := 1
def rv : Fin 14 := 2
def rp : Fin 14 := 3
def rt : Fin 14 := 4
def rM : Fin 14 := 5
def rN : Fin 14 := 6
def k1 : Fin 14 := 7
def k2 : Fin 14 := 8
def k3 : Fin 14 := 9
def k4 : Fin 14 := 10
def k5 : Fin 14 := 11
def k6 : Fin 14 := 12
def rR : Fin 14 := 13

/-- The registers' values: the mode flag, the frame count, the six copies of `|fpIn|`. -/
def Vg (m nN a b c d e g : ℕ) : Fin 14 → ℕ := ![0, 0, 0, 0, 0, m, nN, a, b, c, d, e, g, 0]

theorem upd_M (m nN a b c d e g x : ℕ) : Function.update (Vg m nN a b c d e g) rM x = Vg x nN a b c d e g := by
  funext q; fin_cases q <;> rfl
theorem upd_N (m nN a b c d e g x : ℕ) : Function.update (Vg m nN a b c d e g) rN x = Vg m x a b c d e g := by
  funext q; fin_cases q <;> rfl
theorem upd_1 (m nN a b c d e g x : ℕ) : Function.update (Vg m nN a b c d e g) k1 x = Vg m nN x b c d e g := by
  funext q; fin_cases q <;> rfl
theorem upd_2 (m nN a b c d e g x : ℕ) : Function.update (Vg m nN a b c d e g) k2 x = Vg m nN a x c d e g := by
  funext q; fin_cases q <;> rfl
theorem upd_3 (m nN a b c d e g x : ℕ) : Function.update (Vg m nN a b c d e g) k3 x = Vg m nN a b x d e g := by
  funext q; fin_cases q <;> rfl
theorem upd_4 (m nN a b c d e g x : ℕ) : Function.update (Vg m nN a b c d e g) k4 x = Vg m nN a b c x e g := by
  funext q; fin_cases q <;> rfl
theorem upd_5 (m nN a b c d e g x : ℕ) : Function.update (Vg m nN a b c d e g) k5 x = Vg m nN a b c d x g := by
  funext q; fin_cases q <;> rfl
theorem upd_6 (m nN a b c d e g x : ℕ) : Function.update (Vg m nN a b c d e g) k6 x = Vg m nN a b c d e x := by
  funext q; fin_cases q <;> rfl

theorem Vg_zero : Vg 0 0 0 0 0 0 0 0 = fun _ => 0 := by funext q; fin_cases q <;> rfl

/-! ## The program -/

def cntsW : WM 2 14 :=
  .seq (P1.cntW I rR k1) (.seq (P1.cntW I rR k2) (.seq (P1.cntW I rR k3) (.seq (P1.cntW I rR k4)
    (.seq (P1.cntW I rR k5) (P1.cntW I rR k6)))))

def reqW1 : WM 2 14 := reqSkipW I rf rc rv rp rt rM

def dropW : WM 2 14 := .ifr rM (.seq (.dec rN) (.dec rM)) .skip

def clrW : WM 2 14 := .ifr rM (.dec rM) .skip

/-- **SA's slot-1 program.** -/
def slot1P : WM 2 14 :=
  .seq cntsW (.seq reqW1 (.seq (countLoop I Sx rN) (.seq dropW (.seq (WM.rewind I k1) (.seq (WM.rewind I k2)
    (.seq reqW1 (.seq (copyLoopN I O rN) (.seq (emitW O false) (.seq clrW (.seq (WM.rewind I k3)
      (.seq (WM.rewind I k4) (.seq (WM.rewind Sx k5) (WM.rewind O k6)))))))))))))

/-! ## The run -/

theorem frame_marks (w : List Bool) : frame w = marks w ++ [false] := by
  rw [frame_eq_frameP]; rfl

theorem frames_len_le : ∀ ys : List (List Bool), ys.length ≤ ((ys.map frame).flatten).length
  | [] => le_refl _
  | y :: ys => by
    have := frames_len_le ys
    have := frame_length y
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem natWord_pos (n : ℕ) : 1 ≤ (natWord n).length := by
  rw [PrimAsm.ParseNat.natWord_length]; omega

theorem word_pos (r : PrimRequest) : 1 ≤ r.word.length := by
  rw [word_split3 r]; simp only [List.length_append]; have := natWord_pos r.n; omega

theorem natListCost_le (xs : List ℕ) (L : ℕ) (h1 : xs.length ≤ L) (h2 : (xs.flatMap natWord).length ≤ L) :
    natListCost xs ≤ 500 * (L + 1) ^ 2 := by
  unfold natListCost
  have hb := CarPipe.nbl_le xs.length
  have hp := PrimAsm.CopyNat.two_pow_natBitLength_le xs.length
  have a1 : natBitLength xs.length + 2 ≤ L + 3 := by omega
  have a2 : 40 * 2 ^ natBitLength xs.length + 40 ≤ 80 * L + 120 := by omega
  have := Nat.mul_le_mul a1 a2
  nlinarith

theorem flat_le (xs : List ℕ) : xs.length ≤ (xs.flatMap natWord).length := by
  rw [List.length_flatMap]
  calc xs.length = (xs.map fun _ => 1).sum := by simp
    _ ≤ (xs.map fun x => (natWord x).length).sum := by
      apply List.sum_le_sum; intro x _; rw [PrimAsm.ParseNat.natWord_length]; omega

theorem reqCost_le (r : PrimRequest) (L : ℕ) (h : r.word.length ≤ L) : reqCost r ≤ 1600 * (L + 1) ^ 2 := by
  have hw := word_split3 r
  have hlen := congrArg List.length hw
  simp only [List.length_append, natListWord, List.length_singleton, List.length_cons, List.length_nil] at hlen
  have hn := PrimAsm.ParseNat.natWord_length r.n
  have f1 := flat_le (PrimAsm.Codec.codeList r)
  have f2 := flat_le (PrimAsm.Codec.carrierCodes r)
  have f3 := flat_le r.translation
  have c1 := natListCost_le (PrimAsm.Codec.codeList r) L (by omega) (by omega)
  have c2 := natListCost_le (PrimAsm.Codec.carrierCodes r) L (by omega) (by omega)
  have c3 := natListCost_le r.translation L (by omega) (by omega)
  have hsq : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold reqCost
  omega

/-- **Slot 1's run**: the seed's frames but the THR hash frame, closed by `false`. -/
theorem slot1_spec (cap : ℕ) (r : PrimRequest) (fs ex : List (List Bool))
    (hex : ex.length = if PrimAsm.Codec.modeBit r.mode then 1 else 0) (σ : WState 2 14)
    (hI : σ.st I = frame (r.word ++ ((fs ++ ex).map frame).flatten)) (hO : σ.st O = []) (hS : σ.st Sx = [])
    (hsh : ∀ i, σ.sh i = 0) (hv : ∀ q, σ.val q = 0)
    (hcap : 28 * ((r.word ++ ((fs ++ ex).map frame).flatten).length + 1) ≤ cap) :
    ∃ (τ : WState 2 14) (n : ℕ), WExec cap slot1P σ τ n ∧
      n ≤ 5000 * ((r.word ++ ((fs ++ ex).map frame).flatten).length + 1) ^ 2 ∧
      τ.st O = (fs.map frame).flatten ++ [false] ∧ τ.st I = σ.st I ∧
      (τ.st Sx).length ≤ (r.word ++ ((fs ++ ex).map frame).flatten).length ∧ (∀ i, τ.sh i = 0) ∧
      (∀ q, τ.val q = 0) := by
  set seed := ((fs ++ ex).map frame).flatten with hseed
  set w := r.word ++ seed with hw
  set L := w.length with hL
  have hLs : L = r.word.length + seed.length := by rw [hL, hw, List.length_append]
  have hmk : frame w = marks r.word ++ (marks seed ++ [false]) := by
    rw [frame_marks, hw, marks_append, List.append_assoc]
  have hys : (fs ++ ex).length ≤ seed.length := frames_len_le _
  have hfsl : ((fs.map frame).flatten).length ≤ seed.length := by
    rw [hseed, List.map_append, List.flatten_append, List.length_append]; omega
  have hr1 := word_pos r
  have hv0 : σ.val = Vg 0 0 0 0 0 0 0 0 := by rw [Vg_zero]; funext q; exact hv q
  obtain ⟨mb, hmb⟩ : ∃ m, m = (if PrimAsm.Codec.modeBit r.mode then 1 else 0) := ⟨_, rfl⟩
  rw [← hmb] at hex
  -- 1. `|fpIn|` six times
  have c1 := CarKit.cntF_spec cap I rR k1 (by decide) w σ hI (hsh I) (by rw [hv0]; rfl) (by rw [hv0]; rfl) (by omega)
  have c2 := CarKit.cntF_spec cap I rR k2 (by decide) w (σ.setv k1 L) hI (hsh I)
    (by rw [WState.setv_val, hv0, upd_1]; rfl) (by rw [WState.setv_val, hv0, upd_1]; rfl) (by omega)
  have c3 := CarKit.cntF_spec cap I rR k3 (by decide) w ((σ.setv k1 L).setv k2 L) hI (hsh I)
    (by rw [WState.setv_val, WState.setv_val, hv0, upd_1, upd_2]; rfl)
    (by rw [WState.setv_val, WState.setv_val, hv0, upd_1, upd_2]; rfl) (by omega)
  have c4 := CarKit.cntF_spec cap I rR k4 (by decide) w (((σ.setv k1 L).setv k2 L).setv k3 L) hI (hsh I)
    (by simp only [WState.setv_val]; rw [hv0, upd_1, upd_2, upd_3]; rfl)
    (by simp only [WState.setv_val]; rw [hv0, upd_1, upd_2, upd_3]; rfl) (by omega)
  have c5 := CarKit.cntF_spec cap I rR k5 (by decide) w ((((σ.setv k1 L).setv k2 L).setv k3 L).setv k4 L) hI
    (hsh I) (by simp only [WState.setv_val]; rw [hv0, upd_1, upd_2, upd_3, upd_4]; rfl)
    (by simp only [WState.setv_val]; rw [hv0, upd_1, upd_2, upd_3, upd_4]; rfl) (by omega)
  have c6 := CarKit.cntF_spec cap I rR k6 (by decide) w
    (((((σ.setv k1 L).setv k2 L).setv k3 L).setv k4 L).setv k5 L) hI (hsh I)
    (by simp only [WState.setv_val]; rw [hv0, upd_1, upd_2, upd_3, upd_4, upd_5]; rfl)
    (by simp only [WState.setv_val]; rw [hv0, upd_1, upd_2, upd_3, upd_4, upd_5]; rfl) (by omega)
  set σ1 := ((((((σ.setv k1 L).setv k2 L).setv k3 L).setv k4 L).setv k5 L).setv k6 L) with hσ1
  have v1 : σ1.val = Vg 0 0 L L L L L L := by
    rw [hσ1]; simp only [WState.setv_val]; rw [hv0, upd_1, upd_2, upd_3, upd_4, upd_5, upd_6]
  have s1 : WExec cap cntsW σ σ1 _ := WExec.seq c1 (WExec.seq c2 (WExec.seq c3 (WExec.seq c4 (WExec.seq c5 c6))))
  -- 2. the request word skipped
  have r2 := reqSkip_spec cap I rf rc rv rp rt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) rM (by decide) (by decide) (by decide) (by decide)
    (by decide) r (marks seed ++ [false]) σ1 (by rw [hσ1]; simp only [WState.setv_st]; rw [hI, hmk])
    (by rw [hσ1]; simp only [WState.setv_sh]; exact hsh I) (by rw [v1]; rfl) (by rw [v1]; rfl) (by rw [v1]; rfl)
    (by rw [v1]; rfl) (by rw [v1]; rfl) (by rw [v1]; rfl) (reqCaps_of cap r (by omega))
  rw [← hmb] at r2
  set σ2 := (σ1.seth I (2 * r.word.length)).setv rM mb with hσ2
  have v2 : σ2.val = Vg mb 0 L L L L L L := by rw [hσ2, WState.setv_val, WState.seth_val, v1, upd_M]
  -- 3. the seed's frames to the scratch, counted
  obtain ⟨σ3, s3, e3S, e3Sh, e3I, e3Ih, o3, v3, -⟩ := countLoop_spec cap I Sx (by decide) rN [] (fs ++ ex)
    (marks r.word) σ2 (by rw [hσ2, WState.setv_st, WState.seth_st, hσ1]; simp only [WState.setv_st]; rw [hI, hmk])
    (by rw [hσ2, WState.setv_sh, WState.seth_sh, Function.update_self, marks_length])
    (by rw [hσ2, WState.setv_sh, WState.setv_st, WState.seth_sh, WState.seth_st, Function.update_of_ne
      (by decide : Sx ≠ I), hσ1]; simp only [WState.setv_sh, WState.setv_st]; rw [hsh, hS]; rfl)
    (by rw [v2]; show 0 + (fs ++ ex).length ≤ cap; omega)
  have v3' : σ3.val = Vg mb (fs ++ ex).length L L L L L L := by
    have h0 : Vg mb 0 L L L L L L rN = 0 := rfl
    rw [v3, v2, h0, Nat.zero_add, upd_N]
  -- 4. the hash frame's count dropped
  obtain ⟨σ4, s4, e4st, e4sh, v4⟩ : ∃ σ4, WExec cap dropW σ3 σ4 5 ∧ σ4.st = σ3.st ∧ σ4.sh = σ3.sh ∧
      σ4.val = Vg 0 fs.length L L L L L L := by
    by_cases hm : PrimAsm.Codec.modeBit r.mode = true
    · have hmb' : mb = 1 := by rw [hmb, if_pos hm]
      have hex1 : ex.length = 1 := by rw [hex, hmb']
      have hne : σ3.val rM ≠ 0 := by rw [v3', hmb']; exact one_ne_zero
      have d1 := WExec.dec (cap := cap) rN σ3 (by rw [v3']; show (fs ++ ex).length ≤ cap; omega)
      have d2 := WExec.dec (cap := cap) rM (σ3.setv rN (σ3.val rN - 1))
        (by rw [WState.setv_val, v3', upd_N, hmb']; show 1 ≤ cap; omega)
      refine ⟨_, WExec.mono (WExec.ifrT hne (WExec.seq d1 d2)) (by omega), rfl, rfl, ?_⟩
      simp only [WState.setv_val]
      rw [v3', upd_N]
      show Function.update (Vg mb ((fs ++ ex).length - 1) L L L L L L) rM (mb - 1) = _
      rw [upd_M, hmb', List.length_append, hex1]; rfl
    · have hmb' : mb = 0 := by rw [hmb, if_neg hm]
      have hex0 : ex.length = 0 := by rw [hex, hmb']
      have hz : σ3.val rM = 0 := by rw [v3', hmb']; rfl
      refine ⟨σ3, WExec.mono (WExec.ifrF hz (WExec.skip σ3)) (by omega), rfl, rfl, ?_⟩
      rw [v3', hmb', List.length_append, hex0, Nat.add_zero]
  -- 5. the input rewound
  have w5 := wrewind_spec cap I k1 L σ4 (by rw [v4]; rfl) (by rw [v4]; show L ≤ cap; omega)
  set σ5 := (σ4.setv k1 0).seth I (σ4.sh I - L) with hσ5
  have w6 := wrewind_spec cap I k2 L σ5 (by rw [hσ5, WState.seth_val, WState.setv_val, v4, upd_1]; rfl)
    (by rw [hσ5, WState.seth_val, WState.setv_val, v4, upd_1]; show L ≤ cap; omega)
  set σ6 := (σ5.setv k2 0).seth I (σ5.sh I - L) with hσ6
  have hm1 := marks_length r.word
  have hm2 := marks_length ((fs ++ ex).map frame).flatten
  have hsl : seed.length = (((fs ++ ex).map frame).flatten).length := by rw [hseed]
  have h6I : σ6.sh I = 0 := by
    simp only [hσ6, hσ5, WState.seth_sh, WState.setv_sh, Function.update_self]
    rw [e4sh, e3Ih]
    omega
  have h6st : σ6.st = σ3.st := by
    simp only [hσ6, hσ5, WState.seth_st, WState.setv_st]; rw [e4st]
  have h6sh : ∀ j, j ≠ I → σ6.sh j = σ3.sh j := by
    intro j hj
    simp only [hσ6, hσ5, WState.seth_sh, WState.setv_sh, Function.update_of_ne hj]; rw [e4sh]
  have v6 : σ6.val = Vg 0 fs.length 0 0 L L L L := by
    simp only [hσ6, hσ5, WState.seth_val, WState.setv_val]; rw [v4, upd_1, upd_2]
  -- 6. the request word skipped again
  have h7pre : σ6.st I = marks r.word ++ (marks seed ++ [false]) := by
    rw [h6st, e3I]; simp only [hσ2, hσ1, WState.setv_st, WState.seth_st]; rw [hI, hmk]
  have r7 := reqSkip_spec cap I rf rc rv rp rt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) rM (by decide) (by decide) (by decide) (by decide)
    (by decide) r (marks seed ++ [false]) σ6 h7pre h6I
    (by rw [v6]; rfl) (by rw [v6]; rfl) (by rw [v6]; rfl) (by rw [v6]; rfl) (by rw [v6]; rfl) (by rw [v6]; rfl)
    (reqCaps_of cap r (by omega))
  rw [← hmb] at r7
  set σ7 := (σ6.seth I (2 * r.word.length)).setv rM mb with hσ7
  have v7 : σ7.val = Vg mb fs.length 0 0 L L L L := by
    simp only [hσ7, WState.setv_val, WState.seth_val]; rw [v6, upd_M]
  have h7I : σ7.st I = marks r.word ++ (marks seed ++ [false]) := by
    simp only [hσ7, WState.setv_st, WState.seth_st]; exact h7pre
  have h7O : σ7.st O = [] ∧ σ7.sh O = 0 := by
    have hO3 := o3 O (by decide) (by decide)
    refine ⟨?_, ?_⟩
    · simp only [hσ7, WState.setv_st, WState.seth_st]; rw [h6st, hO3.1]
      simp only [hσ2, hσ1, WState.setv_st, WState.seth_st]; exact hO
    · simp only [hσ7, WState.setv_sh, WState.seth_sh, Function.update_of_ne (by decide : O ≠ I)]
      rw [h6sh O (by decide), hO3.2]
      simp only [hσ2, hσ1, WState.setv_sh, WState.seth_sh, Function.update_of_ne (by decide : O ≠ I)]; exact hsh O
  -- 7. the counted frames to the output
  obtain ⟨σ8, s8, e8O, e8Oh, e8I, e8Ih, o8, v8, -⟩ := copyLoopN_spec cap I O (by decide) rN [false] fs.length
    (fs ++ ex) (marks r.word) σ7 (by simp) (by rw [h7I, hseed])
    (by simp only [hσ7, WState.setv_sh, WState.seth_sh, Function.update_self]; rw [marks_length])
    (by rw [h7O.1, h7O.2]; rfl) (by rw [v7]; rfl) (by have h := hys; simp only [List.length_append] at h; omega)
  have htake : (fs ++ ex).take fs.length = fs := List.take_left' rfl
  rw [htake] at e8O e8Ih s8
  -- 8. the closing `false`
  obtain ⟨σ9, s9, e9O, e9Oh, o9, v9, -⟩ := emit_facts cap O false σ8 e8Oh
  -- 9. the mode flag cleared
  obtain ⟨σ10, s10, e10st, e10sh, v10⟩ : ∃ σ10, WExec cap clrW σ9 σ10 3 ∧ σ10.st = σ9.st ∧ σ10.sh = σ9.sh ∧
      σ10.val = Vg 0 0 0 0 L L L L := by
    have hv9 : σ9.val = Vg mb 0 0 0 L L L L := by rw [v9, v8, v7, upd_N]
    by_cases hm : PrimAsm.Codec.modeBit r.mode = true
    · have hmb' : mb = 1 := by rw [hmb, if_pos hm]
      have hne : σ9.val rM ≠ 0 := by rw [hv9, hmb']; exact one_ne_zero
      have d1 := WExec.dec (cap := cap) rM σ9 (by rw [hv9, hmb']; show 1 ≤ cap; omega)
      refine ⟨_, WExec.mono (WExec.ifrT hne d1) (by omega), rfl, rfl, ?_⟩
      rw [WState.setv_val, hv9, upd_M, hmb']
      rfl
    · have hmb' : mb = 0 := by rw [hmb, if_neg hm]
      have hz : σ9.val rM = 0 := by rw [hv9, hmb']; rfl
      exact ⟨σ9, WExec.mono (WExec.ifrF hz (WExec.skip σ9)) (by omega), rfl, rfl, by rw [hv9, hmb']⟩
  -- 10. everything rewound
  have w11 := wrewind_spec cap I k3 L σ10 (by rw [v10]; rfl) (by rw [v10]; show L ≤ cap; omega)
  set σ11 := (σ10.setv k3 0).seth I (σ10.sh I - L) with hσ11
  have w12 := wrewind_spec cap I k4 L σ11 (by rw [hσ11, WState.seth_val, WState.setv_val, v10, upd_3]; rfl)
    (by rw [hσ11, WState.seth_val, WState.setv_val, v10, upd_3]; show L ≤ cap; omega)
  set σ12 := (σ11.setv k4 0).seth I (σ11.sh I - L) with hσ12
  have w13 := wrewind_spec cap Sx k5 L σ12
    (by rw [hσ12, WState.seth_val, WState.setv_val, hσ11, WState.seth_val, WState.setv_val, v10, upd_3, upd_4]; rfl)
    (by rw [hσ12, WState.seth_val, WState.setv_val, hσ11, WState.seth_val, WState.setv_val, v10, upd_3, upd_4]
        show L ≤ cap; omega)
  set σ13 := (σ12.setv k5 0).seth Sx (σ12.sh Sx - L) with hσ13
  have w14 := wrewind_spec cap O k6 L σ13
    (by rw [hσ13, WState.seth_val, WState.setv_val, hσ12, WState.seth_val, WState.setv_val, hσ11, WState.seth_val,
      WState.setv_val, v10, upd_3, upd_4, upd_5]; rfl)
    (by rw [hσ13, WState.seth_val, WState.setv_val, hσ12, WState.seth_val, WState.setv_val, hσ11, WState.seth_val,
      WState.setv_val, v10, upd_3, upd_4, upd_5]; show L ≤ cap; omega)
  set τ := (σ13.setv k6 0).seth O (σ13.sh O - L) with hτ
  -- the facts along the way
  have hS8 : σ8.st Sx = seed ∧ σ8.sh Sx = seed.length := by
    have h := o8 Sx (by decide) (by decide)
    have hS7 : σ7.st Sx = σ3.st Sx ∧ σ7.sh Sx = σ3.sh Sx := by
      refine ⟨by simp only [hσ7, WState.setv_st, WState.seth_st]; rw [h6st], ?_⟩
      simp only [hσ7, WState.setv_sh, WState.seth_sh, Function.update_of_ne (by decide : Sx ≠ I)]
      exact h6sh Sx (by decide)
    have hS2 : σ2.st Sx = [] := by
      simp only [hσ2, hσ1, WState.setv_st, WState.seth_st]; exact hS
    refine ⟨by rw [h.1, hS7.1, e3S, hS2]; rfl, by rw [h.2, hS7.2, e3Sh, e3S, hS2]; rfl⟩
  have hI8 : σ8.st I = σ.st I := by
    rw [e8I, h7I, hI, hmk]
  refine ⟨τ, _, WExec.seq s1 (WExec.seq r2 (WExec.seq s3 (WExec.seq s4 (WExec.seq w5 (WExec.seq w6 (WExec.seq r7
    (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 (WExec.seq w11 (WExec.seq w12 (WExec.seq w13 w14)))))))))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the cost
    have hq := reqCost_le r L (by omega)
    have := hfsl
    simp only [List.length_append] at hys
    nlinarith
  · -- the output
    rw [hτ, WState.seth_st, WState.setv_st, hσ13, WState.seth_st, WState.setv_st, hσ12, WState.seth_st,
      WState.setv_st, hσ11, WState.seth_st, WState.setv_st, e10st, e9O, e8O, h7O.1]
    simp
  · -- the input kept
    rw [hτ, WState.seth_st, WState.setv_st, hσ13, WState.seth_st, WState.setv_st, hσ12, WState.seth_st,
      WState.setv_st, hσ11, WState.seth_st, WState.setv_st, e10st, (o9 I (by decide)).1, hI8]
  · -- the scratch
    rw [hτ, WState.seth_st, WState.setv_st, hσ13, WState.seth_st, WState.setv_st, hσ12, WState.seth_st,
      WState.setv_st, hσ11, WState.seth_st, WState.setv_st, e10st, (o9 Sx (by decide)).1, hS8.1]
    omega
  · -- the heads
    have h10I : σ10.sh I ≤ 2 * L := by
      rw [e10sh, (o9 I (by decide)).2, e8Ih]; simp only [marks_length]
      have := hfsl; omega
    have hIh : τ.sh I = 0 := by
      simp only [hτ, hσ13, hσ12, hσ11, WState.seth_sh, WState.setv_sh, Function.update_self,
        Function.update_of_ne (show I ≠ O by decide), Function.update_of_ne (show I ≠ Sx by decide)]
      omega
    have hOh : τ.sh O = 0 := by
      simp only [hτ, hσ13, hσ12, hσ11, WState.seth_sh, WState.setv_sh, Function.update_self,
        Function.update_of_ne (show O ≠ Sx by decide), Function.update_of_ne (show O ≠ I by decide)]
      rw [e10sh, e9Oh, e9O, e8O, h7O.1]
      simp only [List.nil_append, List.length_append, List.length_singleton]
      have := hfsl; omega
    have hSh : τ.sh Sx = 0 := by
      simp only [hτ, hσ13, hσ12, hσ11, WState.seth_sh, WState.setv_sh, Function.update_self,
        Function.update_of_ne (show Sx ≠ O by decide), Function.update_of_ne (show Sx ≠ I by decide)]
      rw [e10sh, (o9 Sx (by decide)).2, hS8.2]
      omega
    intro i
    fin_cases i
    · exact hIh
    · exact hOh
    · exact hSh
  · -- the registers
    intro q
    have e : τ.val = Vg 0 0 0 0 0 0 0 0 := by
      rw [hτ, WState.seth_val, WState.setv_val, hσ13, WState.seth_val, WState.setv_val, hσ12, WState.seth_val,
        WState.setv_val, hσ11, WState.seth_val, WState.setv_val, v10, upd_3, upd_4, upd_5, upd_6]
    rw [e, Vg_zero]

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1
