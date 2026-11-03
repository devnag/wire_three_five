import Proof.Wire_3_5.Primitive.Writers.C3WAsm
import Proof.Wire_3_5.Primitive.SeedFix.C4Arm
import Proof.Wire_3_5.Primitive.Writers.CapNum
import Proof.Wire_3_5.Primitive.Writers.FiltNum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Phase
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.PrimT.CarWM NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.C3Marks NearCubicWires.WireExponent3_5.PrimAsm.C3Asm
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)

/-! ## The layout -/

/-- The streams' count minus one. -/
abbrev CN : ℕ := 22
/-- The registers' count. -/
abbrev CR : ℕ := 40

def cIN : Fin (CN + 1) := 0
def cNT : Fin (CN + 1) := 1
def cCT : Fin (CN + 1) := 2
def cAUX : Fin (CN + 1) := 3
def sH : Fin (CN + 1) := 4
def sQ : Fin (CN + 1) := 5
def sM : Fin (CN + 1) := 6
def sP : Fin (CN + 1) := 7
def sPRE : Fin (CN + 1) := 8
def sPOST : Fin (CN + 1) := 9
def sGF1 : Fin (CN + 1) := 10
def sGF2 : Fin (CN + 1) := 11
def sSF : Fin (CN + 1) := 12
def sWF : Fin (CN + 1) := 13
def sFF1 : Fin (CN + 1) := 14
def sFF2 : Fin (CN + 1) := 15
def sCF1 : Fin (CN + 1) := 16
def sCF2 : Fin (CN + 1) := 17
def sAIN : Fin (CN + 1) := 18
def sAOUT : Fin (CN + 1) := 19
def sAT : Fin (CN + 1) := 20
def sSH : Fin (CN + 1) := 21
def sNW : Fin (CN + 1) := 22

def rh : Fin CR := 0
def rQ : Fin CR := 1
def rm : Fin CR := 2
def rpr : Fin CR := 3
def rw : Fin CR := 4
def rg : Fin CR := 5
def rdr : Fin CR := 6
def rK : Fin CR := 7
def rT : Fin CR := 8
def rX : Fin CR := 9
def rD : Fin CR := 10
def rf : Fin CR := 11
def rc : Fin CR := 12
def rp : Fin CR := 13
def rt : Fin CR := 14
def rP1 : Fin CR := 15

/-- `writeNatM`'s registers for `d = rdr`, and for `p = rP1` (sharing `21 … 27`). -/
def RW1 : Fin 8 ↪ Fin CR := ⟨![6, 21, 22, 23, 24, 25, 26, 27], by decide⟩
def RW2 : Fin 8 ↪ Fin CR := ⟨![15, 21, 22, 23, 24, 25, 26, 27], by decide⟩

/-! ## The first program: the numbers, the atoms' ruler, the C3a′ input -/

/-- The unary inputs and the width into registers. -/
def wU : WM CN CR :=
  .seq (C4Arm.ucount sH rh) (.seq (C4Arm.ucount sQ rQ) (.seq (C4Arm.ucount sM rm) (.seq (C4Arm.ucount sP rpr)
    (C4Arm.ucount sWF rw))))

/-- `rD := 4·rX + 2`. -/
def wD4 : WM CN CR :=
  .seq (ParseNat.addTo rX rD rT) (.seq (ParseNat.addTo rX rD rT) (.seq (ParseNat.addTo rX rD rT)
    (.seq (ParseNat.addTo rX rD rT) (StarNums.incN rD 2))))

/-- The first program's numbers: the unary inputs, the gate count, the atoms' ruler. -/
def wPreA : WM CN CR := .seq wU (.seq (ParseNat.readNatM true sGF2 rf rc rg rp rt) (atomsW sFF2 sAT rg rK rT))

/-- The first program's columns' count. -/
def wPreB : WM CN CR := .seq (ParseNat.readNatM true sCF2 rf rc rX rp rt) (.seq wD4 (colsW sCF2 rD rK rT rdr))

/-- The first program's numbers and rulers. -/
def wPre : WM CN CR := .seq wPreA wPreB

/-- **The first program.** -/
def wm1 : WM CN CR := .seq wPre (asmW cNT sGF1 sSF sFF1 sAIN rw rh rQ rK rT)

/-! ## Facts of the single passes -/

section Facts
variable {ns nr : ℕ} (cap : ℕ)

theorem ucount_facts (s : Fin (ns + 1)) (r : Fin nr) (x : ℕ) (σ : WState ns nr) (hs : σ.st s = List.replicate x true)
    (hsh : σ.sh s = 0) (hr : σ.val r = 0) (hx : x ≤ cap) :
    ∃ τ, WExec cap (C4Arm.ucount s r) σ τ (x * 7 + 1) ∧ τ.st = σ.st ∧ τ.sh s = x ∧ (∀ j, j ≠ s → τ.sh j = σ.sh j) ∧
      τ.val r = x ∧ (∀ q, q ≠ r → τ.val q = σ.val q) ∧ τ.cell = σ.cell :=
  ⟨_, C4Arm.ucount_spec cap s r x [] rfl x 0 σ (by omega) (by rw [hs]; simp) hsh hr hx, by simp, by simp,
    fun j hj => by simp [Function.update_of_ne hj], by simp, fun q hq => by simp [Function.update_of_ne hq], rfl⟩

theorem readNat_facts (i : Fin (ns + 1)) (f c v p t : Fin nr) (hfc : f ≠ c) (hfv : f ≠ v) (hfp : f ≠ p)
    (hft : f ≠ t) (hcv : c ≠ v) (hcp : c ≠ p) (hct : c ≠ t) (hpv : p ≠ v) (hpt : p ≠ t) (hvt : v ≠ t) (x : ℕ)
    (rest : List Bool) (σ : WState ns nr) (hst : σ.st i = marks (RepairRepresentation.natWord x) ++ rest)
    (hsh : σ.sh i = 0) (hf : σ.val f = 0) (hc : σ.val c = 0) (hp : σ.val p = 0) (ht : σ.val t = 0) (hv : σ.val v = 0)
    (hcap : 2 ^ (natBitLength x + 1) ≤ cap) :
    ∃ τ, WExec cap (ParseNat.readNatM true i f c v p t) σ τ ((natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)) ∧
      τ.st = σ.st ∧ τ.sh i = (marks (RepairRepresentation.natWord x)).length ∧ (∀ j, j ≠ i → τ.sh j = σ.sh j) ∧
      τ.val v = x ∧ (∀ q, q ≠ v → τ.val q = σ.val q) ∧ τ.cell = σ.cell := by
  have h := ParseNat.readNatM_spec cap true i f c v p t hfc hfv hfp hft hcv hcp hct hpv hpt hvt x [] rest σ
    (by rw [hst]; rfl) (by rw [hsh]; rfl) hf hc hp ht (by rw [hv]; omega)
  refine ⟨_, h, by simp, ?_, fun j hj => by simp [Function.update_of_ne hj], by simp [hv], fun q hq => by
    simp [Function.update_of_ne hq], rfl⟩
  simp [ParseNat.stp]

end Facts

theorem val_upd {ns nr : ℕ} {σ τ : WState ns nr} (r : Fin nr) (x : ℕ) (h1 : τ.val r = x)
    (h2 : ∀ q, q ≠ r → τ.val q = σ.val q) : τ.val = Function.update σ.val r x := by
  funext q
  by_cases hq : q = r
  · subst hq; simp [h1]
  · rw [h2 q hq]; simp [hq]

variable (cap : ℕ)

/-- **The first program's numbers**: the unary inputs counted, the gate count `g` from the gate field's header, `g`
ones per flip pattern on `sAT`. -/
theorem wPreA_spec (σ : WState CN CR) (h Q m pr wd g : ℕ) (gt : List Bool) (flips : List (List Bool))
    (hne : ∀ f ∈ flips, f ≠ []) (hv0 : ∀ q, σ.val q = 0) (hh0 : ∀ s, σ.sh s = 0)
    (hH : σ.st sH = List.replicate h true) (hQ : σ.st sQ = List.replicate Q true)
    (hM : σ.st sM = List.replicate m true) (hP : σ.st sP = List.replicate pr true)
    (hW : σ.st sWF = List.replicate wd true)
    (hG : σ.st sGF2 = marks (RepairRepresentation.natWord g) ++ gt)
    (hF : σ.st sFF2 = flips.flatMap frame ++ [false]) (hA : σ.st sAT = [])
    (hbig : h + Q + m + pr + wd + g + 1 ≤ cap) (hpg : 2 ^ (natBitLength g + 1) ≤ cap) :
    ∃ τ, WExec cap wPreA σ τ ((h + Q + m + pr + wd) * 7 + (natBitLength g + 2) * (40 * 2 ^ natBitLength g + 40) +
        (5 * (flips.flatMap frame).length + flips.length * (UnaryPow.sq cap + 9 * g + 30)) + 20) ∧
      τ.st sAT = List.replicate (flips.length * g) true ∧ τ.sh sAT = (τ.st sAT).length ∧
      (∀ j, j ≠ sAT → τ.st j = σ.st j) ∧
      (∀ j, j ≠ sH → j ≠ sQ → j ≠ sM → j ≠ sP → j ≠ sWF → j ≠ sGF2 → j ≠ sFF2 → j ≠ sAT → τ.sh j = σ.sh j) ∧
      τ.val = Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update σ.val rh h) rQ Q) rm m) rpr pr) rw wd) rg g ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, t1, h1, o1, v1, w1, c1⟩ := ucount_facts cap sH rh h σ hH (hh0 _) (hv0 _) (by omega)
  obtain ⟨σ2, s2, t2, h2, o2, v2, w2, c2⟩ := ucount_facts cap sQ rQ Q σ1 (by rw [t1, hQ]) (by rw [o1 _ (by decide), hh0])
    (by rw [w1 _ (by decide), hv0]) (by omega)
  obtain ⟨σ3, s3, t3, h3, o3, v3, w3, c3⟩ := ucount_facts cap sM rm m σ2 (by rw [t2, t1, hM])
    (by rw [o2 _ (by decide), o1 _ (by decide), hh0]) (by rw [w2 _ (by decide), w1 _ (by decide), hv0]) (by omega)
  obtain ⟨σ4, s4, t4, h4, o4, v4, w4, c4⟩ := ucount_facts cap sP rpr pr σ3 (by rw [t3, t2, t1, hP])
    (by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), hh0])
    (by rw [w3 _ (by decide), w2 _ (by decide), w1 _ (by decide), hv0]) (by omega)
  obtain ⟨σ5, s5, t5, h5, o5, v5, w5, c5⟩ := ucount_facts cap sWF rw wd σ4 (by rw [t4, t3, t2, t1, hW])
    (by rw [o4 _ (by decide), o3 _ (by decide), o2 _ (by decide), o1 _ (by decide), hh0])
    (by rw [w4 _ (by decide), w3 _ (by decide), w2 _ (by decide), w1 _ (by decide), hv0]) (by omega)
  have V5 : σ5.val = Function.update (Function.update (Function.update (Function.update (Function.update σ.val rh h)
      rQ Q) rm m) rpr pr) rw wd := by
    rw [val_upd rw wd v5 w5, val_upd rpr pr v4 w4, val_upd rm m v3 w3, val_upd rQ Q v2 w2, val_upd rh h v1 w1]
  have T5 : σ5.st = σ.st := by rw [t5, t4, t3, t2, t1]
  have H5 : ∀ j, j ≠ sH → j ≠ sQ → j ≠ sM → j ≠ sP → j ≠ sWF → σ5.sh j = σ.sh j := by
    intro j a1 a2 a3 a4 a5; rw [o5 j a5, o4 j a4, o3 j a3, o2 j a2, o1 j a1]
  have Z5 : ∀ q, q ≠ rh → q ≠ rQ → q ≠ rm → q ≠ rpr → q ≠ rw → σ5.val q = 0 := by
    intro q a1 a2 a3 a4 a5; rw [V5]; simp [Function.update_apply, a1, a2, a3, a4, a5, hv0]
  obtain ⟨σ6, s6, t6, h6, o6, v6, w6, c6⟩ := readNat_facts cap sGF2 rf rc rg rp rt (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) g gt σ5 (by rw [T5, hG])
    (by rw [H5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hh0])
    (Z5 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (Z5 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (Z5 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (Z5 _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (Z5 _ (by decide) (by decide) (by decide) (by decide) (by decide)) hpg
  have V6 : σ6.val = Function.update σ5.val rg g := val_upd rg g v6 w6
  have Z6 : ∀ q, q ≠ rh → q ≠ rQ → q ≠ rm → q ≠ rpr → q ≠ rw → q ≠ rg → σ6.val q = 0 := by
    intro q a1 a2 a3 a4 a5 a6; rw [V6]; simp only [Function.update_apply, a6, if_false]; exact Z5 q a1 a2 a3 a4 a5
  have FF6 : σ6.sh sFF2 = 0 := by rw [o6 _ (by decide), H5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hh0]
  have AT6 : σ6.sh sAT = 0 := by rw [o6 _ (by decide), H5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hh0]
  obtain ⟨τ, s7, e7, e7h, n7, n7h, o7, v7, c7⟩ := atomsW_spec cap sFF2 sAT rg rK rT (by decide) (by decide)
    (by decide) (by decide) g (by omega) [] flips [] σ6 hne (by rw [t6, T5, hF]; simp) (by rw [FF6]; rfl)
    (by rw [AT6, t6, T5, hA]; rfl) (by rw [V6]; simp)
    (Z6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (Z6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨τ, WExec.mono (WExec.seq (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))))
    (WExec.seq s6 s7)) (by nlinarith), ?_, e7h, ?_, ?_, ?_, ?_⟩
  · rw [e7, t6, T5, hA]; simp
  · intro j hj
    by_cases hjF : j = sFF2
    · subst hjF; rw [n7, t6, T5]
    · rw [(o7 j hjF hj).1, t6, T5]
  · intro j a1 a2 a3 a4 a5 a6 a7 a8
    rw [(o7 j a7 a8).2, o6 j a6, H5 j a1 a2 a3 a4 a5]
  · rw [v7, V6, V5]
  · rw [c7, c6, c5, c4, c3, c2, c1]

/-- The columns' blocks of `marks (columnsWord w cols)`. -/
def colBlocks (w : ℕ) (cols : List ℕ) : List (List Bool) := cols.map fun x => marks (frame (SignedSortKey.binary w x))

theorem marks_cols (w : ℕ) (cols : List ℕ) :
    marks (cols.flatMap fun x => frame (SignedSortKey.binary w x)) = (colBlocks w cols).flatten := by
  induction cols with
  | nil => rfl
  | cons x cols ih => simp only [List.flatMap_cons, marks_append, ih, colBlocks, List.map_cons, List.flatten_cons]

theorem colBlocks_ok (w : ℕ) (cols : List ℕ) :
    ∀ b ∈ colBlocks w cols, b.length = 4 * w + 2 ∧ b.headD false = true := by
  intro b hb
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
  refine ⟨by simp [frame_length, SignedSortKey.binary_length]; ring, ?_⟩
  cases w with
  | zero => simp [SignedSortKey.binary, frame, marks]
  | succ w => simp [SignedSortKey.binary, frame, marks]

/-- **The first program's columns' count**: the columns field's width header into `rX`, `rD = 4·rX + 2`, the columns'
count into `rdr`. -/
theorem wPreB_spec (σ : WState CN CR) (wd' : ℕ) (cols : List ℕ)
    (hC : σ.st sCF2 = marks (RepairRepresentation.natWord wd') ++
      (marks (cols.flatMap fun x => frame (SignedSortKey.binary wd' x)) ++ [false]))
    (hCh : σ.sh sCF2 = 0) (hf : σ.val rf = 0) (hc : σ.val rc = 0) (hp : σ.val rp = 0) (ht : σ.val rt = 0)
    (hX : σ.val rX = 0) (hD : σ.val rD = 0) (hK : σ.val rK = 0) (hT : σ.val rT = 0) (hd : σ.val rdr = 0)
    (hbig : 4 * wd' + 2 + cols.length + 1 ≤ cap) (hpw : 2 ^ (natBitLength wd' + 1) ≤ cap) :
    ∃ τ, WExec cap wPreB σ τ ((natBitLength wd' + 2) * (40 * 2 ^ natBitLength wd' + 40) + 5 * UnaryPow.sq cap +
        cols.length * (UnaryPow.sq cap + 6 * (4 * wd' + 2) + 10) + 10) ∧
      τ.st = σ.st ∧ (∀ j, j ≠ sCF2 → τ.sh j = σ.sh j) ∧
      τ.val = Function.update (Function.update (Function.update σ.val rX wd') rD (4 * wd' + 2)) rdr cols.length ∧
      τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨σ8, s8, t8, h8, o8, v8, w8, c8⟩ := readNat_facts cap sCF2 rf rc rX rp rt (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) wd' _ σ
    hC hCh hf hc hp ht hX hpw
  have V8 : σ8.val = Function.update σ.val rX wd' := val_upd rX wd' v8 w8
  have nXD : rX ≠ rD := by decide
  have nTD : rT ≠ rD := by decide
  have nXT : rX ≠ rT := by decide
  have hTz : σ8.val rT = 0 := by rw [V8]; simp only [Function.update_apply, (Ne.symm nXT), if_false]; exact hT
  have hDz : σ8.val rD = 0 := by rw [V8]; simp only [Function.update_apply, (Ne.symm nXD), if_false]; exact hD
  have hXv : σ8.val rX = wd' := by rw [V8]; simp
  have d1 := CapNum.add1 cap rX rD rT nXD nXT (Ne.symm nTD) wd' 0 σ8 hXv hDz hTz (by omega) (by omega)
  have d2 := CapNum.add1 cap rX rD rT nXD nXT (Ne.symm nTD) wd' (0 + wd') (σ8.setv rD (0 + wd'))
    (by simp [Function.update_apply, nXD, hXv]) (by simp) (by simp [Function.update_apply, nTD, hTz])
    (by omega) (by omega)
  have d3 := CapNum.add1 cap rX rD rT nXD nXT (Ne.symm nTD) wd' (0 + wd' + wd')
    ((σ8.setv rD (0 + wd')).setv rD (0 + wd' + wd')) (by simp [Function.update_apply, nXD, hXv]) (by simp)
    (by simp [Function.update_apply, nTD, hTz]) (by omega) (by omega)
  have d4 := CapNum.add1 cap rX rD rT nXD nXT (Ne.symm nTD) wd' (0 + wd' + wd' + wd')
    (((σ8.setv rD (0 + wd')).setv rD (0 + wd' + wd')).setv rD (0 + wd' + wd' + wd'))
    (by simp [Function.update_apply, nXD, hXv]) (by simp) (by simp [Function.update_apply, nTD, hTz])
    (by omega) (by omega)
  have d5 := FiltNum.incN1 cap rD (0 + wd' + wd' + wd' + wd') 2
    ((((σ8.setv rD (0 + wd')).setv rD (0 + wd' + wd')).setv rD (0 + wd' + wd' + wd')).setv rD
      (0 + wd' + wd' + wd' + wd')) (by simp) (by omega)
  set σ9 := (((((σ8.setv rD (0 + wd')).setv rD (0 + wd' + wd')).setv rD (0 + wd' + wd' + wd')).setv rD
      (0 + wd' + wd' + wd' + wd')).setv rD (0 + wd' + wd' + wd' + wd' + 2)) with hσ9
  have V9 : σ9.val = Function.update σ8.val rD (4 * wd' + 2) := by
    rw [hσ9]; funext q; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> omega
  have T9 : σ9.st = σ8.st := by rw [hσ9]; rfl
  have H9 : σ9.sh = σ8.sh := by rw [hσ9]; rfl
  have C9 : σ9.cell = σ8.cell := by rw [hσ9]; rfl
  have s9 : WExec cap wD4 σ8 σ9 (5 * UnaryPow.sq cap + 4) :=
    WExec.mono (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 d5)))) (by omega)
  have hlen : (colBlocks wd' cols).length = cols.length := by simp [colBlocks]
  have nKD : rK ≠ rD := by decide
  have nXK : rX ≠ rK := by decide
  have nXd : rX ≠ rdr := by decide
  have nDd : rD ≠ rdr := by decide
  obtain ⟨τ, s10, t10, h10, o10, v10, w10, c10⟩ := colsW_spec cap sCF2 rD rK rT rdr (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (4 * wd' + 2) (by omega) [] (colBlocks wd' cols)
    (marks (RepairRepresentation.natWord wd')) σ9 (colBlocks_ok wd' cols)
    (by rw [T9, t8, hC, marks_cols]) (by rw [H9, h8])
    (by rw [V9]; simp)
    (by rw [V9, V8]; simp only [Function.update_apply, nKD, Ne.symm nXK, if_false]; exact hK)
    (by rw [V9, V8]; simp only [Function.update_apply, nTD, Ne.symm nXT, if_false]; exact hT)
    (by rw [V9, V8]; simp only [Function.update_apply, Ne.symm nDd, Ne.symm nXd, if_false, hd, hlen]; omega)
  refine ⟨τ, WExec.mono (WExec.seq s8 (WExec.seq s9 s10)) (by rw [hlen] at *; omega), ?_, ?_, ?_, ?_⟩
  · rw [t10, T9, t8]
  · intro j hj; rw [o10 j hj, H9, o8 j hj]
  · funext q
    by_cases hq : q = rdr
    · subst hq; rw [v10, V9, V8]; simp only [Function.update_apply, Ne.symm nDd, Ne.symm nXd, if_false, hd, hlen]; simp
    · rw [w10 q hq, V9, V8]; simp [Function.update_apply, hq]
  · rw [c10, C9, c8]

/-- The registers after the first program. -/
def val1 (h Q m pr wd g wd' d : ℕ) : Fin CR → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (fun _ => 0) rh h) rQ Q) rm m) rpr pr) rw wd) rg g) rX wd')
    rD (4 * wd' + 2)) rdr d

theorem val1_rh (h Q m pr wd g wd' d : ℕ) : val1 h Q m pr wd g wd' d rh = h := by simp [val1, Function.update_apply, rh, rQ, rm, rpr, rw, rg, rX, rD, rdr]
theorem val1_rQ (h Q m pr wd g wd' d : ℕ) : val1 h Q m pr wd g wd' d rQ = Q := by simp [val1, Function.update_apply, rh, rQ, rm, rpr, rw, rg, rX, rD, rdr]
theorem val1_rm (h Q m pr wd g wd' d : ℕ) : val1 h Q m pr wd g wd' d rm = m := by simp [val1, Function.update_apply, rh, rQ, rm, rpr, rw, rg, rX, rD, rdr]
theorem val1_rpr (h Q m pr wd g wd' d : ℕ) : val1 h Q m pr wd g wd' d rpr = pr := by simp [val1, Function.update_apply, rh, rQ, rm, rpr, rw, rg, rX, rD, rdr]
theorem val1_rw (h Q m pr wd g wd' d : ℕ) : val1 h Q m pr wd g wd' d rw = wd := by simp [val1, Function.update_apply, rh, rQ, rm, rpr, rw, rg, rX, rD, rdr]
theorem val1_rdr (h Q m pr wd g wd' d : ℕ) : val1 h Q m pr wd g wd' d rdr = d := by simp [val1, Function.update_apply, rh, rQ, rm, rpr, rw, rg, rX, rD, rdr]
theorem val1_zero (h Q m pr wd g wd' d : ℕ) (q : Fin CR) (a1 : q ≠ rh) (a2 : q ≠ rQ) (a3 : q ≠ rm) (a4 : q ≠ rpr)
    (a5 : q ≠ rw) (a6 : q ≠ rg) (a7 : q ≠ rX) (a8 : q ≠ rD) (a9 : q ≠ rdr) : val1 h Q m pr wd g wd' d q = 0 := by
  simp [val1, Function.update_apply, a1, a2, a3, a4, a5, a6, a7, a8, a9]

/-- The first program's cost. -/
def c1Cost (cap n h Q m pr wd g wd' d L F gyl syl : ℕ) : ℕ :=
  (h + Q + m + pr + wd) * 7 + (natBitLength g + 2) * (40 * 2 ^ natBitLength g + 40) +
    (5 * L + F * (UnaryPow.sq cap + 9 * g + 30)) + 20 +
    ((natBitLength wd' + 2) * (40 * 2 ^ natBitLength wd' + 40) + 5 * UnaryPow.sq cap +
      d * (UnaryPow.sq cap + 6 * (4 * wd' + 2) + 10) + 10) +
    (3 * UnaryPow.sq cap + 25 * n + 50 * gyl + 50 * syl + 60 * L + 21 * (wd + h + Q) + 400) + 2

/-- **The first program**: the numbers, the atoms' ruler `1^{|flips|·g}`, and `frame (c3aInput …)` on `sAIN`. -/
theorem wm1_spec (σ : WState CN CR) (n h Q m pr wd g wd' : ℕ) (gy sy : List Bool) (gt : List Bool)
    (flips : List (List Bool)) (cols : List ℕ) (hne : ∀ f ∈ flips, f ≠ []) (hv0 : ∀ q, σ.val q = 0)
    (hh0 : ∀ s, σ.sh s = 0) (hN : σ.st cNT = List.replicate n true)
    (hH : σ.st sH = List.replicate h true) (hQ : σ.st sQ = List.replicate Q true)
    (hM : σ.st sM = List.replicate m true) (hP : σ.st sP = List.replicate pr true)
    (hW : σ.st sWF = List.replicate wd true)
    (hG1 : σ.st sGF1 = frame gy) (hG : σ.st sGF2 = marks (RepairRepresentation.natWord g) ++ gt)
    (hS : σ.st sSF = frame sy)
    (hF1 : σ.st sFF1 = flips.flatMap frame ++ [false]) (hF : σ.st sFF2 = flips.flatMap frame ++ [false])
    (hC : σ.st sCF2 = marks (RepairRepresentation.natWord wd') ++
      (marks (cols.flatMap fun x => frame (SignedSortKey.binary wd' x)) ++ [false]))
    (hA : σ.st sAT = []) (hAI : σ.st sAIN = [])
    (hbig : h + Q + m + pr + wd + g + 4 * wd' + 2 + cols.length + 1 ≤ cap) (hpg : 2 ^ (natBitLength g + 1) ≤ cap)
    (hpw : 2 ^ (natBitLength wd' + 1) ≤ cap) :
    ∃ τ, WExec cap wm1 σ τ (c1Cost cap n h Q m pr wd g wd' cols.length (flips.flatMap frame).length flips.length
        gy.length sy.length) ∧
      τ.st sAIN = frame (CompilerMachine.Top.loadRec (List.replicate n true) (frame gy) (frame sy)
        (List.replicate wd true) (flips.flatMap frame ++ [false]) (List.replicate h true) (List.replicate Q true)
        [] [] [] []) ∧
      τ.sh sAIN = (τ.st sAIN).length ∧
      τ.st sAT = List.replicate (flips.length * g) true ∧ τ.sh sAT = (τ.st sAT).length ∧
      (∀ j, j ≠ sAIN → j ≠ sAT → τ.st j = σ.st j) ∧
      (∀ j, j ≠ sH → j ≠ sQ → j ≠ sM → j ≠ sP → j ≠ sWF → j ≠ sGF2 → j ≠ sFF2 → j ≠ sCF2 → j ≠ sAT →
        j ≠ cNT → j ≠ sGF1 → j ≠ sSF → j ≠ sFF1 → j ≠ sAIN → τ.sh j = σ.sh j) ∧
      τ.val = val1 h Q m pr wd g wd' cols.length ∧ τ.cell = σ.cell := by
  obtain ⟨τA, sA, eA, eAh, tA, hA', vA, cA⟩ := wPreA_spec cap σ h Q m pr wd g gt flips hne hv0 hh0 hH hQ hM hP hW hG hF
    hA (by omega) hpg
  have VA : ∀ q, q ≠ rh → q ≠ rQ → q ≠ rm → q ≠ rpr → q ≠ rw → q ≠ rg → τA.val q = 0 := by
    intro q a1 a2 a3 a4 a5 a6; rw [vA]; simp [Function.update_apply, a1, a2, a3, a4, a5, a6, hv0]
  obtain ⟨τB, sB, tB, hB, vB, cB⟩ := wPreB_spec cap τA wd' cols (by rw [tA _ (by decide), hC])
    (by rw [hA' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hh0])
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (VA _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) (by omega) hpw
  have hsh : ∀ j, j ≠ sH → j ≠ sQ → j ≠ sM → j ≠ sP → j ≠ sWF → j ≠ sGF2 → j ≠ sFF2 → j ≠ sCF2 → j ≠ sAT →
      τB.sh j = 0 := by
    intro j a1 a2 a3 a4 a5 a6 a7 a8 a9; rw [hB j a8, hA' j a1 a2 a3 a4 a5 a6 a7 a9, hh0]
  have hstB : ∀ j, j ≠ sAT → τB.st j = σ.st j := by intro j hj; rw [tB, tA j hj]
  have V0 : σ.val = fun _ => 0 := funext hv0
  have VB : τB.val = val1 h Q m pr wd g wd' cols.length := by
    rw [vB, vA, V0]; rfl
  obtain ⟨τ, sC, eC, eCh, nC, gC, sC', fC, oC, vC, cC⟩ := asmW_spec cap cNT sGF1 sSF sFF1 sAIN rw rh rQ rK rT
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    n wd h Q gy sy flips hne τB (by rw [hstB _ (by decide), hN])
    (hsh _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hstB _ (by decide), hG1])
    (hsh _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hstB _ (by decide), hS])
    (hsh _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hstB _ (by decide), hF1])
    (hsh _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hstB _ (by decide), hAI])
    (hsh _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [VB, val1_rw]) (by rw [VB, val1_rh]) (by rw [VB, val1_rQ])
    (by rw [VB, val1_zero _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)])
    (by rw [VB, val1_zero _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]) (by omega) (by omega) (by omega)
  refine ⟨τ, WExec.mono (WExec.seq (WExec.seq sA sB) sC) (by unfold c1Cost; omega), eC, eCh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(oC sAT (by decide) (by decide) (by decide) (by decide) (by decide)).1, tB, eA]
  · rw [(oC sAT (by decide) (by decide) (by decide) (by decide) (by decide)).2,
      (oC sAT (by decide) (by decide) (by decide) (by decide) (by decide)).1, hB sAT (by decide), eAh, tB]
  · intro j h1 h2
    by_cases j1 : j = cNT
    · subst j1; rw [nC, hstB _ (by decide)]
    · by_cases j2 : j = sGF1
      · subst j2; rw [gC, hstB _ (by decide)]
      · by_cases j3 : j = sSF
        · subst j3; rw [sC', hstB _ (by decide)]
        · by_cases j4 : j = sFF1
          · subst j4; rw [fC, hstB _ (by decide)]
          · rw [(oC j j1 j2 j3 j4 h1).1, hstB j h2]
  · intro j a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
    rw [(oC j a10 a11 a12 a13 a14).2, hB j a8, hA' j a1 a2 a3 a4 a5 a6 a7 a9]
  · rw [vC, VB]
  · rw [cC, cB, cA]

/-! ## The second program, part a: the children's ruler and the header's field -/

/-- **The second program, part a.** -/
def wm2a : WM CN CR :=
  .seq (skipFs sAOUT) (.seq (shW sAT sAOUT sSH) (.seq (FinalPass.Hash4.wcopyR rpr rP1 rT) (.seq (.inc rP1)
    (nw9W sNW RW1 RW2))))

theorem RW1_ne_P1 : ∀ i, RW1 i ≠ rP1 := by decide

theorem RW2_eq : ∀ i : Fin 8, i ≠ 0 → RW2 i = RW1 i := by decide

theorem wm2a_spec (σ : WState CN CR) (ys : List (List Bool)) (atoms : List (List (List Bool))) (d pr : ℕ)
    (hys : ∀ y ∈ ys, y ≠ []) (hat : ∀ E ∈ atoms, ∀ y ∈ E, y ≠ [])
    (hO : σ.st sAOUT = ys.flatMap frame ++ false :: atomsStream atoms) (hOh : σ.sh sAOUT = 0)
    (hT : σ.st sAT = List.replicate atoms.length true) (hTh : σ.sh sAT = 0)
    (hS : σ.st sSH = []) (hSh : σ.sh sSH = 0) (hN : σ.st sNW = []) (hNh : σ.sh sNW = 0)
    (hd : σ.val rdr = d) (hpr : σ.val rpr = pr) (hP1 : σ.val rP1 = 0) (hrT : σ.val rT = 0)
    (hRW : ∀ i : Fin 8, i ≠ 0 → σ.val (RW1 i) = 0) (hcap : d + pr + 1 + 20 * (d + pr + 3) ≤ cap) :
    ∃ τ, WExec cap wm2a σ τ (5 * (ys.flatMap frame).length + 11 * (atomsStream atoms).length +
        2 * UnaryPow.sq cap + (d + pr + 13) * (200 * (d + pr + 1) + 400) + 40) ∧
      τ.st sSH = List.replicate (atoms.map List.length).sum true ∧
      τ.st sNW = frame (RepairRepresentation.natWord d ++ RepairRepresentation.natWord (pr + 1)) ∧
      (∀ j, j ≠ sSH → j ≠ sNW → τ.st j = σ.st j) ∧
      (∀ j, j ≠ sAOUT → j ≠ sAT → j ≠ sSH → j ≠ sNW → τ.sh j = σ.sh j) ∧
      (∀ r, r ≠ rP1 → r ≠ RW1 7 → τ.val r = σ.val r) ∧ τ.val rP1 = pr + 1 ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have s1 := skipFs_spec cap sAOUT (atomsStream atoms) ys [] σ hys (by rw [hO]; simp) (by rw [hOh]; rfl)
  set σ1 := σ.seth sAOUT ([].length + (ys.flatMap frame).length + 1) with hσ1
  have T1 : σ1.st = σ.st := rfl
  have V1 : σ1.val = σ.val := rfl
  have H1 : ∀ j, j ≠ sAOUT → σ1.sh j = σ.sh j := fun j hj => by simp [σ1, Function.update_of_ne hj]
  obtain ⟨σ2, s2, e2, e2h, t2, t2h, n2, n2h, o2, v2, c2⟩ := shW_spec cap sAT sAOUT sSH (by decide) (by decide)
    (by decide) [] atoms [] (ys.flatMap frame ++ [false]) σ1 hat (by rw [T1, hT]; simp)
    (by rw [H1 _ (by decide), hTh]; rfl) (by rw [T1, hO]; simp) (by simp [σ1])
    (by rw [H1 _ (by decide), T1, hS, hSh]; rfl)
  have V2 : σ2.val = σ.val := by rw [v2, V1]
  have h3 := SparseNum.copy1 cap rpr rP1 rT (by decide) (by decide) (by decide) pr σ2 (by rw [V2, hpr])
    (by rw [V2, hP1]) (by rw [V2, hrT]) (by omega)
  have h4 := SparseNum.inc1 cap rP1 pr (σ2.setv rP1 pr) (by simp) (by omega)
  set σ4 := (σ2.setv rP1 pr).setv rP1 (pr + 1) with hσ4
  have hv4 : ∀ q, q ≠ rP1 → σ4.val q = σ.val q := by
    intro q hq; simp only [hσ4, WState.setv_val, Function.update_apply, hq, if_false]; rw [V2]
  have T4 : σ4.st = σ2.st := rfl
  have H4 : σ4.sh = σ2.sh := rfl
  have C4 : σ4.cell = σ2.cell := rfl
  have NW4 : σ4.st sNW = [] := by
    rw [T4, (o2 sNW (by decide) (by decide) (by decide)).1, T1, hN]
  have NWh4 : σ4.sh sNW = 0 := by
    rw [H4, (o2 sNW (by decide) (by decide) (by decide)).2, H1 _ (by decide), hNh]
  obtain ⟨τ, s5, e5, e5h, o5, v5, c5⟩ := nw9W_spec cap sNW RW1 RW2 RW2_eq d (pr + 1) σ4
    (by rw [show RW1 0 = rdr from rfl, hv4 _ (by decide), hd])
    (by rw [show RW2 0 = rP1 from rfl]; simp [hσ4])
    (fun i hi => by rw [hv4 _ (RW1_ne_P1 i), hRW i hi]) (by rw [NW4, NWh4]; rfl) (by omega)
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq h3 (WExec.seq h4 s5)))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : (d + (pr + 1) + 12) * (200 * (d + (pr + 1)) + 400) = (d + pr + 13) * (200 * (d + pr + 1) + 400) := by
      ring
    simp only [List.length_nil, Nat.zero_add] at *
    omega
  · rw [(o5 sSH (by decide)).1, T4, e2, T1, hS]; rfl
  · rw [e5, NW4]; rfl
  · intro j h1 h2
    rw [(o5 j h2).1, T4]
    by_cases jT : j = sAT
    · subst jT; rw [t2, T1]
    · by_cases jO : j = sAOUT
      · subst jO; rw [n2, T1]
      · rw [(o2 j jT jO h1).1, T1]
  · intro j a1 a2 a3 a4
    rw [(o5 j a4).2, H4, (o2 j a2 a1 a3).2, H1 j a1]
  · intro r h1 h2
    rw [v5 r h2, hv4 r h1]
  · rw [v5 _ (by decide)]; simp [hσ4]
  · rw [c5, C4, c2]; rfl

end NearCubicWires.WireExponent3_5.PrimAsm.C3Phase
