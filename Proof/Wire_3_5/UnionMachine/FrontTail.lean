import Proof.Wire_3_5.UnionMachine.FrontInstall
import Proof.Wire_3_5.FinalPass.LiftR

/-! # C6 front, the tail: the table writer, the capacities, the install as ONE word program

The front's last stage before the loop (P3:3669-3691; `Plan.bankA`): the table writer's word program `P` (numerals,
table, thresholds, on its layout `WState 10 56`) runs renamed into a larger layout (`WM.liftW`), then the capacity
writer (`FrontCapW.capW`: the rulers `U capQ`, `U RQ` from `q`), then the install (`FrontInstall.installW`: the loop's
kept tapes, its log and its driver). Layout `WState 25 105`:
* streams `0 … 10` the writer's, `11 … 14` the capacity writer's, `15 … 25` the install's (the loop's table, cell,
  `p`, six accumulators, log, driver);
* registers `0 … 55` the writer's (`0` the table's length, `52` = `p`, `24 … 29` the thresholds, `54` = `q`),
  `56 … 102` the capacity writer's, `103`, `104` the install's counters.

**`tailW_spec`**: from the writer's exit, the install's streams hold the loop's kept tapes at `capQ`, `RQ`.

Paper quantity of the main type: the loop bank's entry (the table, `p`, the thresholds, the capacities). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTail
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCapW NearCubicWires.WireExponent3_5.UnionMachine.FrontInstall

/-! ## The layout -/

/-- The writer's streams and registers inside the tail's layout. -/
def fsT (i : Fin 11) : Fin 26 := Fin.castLE (by norm_num) i
def frT (r : Fin 56) : Fin 105 := Fin.castLE (by norm_num) r

theorem fsT_val (i : Fin 11) : (fsT i).val = i.val := rfl
theorem frT_val (r : Fin 56) : (frT r).val = r.val := rfl
theorem fsT_inj : Function.Injective fsT := fun a b h => Fin.ext (by simpa [fsT_val] using congrArg Fin.val h)
theorem frT_inj : Function.Injective frT := fun a b h => Fin.ext (by simpa [frT_val] using congrArg Fin.val h)

/-- The capacity writer's registers: `q` in the writer's `54`, the rest fresh (`56 … 102`). -/
def gtF (i : Fin 48) : Fin 105 := if i.val = 0 then ⟨54, by norm_num⟩ else ⟨55 + i.val, by omega⟩

theorem gtF_val (i : Fin 48) : (gtF i).val = if i.val = 0 then 54 else 55 + i.val := by
  unfold gtF; split_ifs <;> rfl

theorem gtF_inj : Function.Injective gtF := by
  intro a b h
  have := congrArg Fin.val h
  rw [gtF_val, gtF_val] at this
  apply Fin.ext
  split_ifs at this <;> omega

def Gt : Fin 48 ↪ Fin 105 := ⟨gtF, gtF_inj⟩

theorem Gt_val (i : Fin 48) : (Gt i).val = if i.val = 0 then 54 else 55 + i.val := gtF_val i

/-- The install's streams: the rulers `13`, `14`, the table's source `0`, then `15 … 25`. -/
def stF (j : Fin 14) : Fin 26 :=
  if j.val = 0 then ⟨13, by norm_num⟩ else if j.val = 1 then ⟨14, by norm_num⟩ else if j.val = 2 then ⟨0, by norm_num⟩
  else ⟨12 + j.val, by omega⟩

theorem stF_val (j : Fin 14) : (stF j).val =
    if j.val = 0 then 13 else if j.val = 1 then 14 else if j.val = 2 then 0 else 12 + j.val := by
  unfold stF; split_ifs <;> rfl

theorem stF_inj : Function.Injective stF := by
  intro a b h
  have := congrArg Fin.val h
  rw [stF_val, stF_val] at this
  apply Fin.ext
  split_ifs at this <;> omega

def St : Fin 14 ↪ Fin 26 := ⟨stF, stF_inj⟩

theorem St_val (j : Fin 14) : (St j).val =
    if j.val = 0 then 13 else if j.val = 1 then 14 else if j.val = 2 then 0 else 12 + j.val := stF_val j

/-- The install's registers: the table's length `0`, `p` in `52`, the thresholds `24 … 29`, counters `103`, `104`. -/
def rgF (j : Fin 10) : Fin 105 :=
  if j.val = 0 then ⟨0, by norm_num⟩ else if j.val = 1 then ⟨52, by norm_num⟩
  else if j.val ≤ 7 then ⟨22 + j.val, by omega⟩ else ⟨95 + j.val, by omega⟩

theorem rgF_val (j : Fin 10) : (rgF j).val =
    if j.val = 0 then 0 else if j.val = 1 then 52 else if j.val ≤ 7 then 22 + j.val else 95 + j.val := by
  unfold rgF; split_ifs <;> rfl

theorem rgF_inj : Function.Injective rgF := by
  intro a b h
  have := congrArg Fin.val h
  rw [rgF_val, rgF_val] at this
  apply Fin.ext
  split_ifs at this <;> omega

def Rgt : Fin 10 ↪ Fin 105 := ⟨rgF, rgF_inj⟩

theorem Rgt_val (j : Fin 10) : (Rgt j).val =
    if j.val = 0 then 0 else if j.val = 1 then 52 else if j.val ≤ 7 then 22 + j.val else 95 + j.val := rgF_val j

/-! ## The tail -/

/-- The loop's capacities from `q` (`FrontCaps.capQ`, `RQ` at `K = 32coef+1`, `A = Amain`, `cr` the row constant). -/
def mOf (cr q : ℕ) : ℕ := q - Cost.starWidth (Ledger.rowBr cr q) q / 4
def capOf (cr K A q : ℕ) : ℕ := (q + 1) ^ A * K * 2 ^ mOf cr q
def rOf (cr K A q : ℕ) : ℕ := (q + 6) * 1000 * capOf cr K A q

/-- **The tail**: the writer's program renamed, the capacity writer, the install. -/
def tailW (P : WM 10 56) (cr K A : ℕ) : WM 25 105 :=
  .seq (P.liftW fsT frT) (.seq (capW cr K A Gt 11 12 13 14) (installW St Rgt))

/-- The tail's cost beyond the writer's. -/
def tailCost (cr K A q L cap : ℕ) : ℕ :=
  1 + (capWCost A (mOf cr q) ((q + 1) ^ A * K) ((q + 6) * 1000) (UnaryPow.sq cap) + 1 +
    installCost (capOf cr K A q) (rOf cr K A q) L (UnaryPow.sq cap))

theorem gt_ne_frT (i : Fin 48) (r : Fin 56) (hr : r.val ≠ 54) : Gt i ≠ frT r := fun h => by
  have e := congrArg Fin.val h
  rw [Gt_val, frT_val] at e
  have hr' := r.isLt
  split_ifs at e <;> omega

theorem rgt_acc (i : Fin 6) : Rgt ⟨i.val + 2, by omega⟩ = frT ⟨24 + i.val, by omega⟩ := by
  fin_cases i <;> decide

/-- **The tail's run**: from the writer's exit (`q` in `54`, the table word on stream `0` with its head at its end and
its length in `0`, `p` in `52`, the thresholds in `24 … 29`), the install's streams `St 3 … St 13` hold the table, the
cell, `p` and the thresholds as registers of capacity `capQ`, the log `0^{RQ+1}` and the driver `1^{RQ}`. -/
theorem tailW_spec (P : WM 10 56) (capT : ℕ) (σT τT : WState 10 56) (nT : ℕ) (hP : WExec capT P σT τT nT)
    (cap : ℕ) (hcap : capT ≤ cap) (ω : WState 25 105) (hω : LiftW fsT frT ω σT)
    (hfs : ∀ j : Fin 26, 11 ≤ j.val → ω.st j = [] ∧ ω.sh j = 0)
    (hfr : ∀ r : Fin 105, 56 ≤ r.val → ω.val r = 0)
    (cr K A q p : ℕ) (a : Fin 6 → ℕ) (s : List Bool)
    (hq : τT.val 54 = q) (hs : τT.st 0 = s) (hsh : τT.sh 0 = s.length) (hL : τT.val 0 = s.length)
    (hp : τT.val 52 = p) (ha : ∀ i : Fin 6, τT.val ⟨24 + i.val, by omega⟩ = a i)
    (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q) (hK : 1 ≤ K)
    (hcapW : K * (q + 1) ^ A + 1000 * (q + 7) + 2 * cr + 100 ≤ cap)
    (hpc : p ≤ capOf cr K A q) (hac : ∀ i, a i ≤ capOf cr K A q) (hpW : p ≤ cap) (haW : ∀ i, a i ≤ cap)
    (hsc : s.length ≤ cap) :
    ∃ τ, WExec cap (tailW P cr K A) ω τ (nT + tailCost cr K A q s.length cap) ∧
      ∀ j : Fin 14, 3 ≤ j.val →
        τ.st (St j) = wtI (capOf cr K A q) (rOf cr K A q) p a s j.val ∧ τ.sh (St j) = hdI p a j.val := by
  obtain ⟨ω1, e1, hl1, ho1⟩ := WExec.liftW capT cap hcap fsT fsT_inj frT frT_inj hP ω hω
  -- the fresh streams and registers survive the writer
  have fs1 : ∀ j : Fin 26, 11 ≤ j.val → ω1.st j = [] ∧ ω1.sh j = 0 := fun j hj => by
    have hout : ∀ i, fsT i ≠ j := fun i h => by
      have e := congrArg Fin.val h; rw [fsT_val] at e; have hi := i.isLt; omega
    rw [(ho1.1 j hout).2, (ho1.1 j hout).1]; exact hfs j hj
  have fr1 : ∀ r : Fin 105, 56 ≤ r.val → ω1.val r = 0 := fun r hr => by
    have hout : ∀ r' , frT r' ≠ r := fun r' h => by
      have e := congrArg Fin.val h; rw [frT_val] at e; have hr' := r'.isLt; omega
    rw [ho1.2 r hout]; exact hfr r hr
  have hG0 : Gt 0 = frT 54 := Fin.ext (by rw [Gt_val, frT_val]; rfl)
  have s11 := fs1 ⟨11, by norm_num⟩ (by norm_num)
  have s12 := fs1 ⟨12, by norm_num⟩ (by norm_num)
  have s13 := fs1 ⟨13, by norm_num⟩ (by norm_num)
  have s14 := fs1 ⟨14, by norm_num⟩ (by norm_num)
  obtain ⟨ω2, e2, hC, hCh, hD, hDh, hso, hro, -⟩ := capW_spec cap cr K A Gt 11 12 13 14 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) ω1 q (by rw [hG0, hl1.val]; exact hq)
    (fun i hi => fr1 _ (by
      have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
      rw [Gt_val, if_neg hi0]; omega)) s11 s12 s13 s14 hcr h4 hK hcapW
  -- what the install reads
  have kS : ∀ j : Fin 26, 15 ≤ j.val ∨ j.val ≤ 10 → ω2.st j = ω1.st j ∧ ω2.sh j = ω1.sh j := fun j hj =>
    hso j (fun h => by subst h; simp at hj) (fun h => by subst h; simp at hj) (fun h => by subst h; simp at hj)
      (fun h => by subst h; simp at hj)
  have kR : ∀ r : Fin 56, r.val ≠ 54 → ω2.val (frT r) = τT.val r := fun r hr =>
    (hro _ (fun i => gt_ne_frT i r hr)).trans (hl1.val r)
  have hS0 : St 0 = 13 := Fin.ext (by rw [St_val]; rfl)
  have hS1 : St 1 = 14 := Fin.ext (by rw [St_val]; rfl)
  have hS2 : St 2 = fsT 0 := Fin.ext (by rw [St_val, fsT_val]; rfl)
  have hR0 : Rgt 0 = frT 0 := Fin.ext (by rw [Rgt_val, frT_val]; rfl)
  have hR1 : Rgt 1 = frT 52 := Fin.ext (by rw [Rgt_val, frT_val]; rfl)
  have hacc : ∀ i : Fin 6, ω2.val (Rgt ⟨i.val + 2, by omega⟩) = a i := fun i => by
    rw [rgt_acc i, kR _ (by simp only; omega)]; exact ha i
  have hR8 : ω2.val (Rgt 8) = 0 := by
    rw [hro _ (fun i h => by have := congrArg Fin.val h; rw [Gt_val, Rgt_val] at this; split_ifs at this <;> simp at *
      <;> omega)]
    exact fr1 _ (by rw [Rgt_val]; simp)
  have hR9 : ω2.val (Rgt 9) = 0 := by
    rw [hro _ (fun i h => by have := congrArg Fin.val h; rw [Gt_val, Rgt_val] at this; split_ifs at this <;> simp at *
      <;> omega)]
    exact fr1 _ (by rw [Rgt_val]; simp)
  obtain ⟨τ, e3, hA, -, -, -, -, -⟩ := installW_spec cap St Rgt ω2 (capOf cr K A q) (rOf cr K A q) p a s
    (by rw [hS0]; exact hC) (by rw [hS0]; exact hCh) (by rw [hS1]; exact hD) (by rw [hS1]; exact hDh)
    (by rw [hS2, (kS _ (by rw [fsT_val]; simp)).1, hl1.st]; exact hs)
    (by rw [hS2, (kS _ (by rw [fsT_val]; simp)).2, hl1.sh]; exact hsh)
    (fun j hj => by
      have hv : (St j).val = 12 + j.val := by rw [St_val]; split_ifs <;> omega
      rw [(kS _ (by omega)).1, (kS _ (by omega)).2]; exact fs1 _ (by omega))
    (by rw [hR0, kR _ (by decide)]; exact hL) (by rw [hR1, kR _ (by decide)]; exact hp)
    (hacc 0) (hacc 1) (hacc 2) (hacc 3) (hacc 4) (hacc 5) hR8 hR9 hpc hac hpW haW hsc
  refine ⟨τ, WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) rfl ?_, hA⟩
  unfold tailCost capOf rOf mOf
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTail
