import Proof.SourceAssembly.SourceInitPost

/-! # The one-time init's placement on the source layout (`dimsOf` + `SourceRestLayout`)

**Consumer.** `SourceInitRun.init_run` (next module): `Once.once_run` needs its pipeline dock `ds` (the arity on the
queried cache's tape 13, every other port a fresh tape), a blank `b0`, the clear driver/log `scr 11/12` and an erase
`mask` covering every source tape at or above `F` that is not kept; `InitPost.post_run` needs ONE injective dock
`s2 : Fin 323 → Fin T` onto the residents. **Paper**: none names a tape; the layout is fixed before the input
(`paper.tex:4280-4290`) — every map depends on the layout `d`, the per-call block size `restPc eX pX gW`, the two
exponents `eR eV` (hence `Dimension.P eR eV`) and the two read-only source tapes `ar` (arity) and `wd`
(`Wd 218`, the phase width), which the site code fixes per `(sources, p, k, r, mode, ph)`. **Budget**: none.

Placement (all new tapes in the reserved region after the five prologue residents `rsT 0..4` (`B+19+Pc ..`) and the
eight FactorSelection residents `gT 0..7` (`B+24+Pc ..`, written by `SourceInitHeader`); `JB := B+32+Pc`):

| tapes | role |
|---|---|
| `JB + x` (`x ≠ 0`, `x < P`) | `Dimension` pipeline port `x` (`pRl` at `65+2eR` stays as `Rc`'s exact log; `pV = P-2`, `pVl = P-1`) |
| `JB + P` | `Once`'s blank `b0` |
| `JB + P + 1 + (j-32)` | the post-`Once` machine's workspace `j = 32 .. 322` |

`s2` sends the post-`Once` machine's special tapes to: `0 ↦ ar`, `1 ↦ wd`, `2,3 ↦ JB+P-2, JB+P-1`,
`4,5 ↦ scr 11, 12`, `6..11 ↦ 278..283`, `12..16 ↦ B+14..B+18` (`cs 2`, `drv 0 1 2 4`), `17..21 ↦ rsT 0..4`,
`22..31 ↦ encT 3..12` (`enc 3, 4, 6, 7, 8, 9, 10`, `app 2, 4, 5`).
The only new layout facts are `InitExt.hjunk : 32 + Pc + X ≤ res` and `InitExt.hX : P + 292 ≤ X` (`X` = the init's
workspace size, the header stage's included).
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
namespace NearCubicWires.SourceConstruction.InitRun
noncomputable section

/-- The init's workspace base: after the five prologue residents `rsT 0..4` (`B+19+Pc ..`) and the eight
FactorSelection residents `gT 0..7` (`B+24+Pc ..`, `SourceInitHeader`). -/
def JB (d : Dims) (eX pX gW : Nat) : Nat := d.B + 32 + restPc eX pX gW

/-- The room the init needs in the reserved region: `X` workspace tapes from `JB`, at least the pipeline, its blank
and the post-`Once` machine's 291 (the rest is the header stage's). -/
structure InitExt (d : Dims) (eX pX gW eR eV X : Nat) : Prop where
  rest : d.RestExt eX pX gW
  hjunk : 32 + restPc eX pX gW + X ≤ d.res
  hX : Dimension.P eR eV + 292 ≤ X

/-- The layout facts every value argument below uses. -/
theorem lay {d : Dims} {eX pX gW eR eV X : Nat} (e : InitExt d eX pX gW eR eV X) :
    285 < d.F ∧ d.B = d.F + d.rt + 13 + d.R1 + 410 + d.w + d.tc ∧ d.scrV 11 + 2 = d.B ∧
    d.scrV 12 + 1 = d.B ∧ d.U = d.B + d.res ∧ JB d eX pX gW = d.B + 32 + restPc eX pX gW ∧
    32 + restPc eX pX gW + Dimension.P eR eV + 292 ≤ d.res ∧ 66 ≤ Dimension.P eR eV := by
  have h1 := e.rest.ext.hF
  have h2 := e.hjunk
  have h2' := e.hX
  have h3 := Dimension.P_ge eR eV
  refine ⟨h1, rfl, ?_, ?_, ?_, rfl, by omega, h3⟩
  · simp only [Dims.scrV, Dims.B]; omega
  · simp only [Dims.scrV, Dims.B]; omega
  · simp only [Dims.U, Dims.B, Dims.prepT]; omega

/-! ## 1. The dock of the post-`Once` machine -/

/-- Its values: `a`, `w` are the arity and width tapes (below `F`). -/
def s2V (d : Dims) (eX pX gW P a w : Nat) (j : Nat) : Nat :=
  if j = 0 then a
  else if j = 1 then w
  else if j = 2 then JB d eX pX gW + P - 2
  else if j = 3 then JB d eX pX gW + P - 1
  else if j = 4 then d.scrV 11
  else if j = 5 then d.scrV 12
  else if j < 12 then 272 + j
  else if j < 17 then d.B + 2 + j
  else if j < 22 then d.B + 19 + restPc eX pX gW + (j - 17)
  else if j < 32 then d.F + d.rt + j - 19
  else JB d eX pX gW + P + 1 + (j - 32)

section vals
variable (d : Dims) (eX pX gW P a w : Nat)
theorem s2V_2 : s2V d eX pX gW P a w 2 = JB d eX pX gW + P - 2 := by simp [s2V]
theorem s2V_3 : s2V d eX pX gW P a w 3 = JB d eX pX gW + P - 1 := by simp [s2V]
theorem s2V_4 : s2V d eX pX gW P a w 4 = d.scrV 11 := by simp [s2V]
theorem s2V_5 : s2V d eX pX gW P a w 5 = d.scrV 12 := by simp [s2V]
theorem s2V_rew (j : Nat) (h1 : 6 ≤ j) (h2 : j < 12) : s2V d eX pX gW P a w j = 272 + j := by
  unfold s2V
  rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega), if_neg (show j ≠ 2 by omega),
    if_neg (show j ≠ 3 by omega), if_neg (show j ≠ 4 by omega), if_neg (show j ≠ 5 by omega), if_pos h2]
theorem s2V_cs (j : Nat) (h1 : 12 ≤ j) (h2 : j < 17) : s2V d eX pX gW P a w j = d.B + 2 + j := by
  unfold s2V
  rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega), if_neg (show j ≠ 2 by omega),
    if_neg (show j ≠ 3 by omega), if_neg (show j ≠ 4 by omega), if_neg (show j ≠ 5 by omega),
    if_neg (show ¬ j < 12 by omega), if_pos h2]
theorem s2V_rs (j : Nat) (h1 : 17 ≤ j) (h2 : j < 22) :
    s2V d eX pX gW P a w j = d.B + 19 + restPc eX pX gW + (j - 17) := by
  unfold s2V
  rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega), if_neg (show j ≠ 2 by omega),
    if_neg (show j ≠ 3 by omega), if_neg (show j ≠ 4 by omega), if_neg (show j ≠ 5 by omega),
    if_neg (show ¬ j < 12 by omega), if_neg (show ¬ j < 17 by omega), if_pos h2]
theorem s2V_enc (j : Nat) (h1 : 22 ≤ j) (h2 : j < 32) : s2V d eX pX gW P a w j = d.F + d.rt + j - 19 := by
  unfold s2V
  rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega), if_neg (show j ≠ 2 by omega),
    if_neg (show j ≠ 3 by omega), if_neg (show j ≠ 4 by omega), if_neg (show j ≠ 5 by omega),
    if_neg (show ¬ j < 12 by omega), if_neg (show ¬ j < 17 by omega), if_neg (show ¬ j < 22 by omega),
    if_pos h2]
theorem s2V_junk (j : Nat) (h1 : 32 ≤ j) : s2V d eX pX gW P a w j = JB d eX pX gW + P + 1 + (j - 32) := by
  unfold s2V
  rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega), if_neg (show j ≠ 2 by omega),
    if_neg (show j ≠ 3 by omega), if_neg (show j ≠ 4 by omega), if_neg (show j ≠ 5 by omega),
    if_neg (show ¬ j < 12 by omega), if_neg (show ¬ j < 17 by omega), if_neg (show ¬ j < 22 by omega),
    if_neg (show ¬ j < 32 by omega)]
end vals

/-- The value set of the dock. -/
def InS2 (d : Dims) (eX pX gW P a w v : Nat) : Prop :=
  v = a ∨ v = w ∨ v = JB d eX pX gW + P - 2 ∨ v = JB d eX pX gW + P - 1 ∨ v = d.scrV 11 ∨ v = d.scrV 12 ∨
  (278 ≤ v ∧ v < 284) ∨ (d.B + 14 ≤ v ∧ v < d.B + 19) ∨
  (d.B + 19 + restPc eX pX gW ≤ v ∧ v < d.B + 24 + restPc eX pX gW) ∨
  (d.F + d.rt + 3 ≤ v ∧ v < d.F + d.rt + 13) ∨ (JB d eX pX gW + P + 1 ≤ v ∧ v < JB d eX pX gW + P + 292)

theorem s2V_in (d : Dims) (eX pX gW P a w j : Nat) (hj : j < 323) :
    InS2 d eX pX gW P a w (s2V d eX pX gW P a w j) := by
  unfold InS2
  by_cases h0 : j = 0
  · subst h0; exact Or.inl (by simp [s2V])
  by_cases h1 : j = 1
  · subst h1; exact Or.inr (Or.inl (by simp [s2V]))
  by_cases h2 : j = 2
  · subst h2; exact Or.inr (Or.inr (Or.inl (s2V_2 d eX pX gW P a w)))
  by_cases h3 : j = 3
  · subst h3; exact Or.inr (Or.inr (Or.inr (Or.inl (s2V_3 d eX pX gW P a w))))
  by_cases h4 : j = 4
  · subst h4; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (s2V_4 d eX pX gW P a w)))))
  by_cases h5 : j = 5
  · subst h5; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (s2V_5 d eX pX gW P a w))))))
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
  by_cases h12 : j < 12
  · rw [s2V_rew d eX pX gW P a w j (by omega) h12]; exact Or.inl ⟨by omega, by omega⟩
  by_cases h17 : j < 17
  · rw [s2V_cs d eX pX gW P a w j (by omega) h17]; exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  by_cases h22 : j < 22
  · rw [s2V_rs d eX pX gW P a w j (by omega) h22]; exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  by_cases h32 : j < 32
  · rw [s2V_enc d eX pX gW P a w j (by omega) h32]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  · rw [s2V_junk d eX pX gW P a w j (by omega)]
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))

/-- The placement: the layout, the universe, and the two read-only source tapes below `F`. -/
structure Place (d : Dims) (eX pX gW eR eV X T : Nat) where
  ext : InitExt d eX pX gW eR eV X
  hT : d.U ≤ T
  /-- the arity template (the queried cache's tape 13). -/
  ar : Fin T
  /-- the phase width `1^b` (`Wd 218`). -/
  wd : Fin T
  har : ar.val < d.F ∧ (ar.val < 278 ∨ 284 ≤ ar.val)
  hwd : wd.val < d.F ∧ (wd.val < 278 ∨ 284 ≤ wd.val)
  hne : ar ≠ wd

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

theorem s2V_lt (j : Nat) (hj : j < 323) : s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val j < d.U := by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have h1 := pl.har.1
  have h2 := pl.hwd.1
  have := s2V_in d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val j hj
  unfold InS2 at this
  omega

/-- The dock. -/
def s2 : Fin 323 → Fin T := fun j =>
  ⟨s2V d eX pX gW (Dimension.P eR eV) pl.ar.val pl.wd.val j.val,
    Nat.lt_of_lt_of_le (pl.s2V_lt j.val j.isLt) pl.hT⟩

end Place

section dec


end dec

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

/-! ## 2. `Once`'s pipeline dock, blank and mask -/

/-- The pipeline dock: port `0` (`pq`) is the arity tape, port `x` the fresh tape `JB + x`. -/
def ds : Fin (Dimension.P eR eV) → Fin T := fun x =>
  if x.val = 0 then pl.ar else ⟨JB d eX pX gW + x.val, by
    obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
    have := x.isLt
    have := pl.hT
    omega⟩

/-- `Once`'s blank scratch `b0`. -/
def b0 : Fin T := ⟨JB d eX pX gW + Dimension.P eR eV, by
  obtain ⟨hF, hB, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have := pl.hT
  omega⟩

/-- `Once`'s erase set: every source tape at or above `F` except the clear driver/log and the three kept
pipeline ports (`Rc`'s log, `V`, `V`'s log). -/
def mask (_pl : Place d eX pX gW eR eV X T) : Fin T → Bool := fun x =>
  decide (d.F ≤ x.val ∧ x.val < d.U ∧ x.val ≠ d.scrV 11 ∧ x.val ≠ d.scrV 12 ∧
    x.val ≠ JB d eX pX gW + (65 + 2*eR) ∧ x.val ≠ JB d eX pX gW + Dimension.P eR eV - 2 ∧
    x.val ≠ JB d eX pX gW + Dimension.P eR eV - 1)

end Place

end
end NearCubicWires.SourceConstruction.InitRun
end
