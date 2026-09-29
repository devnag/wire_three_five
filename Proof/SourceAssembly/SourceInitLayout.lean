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

/-! ## 1. The dock of the post-`Once` machine -/

section vals
end vals

namespace Place

end Place

section dec


end dec

namespace Place

/-! ## 2. `Once`'s pipeline dock, blank and mask -/

end Place

end
end NearCubicWires.SourceConstruction.InitRun
end
