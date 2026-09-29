import Proof.Wire_3_5.UnionMachine.FsNeed

/-! # C6, the FILTER setup: the machine, to the `FiltSetupSpec5`

"The filter's seed is `e`; [...] the filter `F_e` [...] of the regular filter at the call's parameters"
(filt:gap, P3:2019-2054, 2083-2100): from the FILTER setup's entry bank (`FsIn2`: the eight values, the request, the
counter, the data) the setup program `FsRun.fsProg` computes the filter's numbers at every length (`GapNums`
parts around the length branch), the setup's registers, the walk bank's inputs with the seed's index word (X1) and the
zero words, and raises the FILTER flag: a FILTER-ready state (`UnitReady.FiltReady`) at the seed
`(gapSeedEquiv P).symm g`, rulers `rulerW P`, within `fsCost cap` (`O(cap²)`) at every capacity above
`fsNeed = 10^5·(len + cap + err + L + r4 + G + off + |GapSeed P| + 1)^3`.

* **`fsSpec W : FiltSetupSpec5 W`** (the consumers: the SYM FILTER rows, THR's THR FILTER rows, the HASH
  writer's aux row).

Paper quantity of the main type: the FILTER-ready unit state of the regular filter at the call's seed. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FsSpec
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.UnionMachine

theorem fsCost_poly (c : ℕ) : ValidatorPolynomialDomination.PolyBounded (FsRun.fsCost c) c 200000 2 := by
  unfold ValidatorPolynomialDomination.PolyBounded FsRun.fsCost UnaryPow.sq
  nlinarith

/-- **The FILTER-setup machine**, built to the `FiltSetupSpec5`. -/
noncomputable def fsSpec (W : WalkBankProducer) : FiltSetupSpec5 W where
  prog := FsRun.fsProg W.x
  need := FsNeed.fsNeed
  bound := FsRun.fsCost
  Cn := 100000
  Dn := 3
  need_poly := fun _ _ _ _ _ _ _ _ => le_rfl
  Cb := 200000
  Db := 2
  bound_poly := fsCost_poly
  run := fun cap P g hg L r4 G off w out u j σ hU hlen hneed hin => by
    obtain ⟨τ, hx, h0, h0h, h2, h2h, h150, h150h, h151, h151h, rest⟩ :=
      FsReady.fs_ready W cap P g hg L r4 G off w out u j σ hU hlen
        (FsNeed.fsCap_of_need cap P g L r4 G off hg hlen hneed) hin
    exact ⟨τ, _, hx, le_rfl, h0, h0h, h2, h2h, h150, h150h, h151, h151h, rest⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FsSpec
