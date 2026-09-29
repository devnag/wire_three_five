import Proof.Wire_3_5.Primitive.Writers.ThrN3
import Proof.Wire_3_5.Primitive.SeedFix.C4SG

/-! # c4 THR block, numbers part 4: the THR numbers machine's program, as one run

`bigWT F = numsTW ; seedW ; F.prog ; derW ; emitsW symEmits` (the SYM `bigW` with the THR numbers in front): from the
THR cell's entry, the thirty-nine loop-entry words `symClean` at the THR values (the THR loop entry is the SYM
word table at the THR `Q`, `kh`, `ℓ`, `n_T = 2^{seedBits}·|𝒢|·Σp`). The words' part is one generic run
(`words_spec`) from any state holding the numbers.

Paper quantity: the THR loop entry's words (samp:seed, samp:q at a THR call; P3:2987-3000, 3011-3016). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- **The words' program from the numbers**: the seed block, the free numbers, the derived numbers, the words. -/
def wordsW (F : FreeProg) : WM (LNS 0) LNR := .seq seedW (.seq F.prog (.seq derW (emitsW symEmits)))

/-- **The words' run from any state holding the numbers** (`bigS_spec` after its numbers). -/
theorem words_spec (F : FreeProg) (cap : ℕ) (σ : WState (LNS 0) LNR)
    (Q kh gs fs pi bv sv r2 rv n L capS a nc M : ℕ)
    (eQ : σ.val (KB 52) = Q) (ekh : σ.val (SGb 8) = kh) (e21 : σ.val (G 21) = gs) (e41 : σ.val (G 41) = fs)
    (e52 : σ.val (G 52) = pi) (eb : σ.val (SGb 5) = bv) (es : σ.val (SGb 4) = sv) (er2 : σ.val (SGb 6) = r2)
    (er : σ.val (SGb 3) = rv) (en : σ.val dN = n) (eL : σ.val (SGb 1) = L) (ecap : σ.val (Hb 13) = capS)
    (ea : σ.val dA = a) (enc : σ.val dNC = nc) (eM : σ.val dMS = M)
    (hz : ∀ q : Fin LNR, 64 ≤ q.val → q.val < 250 → σ.val q = 0)
    (hsk : ∀ k : Fin 161, 120 ≤ k.val → σ.st (sk 0 k) = [])
    (hsh : ∀ k : Fin 161, 120 ≤ k.val → σ.sh (sk 0 k) = 0)
    (hsc : SeedCap cap Q kh gs fs pi bv sv r2 rv n)
    (x : FreeIn) (hx : x = ⟨n, kh, L, capS, a, nc, M, Q, max (kh + kh) (Nat.clog 2 Q), gs * fs * pi, wOf kh Q,
      (n - rv * bv + 1) / 2 + (bv - sv) * r2⟩)
    (hF : F.ok cap x) (hdc : DerCap cap Q kh (F.val x 0) (F.val x 1))
    (cQl : Q - 1 < 2 ^ max (kh + kh) (Nat.clog 2 Q)) (cQ : Q + 1 ≤ cap)
    (cl : 3 * max (kh + kh) (Nat.clog 2 Q) + Q + 3 ≤ cap) (ck : kh + kh + 1 ≤ cap)
    (cfr : ∀ j, F.val x j + F.val x j + 3 ≤ cap)
    (cdd : ∀ i, derVals Q kh (F.val x 0) (F.val x 1) i + derVals Q kh (F.val x 0) (F.val x 1) i + 3 ≤ cap)
    (ccnt : gs * fs * pi * 2 ^ wOf kh Q + 1 ≤ cap)
    (cd2 : (0 + ((n - rv * bv + 1) / 2 + (bv - sv) * r2) + ((n - rv * bv + 1) / 2 + (bv - sv) * r2)) +
      (0 + ((n - rv * bv + 1) / 2 + (bv - sv) * r2) + ((n - rv * bv + 1) / 2 + (bv - sv) * r2)) + 3 ≤ cap)
    (c17 : 17 ≤ cap) :
    ∃ τ c, WExec cap (wordsW F) σ τ c ∧
      c ≤ 400 * UnaryPow.sq cap + 1 + (F.cost cap x + 1 + (200 * UnaryPow.sq cap + 1 + (400 * UnaryPow.sq cap))) ∧
      (∀ j : Fin 39, τ.st (sk 0 (symO j)) = symClean Q kh (max (kh + kh) (Nat.clog 2 Q)) (gs * fs * pi * 2 ^ wOf kh Q)
        (0 + ((n - rv * bv + 1) / 2 + (bv - sv) * r2) + ((n - rv * bv + 1) / 2 + (bv - sv) * r2))
        (F.val x) (derVals Q kh (F.val x 0) (F.val x 1)) j) ∧
      (∀ s, (∀ j : Fin 39, s ≠ sk 0 (symO j)) → τ.st s = σ.st s) ∧ τ.cell = σ.cell := by
  set ell := max (kh + kh) (Nat.clog 2 Q) with hell
  set cnt := gs * fs * pi * 2 ^ wOf kh Q with hcnt
  set dRv := (n - rv * bv + 1) / 2 + (bv - sv) * r2 with hdRv
  set d2 := 0 + dRv + dRv with hd2
  set fr := F.val x with hfr
  set dd := derVals Q kh (F.val x 0) (F.val x 1) with hdd
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨τ2, c2, e2, c2le, s2X2, s2N0, s2W0, s2P1, s2CC, s2ST, s2D2, s2X0, s2T, s2fr, s2st, s2sh, s2cl⟩ :=
    seed_spec cap σ Q kh gs fs pi bv sv r2 rv n eQ ekh e21 e41 e52 eb es er2 er en hz hsc
  have k2 : ∀ q : Fin LNR, (q.val < 64 ∨ 127 ≤ q.val) → τ2.val q = σ.val q := s2fr
  have hfreg : FreeRegs τ2 x := by
    rw [hx]
    exact ⟨by rw [k2 _ (by right; decide)]; exact en, by rw [k2 _ (by right; decide)]; exact ekh,
      by rw [k2 _ (by right; decide)]; exact eL, by rw [k2 _ (by right; decide)]; exact ecap,
      by rw [k2 _ (by right; decide)]; exact ea, by rw [k2 _ (by right; decide)]; exact enc,
      by rw [k2 _ (by right; decide)]; exact eM, by rw [k2 _ (by left; decide)]; exact eQ, s2X2, s2N0, s2W0, s2ST⟩
  obtain ⟨τ3, e3, s3fb, s3fr, s3st, s3sh, s3cl⟩ := F.run cap τ2 x hfreg
    (fun q h1' h2' => by rw [k2 q (by right; omega)]; exact hz q (by omega) (by omega))
    (fun q h1' h2' => by rw [k2 q (by right; omega)]; exact hz q (by omega) (by omega)) hF
  have k3 : ∀ q : Fin LNR, (q.val < 130 ∨ (137 ≤ q.val ∧ q.val < 177) ∨ 200 ≤ q.val) → τ3.val q = τ2.val q := s3fr
  obtain ⟨τ4, c4, e4, c4le, d0, d1, d2', d3, d4, d5, d6, r0, r4, t4, fr4, rb4, st4, sh4, cl4⟩ :=
    der_spec cap τ3 Q kh (F.val x 0) (F.val x 1)
      (by rw [k3 _ (by left; decide)]; exact s2X0) (by rw [k3 _ (by left; decide)]; exact s2X2) (s3fb 0) (s3fb 1)
      (by rw [k3 _ (by left; decide)]; exact s2W0) (by rw [k3 _ (by left; decide), k2 _ (by left; decide)]; exact eQ)
      (fun q h1' h2' => by rw [k3 q (by right; left; omega), k2 q (by right; omega)]; exact hz q (by omega) (by omega))
      (by rw [k3 _ (by left; decide)]; exact s2T) hdc
  have k4 : ∀ q : Fin LNR, (q.val < 140 ∨ 177 ≤ q.val) → τ4.val q = τ3.val q := fr4
  have hSR : SymRegs τ4 Q kh ell cnt d2 fr dd := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun j => ?_, fun i => ?_, r0, r4, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k4 _ (by left; decide), k3 _ (by left; decide)]; exact s2X0
    · rw [k4 _ (by left; decide), k3 _ (by left; decide)]; exact s2X2
    · rw [k4 _ (by right; decide), k3 _ (by right; right; decide), k2 _ (by right; decide)]; exact ekh
    · rw [k4 _ (by left; decide), k3 _ (by left; decide), k2 _ (by left; decide)]; exact eQ
    · rw [k4 _ (by left; decide), k3 _ (by left; decide)]; exact s2CC
    · rw [k4 _ (by left; decide), k3 _ (by left; decide)]; exact s2D2
    · rw [k4 _ (by left; simp [FB, blk_val]; omega)]; exact s3fb j
    · fin_cases i
      · exact d0
      · exact d1
      · exact d2'
      · exact d3
      · exact d4
      · exact d5
      · exact d6
    all_goals first
      | (rw [rb4 _ (by decide), k3 _ (by right; left; decide), k2 _ (by right; decide)]
         exact hz _ (by decide) (by decide))
  have hst4 : τ4.st = σ.st := by rw [st4, s3st, s2st]
  have hsh4 : ∀ k : Fin 161, 120 ≤ k.val → τ4.sh (sk 0 k) = 0 := by
    intro k hk
    rw [sh4, s3sh, s2sh]
    exact hsh k hk
  have hok := symEmits_ok cap τ4 Q kh ell cnt d2 fr dd hSR (fun k hk => by rw [hst4]; exact hsk k hk) hsh4
    (fun q h1' h2' => by rw [k4 q (by right; omega), k3 q (by right; right; omega), k2 q (by right; omega)]
                         exact hz q (by omega) (by omega))
    cQl cQ cl ck cfr cdd ccnt (by rw [hd2]; exact cd2) c17
  obtain ⟨τ5, e5, sE, sO, -, -, -, cl5⟩ := emitsW_spec cap symEmits τ4 hok symEmits_O_nodup symEmits_OP_nodup
    (by rw [k4 _ (by right; decide), k3 _ (by right; right; decide), k2 _ (by right; decide)]; exact hz _ (by decide) (by decide))
    (by rw [k4 _ (by right; decide), k3 _ (by right; right; decide), k2 _ (by right; decide)]; exact hz _ (by decide) (by decide))
  have hcost5 : (symEmits.map (wordCost τ4)).sum + symEmits.length ≤ 400 * UnaryPow.sq cap := by
    have hle : ∀ e ∈ symEmits, wordCost τ4 e ≤ 8 * UnaryPow.sq cap := by
      intro e he
      obtain ⟨sh1, sh2, sh3⟩ := symEmits_short e he
      have hw := hok e he
      refine wordCost_le cap τ4 e (fun p hp A u hpA => ⟨(hw.hps p hp A u hpA).2, sh1 p hp A u hpA⟩) sh2 sh3
        (fun R hR => ?_)
      have hhd := hw.hhd
      rw [hR] at hhd
      obtain ⟨-, -, -, -, -, -, -, -, hc⟩ := hhd
      omega
    have := List.sum_le_card_nsmul (symEmits.map (wordCost τ4)) (8 * UnaryPow.sq cap) (fun y hy => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy; exact hle e he)
    simp only [List.length_map, symEmits_length, smul_eq_mul] at this
    rw [symEmits_length]
    omega
  have fin0 : τ5.st (sk 0 120) = symClean Q kh ell cnt d2 fr dd 0 := by
    have hw := symW0 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin1 : τ5.st (sk 0 121) = symClean Q kh ell cnt d2 fr dd 1 := by
    have hw := symW1 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin2 : τ5.st (sk 0 122) = symClean Q kh ell cnt d2 fr dd 2 := by
    have hw := symW2 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin3 : τ5.st (sk 0 123) = symClean Q kh ell cnt d2 fr dd 3 := by
    have hw := symW3 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin4 : τ5.st (sk 0 124) = symClean Q kh ell cnt d2 fr dd 4 := by
    have hw := symW4 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin5 : τ5.st (sk 0 125) = symClean Q kh ell cnt d2 fr dd 5 := by
    have hw := symW5 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin6 : τ5.st (sk 0 126) = symClean Q kh ell cnt d2 fr dd 6 := by
    have hw := symW6 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin7 : τ5.st (sk 0 127) = symClean Q kh ell cnt d2 fr dd 7 := by
    have hw := symW7 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin8 : τ5.st (sk 0 128) = symClean Q kh ell cnt d2 fr dd 8 := by
    have hw := symW8 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin9 : τ5.st (sk 0 129) = symClean Q kh ell cnt d2 fr dd 9 := by
    have hw := symW9 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin10 : τ5.st (sk 0 130) = symClean Q kh ell cnt d2 fr dd 10 := by
    have hw := symW10 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin11 : τ5.st (sk 0 131) = symClean Q kh ell cnt d2 fr dd 11 := by
    have hw := symW11 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin12 : τ5.st (sk 0 132) = symClean Q kh ell cnt d2 fr dd 12 := by
    have hw := symW12 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin13 : τ5.st (sk 0 133) = symClean Q kh ell cnt d2 fr dd 13 := by
    have hw := symW13 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin14 : τ5.st (sk 0 135) = symClean Q kh ell cnt d2 fr dd 14 := by
    have hw := symW14 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin15 : τ5.st (sk 0 136) = symClean Q kh ell cnt d2 fr dd 15 := by
    have hw := symW15 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin16 : τ5.st (sk 0 137) = symClean Q kh ell cnt d2 fr dd 16 := by
    have hw := symW16 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin17 : τ5.st (sk 0 138) = symClean Q kh ell cnt d2 fr dd 17 := by
    have hw := symW17 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin18 : τ5.st (sk 0 139) = symClean Q kh ell cnt d2 fr dd 18 := by
    have hw := symW18 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin19 : τ5.st (sk 0 140) = symClean Q kh ell cnt d2 fr dd 19 := by
    have hw := symW19 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin20 : τ5.st (sk 0 141) = symClean Q kh ell cnt d2 fr dd 20 := by
    have hw := symW20 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin21 : τ5.st (sk 0 142) = symClean Q kh ell cnt d2 fr dd 21 := by
    have hw := symW21 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin22 : τ5.st (sk 0 143) = symClean Q kh ell cnt d2 fr dd 22 := by
    have hw := symW22 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin23 : τ5.st (sk 0 144) = symClean Q kh ell cnt d2 fr dd 23 := by
    have hw := symW23 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin24 : τ5.st (sk 0 145) = symClean Q kh ell cnt d2 fr dd 24 := by
    have hw := symW24 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin25 : τ5.st (sk 0 146) = symClean Q kh ell cnt d2 fr dd 25 := by
    have hw := symW25 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin26 : τ5.st (sk 0 147) = symClean Q kh ell cnt d2 fr dd 26 := by
    have hw := symW26 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin27 : τ5.st (sk 0 148) = symClean Q kh ell cnt d2 fr dd 27 := by
    have hw := symW27 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin28 : τ5.st (sk 0 149) = symClean Q kh ell cnt d2 fr dd 28 := by
    have hw := symW28 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin29 : τ5.st (sk 0 150) = symClean Q kh ell cnt d2 fr dd 29 := by
    have hw := symW29 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin30 : τ5.st (sk 0 151) = symClean Q kh ell cnt d2 fr dd 30 := by
    have hw := symW30 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin31 : τ5.st (sk 0 152) = symClean Q kh ell cnt d2 fr dd 31 := by
    have hw := symW31 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin32 : τ5.st (sk 0 153) = symClean Q kh ell cnt d2 fr dd 32 := by
    have hw := symW32 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin33 : τ5.st (sk 0 154) = symClean Q kh ell cnt d2 fr dd 33 := by
    have hw := symW33 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin34 : τ5.st (sk 0 155) = symClean Q kh ell cnt d2 fr dd 34 := by
    have hw := symW34 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin35 : τ5.st (sk 0 156) = symClean Q kh ell cnt d2 fr dd 35 := by
    have hw := symW35 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin36 : τ5.st (sk 0 157) = symClean Q kh ell cnt d2 fr dd 36 := by
    have hw := symW36 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin37 : τ5.st (sk 0 158) = symClean Q kh ell cnt d2 fr dd 37 := by
    have hw := symW37 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  have fin38 : τ5.st (sk 0 159) = symClean Q kh ell cnt d2 fr dd 38 := by
    have hw := symW38 τ4 Q kh ell cnt d2 fr dd hSR
    rw [← hw.1, sE _ (List.get_mem _ _), hw.2]; rfl
  refine ⟨τ5, _, WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)), by omega, fun j => ?_, fun s hs => ?_, ?_⟩
  · fin_cases j
    · exact fin0
    · exact fin1
    · exact fin2
    · exact fin3
    · exact fin4
    · exact fin5
    · exact fin6
    · exact fin7
    · exact fin8
    · exact fin9
    · exact fin10
    · exact fin11
    · exact fin12
    · exact fin13
    · exact fin14
    · exact fin15
    · exact fin16
    · exact fin17
    · exact fin18
    · exact fin19
    · exact fin20
    · exact fin21
    · exact fin22
    · exact fin23
    · exact fin24
    · exact fin25
    · exact fin26
    · exact fin27
    · exact fin28
    · exact fin29
    · exact fin30
    · exact fin31
    · exact fin32
    · exact fin33
    · exact fin34
    · exact fin35
    · exact fin36
    · exact fin37
    · exact fin38
  · rw [sO s (fun e he => ?_), hst4]
    obtain ⟨k, hk⟩ := List.get_of_mem he
    rw [← hk]
    have := hs ⟨k.val, by rw [← symEmits_length]; exact k.isLt⟩
    intro e2'
    apply this
    rw [e2']
    fin_cases k <;> rfl
  · rw [cl5, cl4, s3cl, s2cl]

/-- **The THR numbers machine's program.** -/
def bigWT (F : FreeProg) (cr fe : ℕ) : WM (LNS 0) LNR := .seq (numsTW cr fe) (wordsW F)

/-- **The THR numbers machine's program, run** (C4.K's free numbers `F`): from the THR cell's entry, the thirty-nine
loop-entry words on the streams `symO` at the THR values (`Q` the THR count, `n_T = 2^{seedBits}·|𝒢|·Σp`), every
other stream as at entry. -/
theorem bigT_spec (F : FreeProg) (cap cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n)
    (w : List Bool) (codes cc : List ℕ) (tl : List Bool) (hs xs : List ℕ) (tg Kb : ℕ)
    (hw : w = Data.reqW P.n true codes cc tl) (hhs : hs.length = 16) (hxs : xs.length ≤ 2)
    (h0v : hs.getD 0 0 = xs.length) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb)
    (cW : 2 * w.length + 2 ≤ cap)
    (cP : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
      Kb + P.n + codes.length + 1 ≤ cap)
    (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (capT err g cu pS I Q kh gs : ℕ) (hT : hs.getD 1 0 = capT) (hg : hs.getD 2 0 = g) (hcu : hs.getD 4 0 = cu)
    (hp : hs.getD 6 0 = pS) (herr : err = fe * Nat.clog 2 (P.n + 2)) (hkh : kh = P.s * (P.r / 2))
    (hgs : gs = 2 ^ (gP P.n capT err).seedBits)
    (cT1 : 1 ≤ capT) (cT : capT * 32 + 2 ≤ cap) (cL : 2 * (P.n + 1) ^ 26 + 8 ≤ cap) (cE : err + 4 ≤ cap)
    (cSB : 2 ^ ((gP P.n capT err).seedBits + 1) ≤ cap)
    (cLB : (gP P.n capT err).labelBits + (gP P.n capT err).fieldBits + (gP P.n capT err).walkLen + 512 ≤ cap)
    (cB : 2 * (g * cu) + 2 ≤ cap)
    (hI : I = g * pS * 2 ^ (gP P.n capT err).seedBits * (2 * (g * cu) + 1) * (2 * (g * cu) + 1) + 1)
    (hQ : Q = 2 ^ ((kh * 5 + 3) / 2 / 2) * (I * 8192 * P.n * P.n)) (hn : 2 ≤ P.n) (cQ2 : 2 * Q ≤ cap)
    (hsc : SeedCap cap Q kh gs g pS P.b P.s (P.r / 2) P.r P.n)
    (x : FreeIn) (hx : x = ⟨P.n, kh, Nat.clog 2 (P.n + 2), capT, codes.length, cc.length, hs.getD 7 0, Q,
      max (kh + kh) (Nat.clog 2 Q), gs * g * pS, wOf kh Q, (P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)⟩)
    (hF : F.ok cap x) (hdc : DerCap cap Q kh (F.val x 0) (F.val x 1))
    (cQl : Q - 1 < 2 ^ max (kh + kh) (Nat.clog 2 Q)) (cQ : Q + 1 ≤ cap)
    (cl : 3 * max (kh + kh) (Nat.clog 2 Q) + Q + 3 ≤ cap) (ck : kh + kh + 1 ≤ cap)
    (cfr : ∀ j, F.val x j + F.val x j + 3 ≤ cap)
    (cdd : ∀ i, derVals Q kh (F.val x 0) (F.val x 1) i + derVals Q kh (F.val x 0) (F.val x 1) i + 3 ≤ cap)
    (ccnt : gs * g * pS * 2 ^ wOf kh Q + 1 ≤ cap)
    (cd2 : (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) +
        ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2))) +
      (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) +
        ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2))) + 3 ≤ cap)
    (c17 : 17 ≤ cap) :
    ∃ τ c, WExec cap (bigWT F cr fe) (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ numsTCost cap P.n codes.length cc.length Kb + 1 + (400 * UnaryPow.sq cap + 1 + (F.cost cap x + 1 +
        (200 * UnaryPow.sq cap + 1 + (400 * UnaryPow.sq cap)))) ∧
      (∀ j : Fin 39, τ.st (sk 0 (symO j)) = symClean Q kh (max (kh + kh) (Nat.clog 2 Q)) (gs * g * pS * 2 ^ wOf kh Q)
        (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)))
        (F.val x) (derVals Q kh (F.val x 0) (F.val x 1)) j) ∧
      (∀ s, (∀ j : Fin 39, s ≠ sk 0 (symO j)) →
        τ.st s = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))).st s) ∧
      τ.cell = false := by
  obtain ⟨τ1, c1, e1, c1le, v1N, v1A, v1NC, v1MS, v1L, v1r, v1s, v1b, v1r2, v1kh, v1k, v1err, v1cap, v1G21, v1G41,
    v1G52, v1KB, v1z, v1st, v1sh, v1cl⟩ := numsT_spec cap cr fe P hrP w codes cc tl hs xs tg Kb hw hhs hxs h0v hKb cW
      cP hcl hcs hcS capT err g cu pS I Q hT hg hcu hp herr cT1 cT cL cE cSB cLB cB hI (by rw [← hkh]; exact hQ) hn cQ2
  have hsk : ∀ k : Fin 161, 120 ≤ k.val → τ1.st (sk 0 k) = [] := by
    intro k hk
    have n0 : sk 0 k ≠ sk 0 0 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n1 : sk 0 k ≠ sk 0 1 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n2 : sk 0 k ≠ sk 0 2 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n3 : sk 0 k ≠ sk 0 113 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    rw [v1st]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n0, n1, n2, n3]
  have hsh : ∀ k : Fin 161, 120 ≤ k.val → τ1.sh (sk 0 k) = 0 := by
    intro k hk
    have n3 : sk 0 k ≠ sk 0 113 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n1 : sk 0 k ≠ sk 0 1 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    rw [v1sh _ n3]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n1]
  obtain ⟨τ, c, e, cle, hwd, hrest, hcl5⟩ := words_spec F cap τ1 Q kh gs g pS P.b P.s (P.r / 2) P.r P.n
    (Nat.clog 2 (P.n + 2)) capT codes.length cc.length (hs.getD 7 0) v1KB (by rw [hkh]; exact v1kh)
    (by rw [hgs]; exact v1G21) v1G41 v1G52 v1b v1s v1r2 v1r v1N v1L v1cap v1A v1NC v1MS v1z hsk hsh hsc x hx hF hdc
    cQl cQ cl ck cfr cdd ccnt cd2 c17
  exact ⟨τ, _, WExec.seq e1 e, by omega, hwd, fun s hs => by rw [hrest s hs, v1st], by rw [hcl5, v1cl]⟩

end NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
