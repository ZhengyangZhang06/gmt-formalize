# Chapter 1 — Preliminary Measure Theory (Simon, printed pp. 1–38)

Frozen contract: `GMT/Ch01/Contract.lean` (namespace `GMT.Ch01`); the prover edits the byte-identical
copy `GMT/Ch01/Submission.lean`. The single target is

```
theorem GMT.Ch01.main_theorem : CaratheodoryCriterion ∧ BorelRegularApproximation ∧ LusinTheorem ∧
  LebesgueEqHausdorff ∧ IsodiametricInequality ∧ UpperDensityComparison ∧ UpperDensityTheorem ∧
  BesicovitchCovering ∧ GeneralDensityTheorem ∧ LebesgueDifferentiation ∧ RadonNikodymTheorem ∧
  HausdorffDensityBounds ∧ RieszPositive ∧ RieszVector ∧ RadonCompactness
```

All Props quantify over spaces in arbitrary universes (`Type u`, `Type v`), so `main_theorem` is
universe-polymorphic.

## Conventions (as in the book)

* A measure is an outer measure `μ : OuterMeasure X`; "`μ`-measurable set" = `μ.IsCaratheodory A` (Def. 1.2).
* "`μ`-a.e." = Mathlib's `∀ᵐ x ∂μ` for the outer measure `μ` (complement of the property has `μ`-outer measure 0).
* Integrals and "`μ`-measurable function" use `caratheodoryMeasure μ`, the measure on the Carathéodory σ-algebra
  (Lemma 1.6/Remark 1.7). It is definitionally `IsRadonOuterMeasure.toCaratheodoryMeasure` of SimonGMT.
* `B_ρ(x)` = `Metric.closedBall x ρ`; Lebesgue outer measure `Lⁿ` = `volume` on `EuclideanSpace ℝ (Fin n)`.

## Statement map

| # | Book item (page) | Lean name | Statement / hypotheses | Existing `Poincare.SimonGMT` proof |
|---|---|---|---|---|
| 1 | Thm 1.13 Carathéodory criterion (p. 6) | `CaratheodoryCriterion` | `X` metric; `μ(A∪B)=μA+μB` whenever `dist(A,B)>0` (∃ `r>0` with `r ≤ d(a,b)` ∀ `a∈A,b∈B`) ⇒ every Borel set is `μ`-measurable. | `caratheodory_metric_criterion` (Chapter01/MetricCriterion.lean), via Mathlib `OuterMeasure.IsMetric.borel_le_caratheodory`; only the bridge "positive distance ⇒ `Metric.AreSeparated`" is needed. |
| 2 | Thm 1.15 regularity (p. 7) | `BorelRegularApproximation` | `X` topological, every closed set `G_δ`; `μ` Borel regular, open σ-finite ⇒ (1) `μA = inf{μU : U open ⊇ A}` ∀`A`; (2) `μA = sup{μC : C closed ⊆ A}` ∀ `μ`-measurable `A`. | `IsBorelRegularOuterMeasure.simon_theorem_1_15` (ExactRegularity.lean) — identical up to unfolding `ClosedSetsAreGDelta`. |
| 3 | Thm 1.17 Lusin (p. 8) | `LusinTheorem` | `X` topological, closed sets `G_δ`; `μ` Borel regular; `A` `μ`-measurable, `μA<∞`; `f : A → ℝ` measurable for the trace σ-algebra; ∀ `ε>0` ∃ closed `C ⊆ A`, `μ(A\C) < ε`, `f∘inclusion` continuous. | `IsBorelRegularOuterMeasure.simon_theorem_1_17` (Lusin.lean) (ε : ℝ≥0∞ there; use `ENNReal.ofReal ε`). |
| 4 | Thm 2.9 `Lⁿ = Hⁿ = Hⁿ_δ` (p. 11) | `LebesgueEqHausdorff` | ∀ `n : ℕ`, `δ>0` real, `A ⊆ ℝⁿ`: `volume A = Hⁿ(A)` and `Hⁿ(A) = Hⁿ_δ(A)`. | `simon_theorem_2_9` (EuclideanNormalization.lean) with `δ := ENNReal.ofReal δ`. |
| 5 | Thm 2.10 isodiametric inequality (p. 11) | `IsodiametricInequality` | ∀ `n`, `A ⊆ ℝⁿ`: `volume A ≤ ω_n (diam A/2)ⁿ`. | `simon_theorem_2_10` (EuclideanNormalization.lean) + `ENNReal.rpow_natCast`. |
| 6 | Thm 3.3 density comparison (p. 14) | `UpperDensityComparison` | `X` metric, `μ` Borel regular, real `n ≥ 0`, `t ≥ 0`, `A₁ ⊆ A₂` arbitrary; `Θ^{*n}(μ,A₂,x) ≥ t` on `A₁` ⇒ `t·Hⁿ(A₁) ≤ μ(A₂)`. | `simon_theorem_3_3` (DensityComparison.lean) — identical. |
| 7 | Thm 3.6 upper density theorem (p. 16) | `UpperDensityTheorem` | `μ` Borel regular, `A` `μ`-measurable, `μA<∞` ⇒ `Θ^{*n}(μ,A,x)=0` for `Hⁿ`-a.e. `x ∉ A`. | `simon_theorem_3_6` (DensityComparison.lean) (null-set form = a.e. form). |
| 8 | Lemma 3.12 Besicovitch (p. 18) | `BesicovitchCovering` | ∀ `n` ∃ `N` ∀ families `B` of closed balls in `ℝⁿ` (centre, radius>0) with bounded radii ∃ `N` pairwise-disjoint subfamilies covering the centres. | `exists_besicovitchCovering_families` (Densities.lean) with index type `↥B`, `N = Besicovitch.multiplicity (EuclideanSpace ℝ (Fin n))`. |
| 9 | Thm 3.16 general density theorem (p. 20) | `GeneralDensityTheorem` | `X` metric; `μ` Borel regular, open σ-finite, Symmetric Vitali; `A` `μ`-measurable ⇒ `μ(A∩B_ρ(x))/μ(B_ρ(x)) → 1` `μ`-a.e. on `A`, `→ 0` `μ`-a.e. on `X\A`. | `simon_theorem_3_16` (GeneralDensity.lean) (indicator form, a.e. for `hμ.toBorelMeasure`; same null sets by `toBorelMeasure_apply_all`). |
| 10 | Cor 3.17 Lebesgue differentiation (p. 20) | `LebesgueDifferentiation` | as in 3.16; `f` `μ`-measurable with `∫_{B_ρ(x)}|f|dμ<∞` for some `ρ>0` at each `x` ⇒ `μ(B_ρ(x))⁻¹∫_{B_ρ(x)} f dμ → f(x)` `μ`-a.e. | `simon_corollary_3_17_of_caratheodory` (GeneralDifferentiation.lean); its integrals are against `hμ.toBorelMeasure`, so a trim/a.e.-Borel-version bridge to `caratheodoryMeasure` is needed. |
| 11 | Thm 3.24 Radon–Nikodym (pp. 24–25) | `RadonNikodymTheorem` | `μ, μ₀` Borel regular, open σ-finite, `μ₀` Symmetric Vitali. (0) the ratio `μ(B_ρ)/μ₀(B_ρ)` tends to the upper density `Θ` `μ₀`-a.e. (this identifies the book's integrand `Θ^{μ₀}(μ,·)`); (i) `μ ≪ μ₀` ⇒ `μA = ∫_A Θ dμ₀` for Borel `A`; (ii) ∃ Borel `Z`, `μ₀Z=0`, `μA = ∫_A Θ dμ₀ + μ(Z∩A)`; (iii) if also `μ` Symmetric Vitali, (ii) holds with `Z = {ratio → ∞}` and `μ₀Z = 0`. | (0) `simon_theorem_3_23_ii` (RadonNikodymDensity.lean); (i) `simon_theorem_3_24_i`, (ii) `simon_theorem_3_24_ii`, (iii) `simon_theorem_3_24_iii` (RadonNikodymTheorem.lean) / `simon_theorem_3_24_iii_borel` (InfiniteDensitySet.lean; `outerInfiniteDensitySet` is our `Z`). Their lintegrals are against `hν.toBorelMeasure`; bridge via `lintegral_trim` + a.e. equality with `rnDeriv`. |
| 12 | Thm 3.26 Hausdorff density bounds (p. 26) | `HausdorffDensityBounds` | `X` metric, real `n ≥ 0`, `A` `Hⁿ`-measurable: (1) `Hⁿ(A)<∞` ⇒ `Θ^{*n}(Hⁿ,A,x) ≤ 1` `Hⁿ`-a.e. on `A`; (2) `Hⁿ_δ(A)<∞` ∀`δ>0` ⇒ `Θ^{*n}(Hⁿ_∞,A,x) ≥ 2⁻ⁿ` `Hⁿ`-a.e. on `A`. | `simon_theorem_3_26_i` (HausdorffDensityBounds.lean), `simon_theorem_3_26_ii` (HausdorffContentDensity.lean). |
| 13 | Thm 4.12 Riesz, non-negative functionals (p. 33) | `RieszPositive` | `X` locally compact Hausdorff; `Λ : C_c(X,ℝ≥0) →ₗ[ℝ≥0] ℝ≥0` (= additive, positively homogeneous `λ : K₊ → [0,∞)`) ⇒ ∃ Radon `μ` with `Λ f = ∫ f dμ` ∀ `f ∈ K₊`. | Mathlib `NNRealRMK.integral_rieszMeasure`, `NNRealRMK.rieszMeasure_regular`; SimonGMT `isRadonOuterMeasure_toOuterMeasure` (RadonOuterMeasure.lean), `integral_radonCaratheodoryMeasure` (RadonCaratheodoryIntegral.lean). |
| 14 | Thm 4.14 Riesz representation (p. 35) | `RieszVector` | `X` LCH, `H` finite-dim real inner product space, `L : C_c(X,H) →ₗ[ℝ] ℝ` bounded above on `{|f| ≤ 1, spt f ⊆ K}` for each compact `K` ⇒ ∃ Radon `μ`, `μ`-measurable `ν : X → H`, `|ν|=1` `μ`-a.e., `L f = ∫ ⟨f,ν⟩ dμ`. | `simon_theorem_4_14` (RadonPolarRepresentation.lean) — same statement (`IsLocallyBoundedCcFunctional` unfolds to our hypothesis; `toCaratheodoryMeasure` ≡ `caratheodoryMeasure`). |
| 15 | Thm 4.16 compactness of Radon measures (p. 37), **corrected** | `RadonCompactness` | `X` locally compact Hausdorff **second countable**; Radon `μ_k` with `sup_k μ_k(K) < ∞` ∀ compact `K` ⇒ ∃ subsequence `φ` and Radon `μ` with `∫ f dμ_{φ k} → ∫ f dμ` ∀ `f ∈ C_c(X,ℝ)`. | **New** for non-compact `X`. Partial: `simon_theorem_4_16_compact_metrizable` (CompactMetrizableCompactness.lean) covers only compact metrizable `X` (insufficient). Printed version refuted by `simon_theorem_4_16_counterexample` (SequentialCompactnessCounterexample.lean). |

## Erratum corrections

* **4.16.** The printed hypotheses (locally compact, σ-compact, Hausdorff) do not imply the sequential conclusion:
  on the compact Hausdorff cube `{0,1}^{𝒫(ℕ)}` the Dirac masses at `x_k = (𝟙[k ∈ S])_S` satisfy the printed
  hypotheses but no subsequence converges against `C_c` (SimonGMT `simon_theorem_4_16_counterexample`; the proof's
  Alaoglu step gives only a subnet). The contract adds second countability. For locally compact Hausdorff spaces this
  is equivalent to "σ-compact + metrizable" and to "locally compact separable metrizable" — the standing assumption the
  book announces for §4 on p. 1 — and it covers `ℝᴺ`, open `U ⊆ ℝᴺ`, and `Gₙ(U)` used in later chapters.
* No other printed statement among the 15 needed correction (the "XXX" placeholders in the proofs of 3.15/3.26 and the
  wrong cross-reference 3.23(iii) → 3.24(iii) in Remark 3.25 do not affect the statements).

## Definitions

New in the contract:

* `GMT.Ch01.caratheodoryMeasure μ := @OuterMeasure.toMeasure X μ.caratheodory μ le_rfl` — the measure space of
  `μ`-measurable sets (Lemma 1.6, Remark 1.7). Faithful: Simon integrates against `μ` on `μ`-measurable sets and calls a
  function `μ`-measurable when it is measurable for this σ-algebra.

Reused from `Poincare.SimonGMT.Chapter01` (survey: clean; bodies read and checked against the book):

* `IsBorelRegularOuterMeasure` (Basic.lean): Borel sets are Carathéodory and every set has a Borel hull of equal measure (p. 5).
* `IsOpenSigmaFinite` (Basic.lean): countable cover by open sets of finite measure (Def. 1.14).
* `realUnitBallVolume m = ofReal(π^{m/2}/Γ(m/2+1))` = `ω_m` (Hausdorff.lean, p. 9).
* `simonHausdorffContentOuter m δ` / `simonHausdorffContent m δ` (Hausdorff.lean): `Hᵐ_δ` of (2.2) with strict bound
  `diam Cⱼ < δ`, value `∞` if no cover, empty covering sets costing 0 (correct at `m = 0`: `H⁰` is counting measure).
  `δ : ℝ≥0∞`; `δ = ∞` is Simon's `Hᵐ_∞` used in 3.26(2).
* `simonHausdorffOuterMeasureReal m = ⨆ δ>0, Hᵐ_δ` = `Hᵐ` of (2.1) (Hausdorff.lean); proved equal to
  `(ω_m/2^m)·μH[m]`.
* `dimensionalUpperDensity μ n A x = limsup_{ρ↓0} μ(A∩B_ρ(x))/(ω_n ρⁿ)` = `Θ^{*n}(μ,A,x)` of (3.1) (Densities.lean).
* `outerRelativeUpperDensity μ μ₀ x = limsup_{ρ↓0} μ(B_ρ(x))/μ₀(B_ρ(x))` (Densities.lean); with `ℝ≥0∞` division it
  equals Simon's three-case definition (3.9) (`outerRelativeUpperDensity_eq_piecewise`).
* `HasSymmetricVitaliProperty` (DensityCovering.lean): Def. 3.10 with balls as (centre, radius > 0) pairs, centred
  fine covers, countable disjoint subfamily covering `μ₀`-almost all of `A`.
* `IsRadonOuterMeasure` (RadonOuterMeasure.lean): literal (R1)–(R3) of Def. 4.6 for an outer measure.

Not used (per the brief): any non-clean SimonGMT definition.

## Notes / points of judgement

* Dimensions in §3 are real `n ≥ 0` (the book defines `ω_m`, `Hᵐ` for all real `m ≥ 0`); §2 results are for
  integer `n` as printed.
* 3.24: the book's integrand `Θ^{μ₀}(μ,x)` is only defined where the density exists; the contract integrates the
  everywhere-defined upper density and adds clause (0) stating the density exists and equals it `μ₀`-a.e.
  In (iii) the contract does not claim Borel measurability of `Z` (not asserted in the book; it is nevertheless proved in
  SimonGMT).
* 3.17 hypothesis is the book's literal one (global `μ`-measurability + finite `∫|f|` on some ball around each point),
  not Mathlib's `LocallyIntegrable`.
* 4.12 is stated with Mathlib's `ℝ≥0`-linear maps on `C_c(X, ℝ≥0)`, which is exactly additivity plus
  `λ(cf) = cλ(f)` for `c ≥ 0`.
* Radon measures in §4 are Simon outer measures satisfying (R1)–(R3); integrals use `caratheodoryMeasure`.
* Encoding check (scratch file outside the repo, not committed): `BorelRegularApproximation`, `LusinTheorem`,
  `LebesgueEqHausdorff`, `IsodiametricInequality`, `UpperDensityComparison`, `UpperDensityTheorem`,
  `BesicovitchCovering`, `HausdorffDensityBounds` and `RieszVector` were each proved in a few lines from the SimonGMT
  theorems listed above, which confirms that these statements match the existing ones. The rest need short bridges
  (1.13, 3.16, 3.17, 3.24, 4.12) or new mathematics (4.16 when `X` is not compact).
