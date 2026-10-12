<!-- theorem-id: gmt-ch01/root -->

# Final proof of `GMT.Ch01.main_theorem` (Simon, *Introduction to GMT*, Chapter 1)

| | |
| --- | --- |
| Node | `root` of run `20261011T134545Z-a770481ea2`; issue https://github.com/ZhengyangZhang06/gmt-formalize/issues/1 |
| Declaration | `GMT.Ch01.main_theorem` in `GMT/Ch01/Submission.lean` |
| Frozen problem | `GMT/Ch01/Contract.lean` at `ec1c322fab7585cea8deb6a95d4dae2d97d09d8e` (unchanged; byte-identical in the candidate) |
| Toolchain and libraries | Lean `v4.35.0-rc3`; Mathlib `25730c7c759d108ef87ab70af2342a196760f79d`; `simongmt` (`Poincare.SimonGMT.*`) `2b3663083f3fe399b6296fb8eaee52169170e197` |
| Axioms of `main_theorem` | `propext`, `Classical.choice`, `Quot.sound` only |
| Mathematical source | L. Simon, *Introduction to Geometric Measure Theory* (2014 Tsinghua notes), Ch. 1, printed pp. 1–38 |

## 0. Summary

`main_theorem` has no hypotheses. Its type is a conjunction of fifteen closed propositions, one for
each headline result of Chapter 1. The Lean proof is a single conjunction introduction: each
conjunct is supplied by an accepted child declaration. Three children supply two conjuncts each:
`lebesgue_eq_hausdorff_and_isodiametric`, `upper_density_comparison_and_theorem` and
`general_density_and_differentiation`. The other nine supply one conjunct each.
Section 2 explains this root step, including the only non-obvious point, which concerns universe
levels. Section 3 records how each child proves its conjunct, with every library theorem it uses
and that theorem's exact provenance. Section 4 lists the dependencies actually used, contrasts
them with the planned decomposition, and shows that there is no circularity. Section 6 describes
the changes made while implementing the root:
- a reordering of declarations in the Lean file (§6.1);
- in a later round, corrections to this prose only (§6.2).

Sections 5, 7 and 8 cover history, verification and the local-reference search.

## 1. The statement

`GMT/Ch01/Contract.lean` (frozen) defines the fifteen propositions together with the conventions
they use, and states:

```lean
theorem main_theorem : CaratheodoryCriterion ∧ BorelRegularApproximation ∧ LusinTheorem ∧
  LebesgueEqHausdorff ∧ IsodiametricInequality ∧ UpperDensityComparison ∧ UpperDensityTheorem ∧
  BesicovitchCovering ∧ GeneralDensityTheorem ∧ LebesgueDifferentiation ∧ RadonNikodymTheorem ∧
  HausdorffDensityBounds ∧ RieszPositive ∧ RieszVector ∧ RadonCompactness
```

The conventions are those of the book:
- A measure is an outer measure `μ : OuterMeasure X`.
- "μ-measurable" means Carathéodory measurable (`μ.IsCaratheodory`).
- "μ-a.e." means the exceptional set has outer measure `0`.
- Integrals are taken against `caratheodoryMeasure μ = μ.toMeasure` on the σ-algebra `μ.caratheodory`.
- `B_ρ(x)` is `closedBall x ρ`.

| # | Proposition | Simon, Ch. 1 |
| --- | --- | --- |
| 1 | `CaratheodoryCriterion` | Theorem 1.13, p. 6 |
| 2 | `BorelRegularApproximation` | Theorem 1.15, p. 7 |
| 3 | `LusinTheorem` | Theorem 1.17, p. 8 |
| 4 | `LebesgueEqHausdorff` | Theorem 2.9, p. 11 |
| 5 | `IsodiametricInequality` | Theorem 2.10, p. 11 |
| 6 | `UpperDensityComparison` | Theorem 3.3, p. 14 |
| 7 | `UpperDensityTheorem` | Theorem 3.6, p. 16 |
| 8 | `BesicovitchCovering` | Lemma 3.12, p. 18 |
| 9 | `GeneralDensityTheorem` | Theorem 3.16, p. 20 |
| 10 | `LebesgueDifferentiation` | Corollary 3.17, p. 20 |
| 11 | `RadonNikodymTheorem` | Theorem 3.24 with clause (0) from 3.23(ii), pp. 24–25 |
| 12 | `HausdorffDensityBounds` | Theorem 3.26, p. 26 |
| 13 | `RieszPositive` | Theorem 4.12, p. 33 |
| 14 | `RieszVector` | Theorem 4.14, p. 35 |
| 15 | `RadonCompactness` | Theorem 4.16, p. 37, **as corrected in the contract** |

**The 4.16 correction.** The contract adds second countability of `X` to the printed
hypotheses. As printed, the theorem is false (`Poincare.SimonGMT.Chapter01.simon_theorem_4_16_counterexample`,
`SequentialCompactnessCounterexample.lean:141`). The added hypothesis is the standing assumption the
book announces for §4: "X is a locally compact, separable metric space" (`book/chapter-01.txt`,
line 20). The correction is part of the frozen statement; the proof neither adds to nor removes
from it.

**Universe structure.** No universe is written explicitly in the statement. Each occurrence of a
universe-polymorphic proposition therefore receives its own universe parameter. Verified with
`set_option pp.universes true`, the elaborated type is:

```
main_theorem.{u_1, …, u_13} : CaratheodoryCriterion.{u_1} ∧ BorelRegularApproximation.{u_2} ∧
  LusinTheorem.{u_3} ∧ LebesgueEqHausdorff ∧ IsodiametricInequality ∧ UpperDensityComparison.{u_4} ∧
  UpperDensityTheorem.{u_5} ∧ BesicovitchCovering ∧ GeneralDensityTheorem.{u_6} ∧
  LebesgueDifferentiation.{u_7} ∧ RadonNikodymTheorem.{u_8} ∧ HausdorffDensityBounds.{u_9} ∧
  RieszPositive.{u_10} ∧ RieszVector.{u_11, u_12} ∧ RadonCompactness.{u_13}
```

The three Euclidean statements (4, 5, 8) quantify over `EuclideanSpace ℝ (Fin n) : Type` and carry
no universe parameter.

## 2. The root proof (the actual Lean argument)

```lean
theorem main_theorem : … := by
  exact ⟨Submission.caratheodory_criterion,
    Submission.borel_regular_approximation,
    Submission.lusin_theorem,
    Submission.lebesgue_eq_hausdorff_and_isodiametric.1,
    Submission.lebesgue_eq_hausdorff_and_isodiametric.2,
    Submission.upper_density_comparison_and_theorem.1,
    Submission.upper_density_comparison_and_theorem.2,
    Submission.besicovitch_covering,
    Submission.general_density_and_differentiation.1,
    Submission.general_density_and_differentiation.2,
    Submission.radon_nikodym_theorem,
    Submission.hausdorff_density_bounds,
    Submission.riesz_positive,
    Submission.riesz_vector,
    Submission.radon_compactness⟩
```

*Proof.* A conjunction is proved by proving each conjunct. The anonymous constructor builds the
right-nested `And.intro` from fifteen proof terms. The table gives the proof term for each conjunct
together with the child's accepted frozen type (from the workflow DAG).

| # | Proof term | Child's frozen type |
| --- | --- | --- |
| 1 | `Submission.caratheodory_criterion` | `CaratheodoryCriterion` |
| 2 | `Submission.borel_regular_approximation` | `BorelRegularApproximation` |
| 3 | `Submission.lusin_theorem` | `LusinTheorem` |
| 4, 5 | `Submission.lebesgue_eq_hausdorff_and_isodiametric.1`, `.2` | `LebesgueEqHausdorff ∧ IsodiametricInequality` |
| 6, 7 | `Submission.upper_density_comparison_and_theorem.1`, `.2` | `UpperDensityComparison.{u} ∧ UpperDensityTheorem.{u}` |
| 8 | `Submission.besicovitch_covering` | `BesicovitchCovering` |
| 9, 10 | `Submission.general_density_and_differentiation.1`, `.2` | `GeneralDensityTheorem.{u} ∧ LebesgueDifferentiation.{u}` |
| 11 | `Submission.radon_nikodym_theorem` | `RadonNikodymTheorem` |
| 12 | `Submission.hausdorff_density_bounds` | `HausdorffDensityBounds` |
| 13 | `Submission.riesz_positive` | `RieszPositive` |
| 14 | `Submission.riesz_vector` | `RieszVector` |
| 15 | `Submission.radon_compactness` | `RadonCompactness` |

Each proof term has the required type, for the following reasons.
- The child types other than the three pairs are syntactically the corresponding conjuncts.
- The pair `LebesgueEqHausdorff ∧ IsodiametricInequality` is universe-free, so its projections `.1`
  and `.2` are exactly conjuncts 4 and 5.
- The paired children 6/7 and 9/10 have one universe `u` shared by both halves, while the frozen
  type gives the halves independent universes (`u_4`, `u_5` and `u_6`, `u_7`). Each child is a
  universe-polymorphic theorem, so each occurrence is instantiated separately. The occurrence
  projected with `.1` is instantiated at `u := u_4` (resp. `u_6`), and the separate occurrence
  projected with `.2` at `u := u_5` (resp. `u_7`). This is why each half is projected from its own
  occurrence of the child, as the comment in the Lean proof explains.

The root uses no hypotheses, no other lemma and no tactic besides `exact`. ∎

## 3. Proofs of the conjuncts, as formalized by the accepted children

Each subsection gives the argument actually implemented in `GMT/Ch01/Submission.lean`. Library
theorems are cited by their full Lean name and a `file:line` location:
- `simongmt` locations are relative to `Poincare/SimonGMT/Chapter01/` in the pinned package.
- Mathlib locations are files of the pinned local snapshot, byte-identical to the build's package.

All of these are **existing pinned upstream declarations, reused, not new helpers**. The root
comparator builds the candidate and exports `GMT.Ch01.main_theorem` together with its dependency
closure. It re-checks that closure with Lean's default kernel, and restricts the axioms to
`propext`, `Quot.sound` and `Classical.choice`. The first run in §7.1 also used the independent
Nanoda kernel. The closure includes every Mathlib and `Poincare.SimonGMT` declaration the proof
depends on, so their reuse is verified in this run, not trusted.

Each library entry gives the statement used, followed by a short summary of the library's own
proof. The summary is for orientation only; the guarantee is the kernel-checked statement. Each
child also has an independently reviewed natural-language proof, recorded on its solution branch
(see §4.3).

### 3.1 Theorem 1.13 — `Submission.caratheodory_criterion : CaratheodoryCriterion`

**Claim.** Let `X` be a metric space and `μ` an outer measure with `μ(A ∪ B) = μ(A) + μ(B)`
whenever some real `r > 0` satisfies `r ≤ d(a, b)` for all `a ∈ A`, `b ∈ B`. Then every Borel set
is `μ`-measurable.

**Proof.**
1. Mathlib calls `μ` *metric* (`OuterMeasure.IsMetric`, `Mathlib/MeasureTheory/Measure/Hausdorff.lean:137`)
   if `μ(s ∪ t) = μ(s) + μ(t)` whenever `Metric.AreSeparated s t`. By definition
   (`Mathlib/Topology/MetricSpace/MetricSeparated.lean:99`), this means: there is an extended real
   `r ≠ 0` with `r ≤ edist(x, y)` for all `x ∈ s`, `y ∈ t`.
2. The hypothesis makes `μ` metric. Given such an `r`, the extended real `min(r, 1)` lies in
   `(0, 1]`, so the real number `ρ := min(r, 1)` satisfies `ρ > 0`.
3. For `a ∈ s` and `b ∈ t` we have `min(r, 1) ≤ r ≤ edist(a, b) = ENNReal.ofReal(dist(a, b))`.
   Since `dist(a, b) ≥ 0`, this gives `ρ ≤ dist(a, b)`. The hypothesis now gives
   `μ(s ∪ t) = μ(s) + μ(t)`.
4. Mathlib's Carathéodory theorem `OuterMeasure.IsMetric.borel_le_caratheodory` (`Hausdorff.lean:161`)
   says that a metric outer measure satisfies `borel X ≤ μ.caratheodory`. Its proof uses the classical
   shells argument for closed sets, which generate the Borel σ-algebra.
5. Hence every Borel `E` is `μ`-measurable. ∎

### 3.2 Theorem 1.15 — `Submission.borel_regular_approximation : BorelRegularApproximation`

**Claim.** Let `X` be a topological space in which every closed set is `G_δ`, and let `μ` be
Borel regular and open σ-finite. Then:
1. `μ(A) = inf{μ(U) : U ⊇ A open}` for every `A`.
2. `μ(A) = sup{μ(C) : C ⊆ A closed}` for every `μ`-measurable `A`.

**Proof.** This is the pinned theorem `IsBorelRegularOuterMeasure.simon_theorem_1_15`
(`ExactRegularity.lean:148`).
- Its hypotheses are `IsBorelRegularOuterMeasure μ`, `IsOpenSigmaFinite μ` and
  `ClosedSetsAreGDelta X`. The last is equivalent to the contract's hypothesis
  `∀ C, IsClosed C → IsGδ C` by `closedSetsAreGDelta_iff` (`ExactRegularity.lean:31`).
- Its conclusion is the same pair of formulas.

*Library proof.* The Borel measure `ν := hμ.toBorelMeasure` (Remark 1.11) agrees with `μ` on every
set by Borel regularity (`IsBorelRegularOuterMeasure.toBorelMeasure_apply_all`, `Basic.lean:285`).
- Each open set is an increasing union of closed sets, because its complement is `G_δ`.
- Each finite restriction `ν⌞V_j` to the open cover is therefore weakly regular.
- Outer regularity glues across the cover.
- (1) for arbitrary `A` then follows from a Borel hull of `A`.
- (2) follows from a Borel subset of `A` with null difference.

The printed proof (p. 7) packages the same ingredients differently. It runs a σ-algebra argument on
the class of Borel sets satisfying (1), uses that closed sets are `G_δ`, works on finite-measure
pieces, and uses Borel hulls. ∎

### 3.3 Theorem 1.17 (Lusin) — `Submission.lusin_theorem : LusinTheorem`

**Claim.** Let `X` be a topological space in which every closed set is `G_δ`, and let `μ` be
Borel regular. Let `A` be `μ`-measurable with `μ(A) < ∞`, let `f : A → ℝ` be measurable for the
trace on `A` of the `μ`-measurable sets, and let `ε > 0`. Then there is a closed `C ⊆ A` with
`μ(A \ C) < ε` and `f|_C` continuous.

The Lean proof follows the printed proof. It does not call the library's `simon_theorem_1_17`.
1. **Level sets.** Take the `μ`-measurable sets as the σ-algebra; Borel sets belong to it.
   - For `i ∈ ℕ` and `j ∈ ℤ`, put `L_{ij} := {a ∈ A : ⌊(i+1) f(a)⌋ = j}`.
   - `L_{ij}` is the image under the inclusion `A → X` of the measurable set
     `{a : (i+1) f(a) ∈ [j, j+1)}`. It is therefore `μ`-measurable: images of measurable subsets of
     a measurable subtype are measurable.
2. **Closed inner approximation inside `A`.**
   - *Setup.* By the remark after (1.12) (`IsBorelRegularOuterMeasure.restrict`, `Basic.lean:324`),
     `μ⌞A` is Borel regular, since `A` is measurable and `μ(A) < ∞`. It is finite, hence open
     σ-finite with the cover `V_n = X`.
   - *Approximation.* Let `E ⊆ A` be measurable. Then `E` is `μ⌞A`-measurable
     (`isCaratheodoryMeasurable_restrict`, `Basic.lean:43`). Theorem 1.15(2)
     (`Submission.borel_regular_approximation` applied to `μ⌞A`) gives
     `μ(E) = (μ⌞A)(E) = sup{μ(F) : F ⊆ E closed}`.
   - *Conclusion.* Let `η > 0`. If `μ(E) < η`, take `F = ∅`. Otherwise choose a closed `F ⊆ E`
     with `μ(F) > μ(E) − η`. Since `F` is Borel, hence measurable, `μ(E) = μ(F) + μ(E \ F)`. All
     values are finite, so `μ(E \ F) < η`.
3. **Weights.** Choose `δ_i > 0` with `Σ_i δ_i < ε` (Mathlib `ENNReal.exists_pos_sum_of_countable'`).
4. **A closed set on which the level function is locally constant.** Fix `i`.
   - Choose `η_j > 0` (`j ∈ ℤ`) with `Σ_j η_j < δ_i`, and closed `C_j ⊆ L_{ij}` with
     `μ(L_{ij} \ C_j) < η_j` (step 2).
   - The measurable sets `E_J := A \ ⋃_{|j| ≤ J} C_j` decrease in `J`.
   - Their intersection lies in `⋃_j (L_{ij} \ C_j)`. Indeed, a point `x` of the intersection lies
     in `L_{i j₀}` for `j₀ = ⌊(i+1) f(x)⌋` but not in `C_{j₀}`.
   - Hence `μ(⋂_J E_J) ≤ Σ_j η_j < δ_i`.
   - Let `μ̂ := μ.toMeasure` be the measure on the σ-algebra of `μ`-measurable sets. It agrees with
     `μ` on measurable sets (Mathlib `MeasureTheory.toMeasure_apply`). **`μ̂` need not be a finite
     measure**: only `μ(A) < ∞` is assumed. Continuity from above (Mathlib
     `tendsto_measure_iInter_atTop`) applies to a decreasing sequence of measurable sets as soon as
     one of them has finite measure. Here `E_0 ⊆ A`, so `μ̂(E_0) ≤ μ̂(A) = μ(A) < ∞`. Therefore
     `μ(E_J) = μ̂(E_J) → μ̂(⋂_J E_J) = μ(⋂_J E_J) < δ_i`, which gives a `J` with `μ(E_J) < δ_i`.
   - Put `D_i := ⋃_{|j| ≤ J} C_j`. It is closed, `D_i ⊆ A`, and `μ(A \ D_i) < δ_i`.
   - The `C_j` lie in the pairwise disjoint level sets. If `a ∈ C_{j₀} ⊆ D_i`, the open set
     `U := X \ ⋃_{|j| ≤ J, j ≠ j₀} C_j` contains `a`, and every `b ∈ D_i ∩ U` lies in `C_{j₀}`.
     Hence `⌊(i+1) f⌋` is constant on `D_i ∩ U`.
5. **The closed set.** Put `C := ⋂_i D_i`. It is closed, `C ⊆ A`, and
   `μ(A \ C) = μ(⋃_i (A \ D_i)) ≤ Σ_i μ(A \ D_i) ≤ Σ_i δ_i < ε`.
6. **Continuity.**
   - On `C`, the functions `g_i := ⌊(i+1) f⌋/(i+1)` are locally constant (step 4), hence continuous.
   - `|f − g_i| < 1/(i+1)` everywhere, so `g_i → f` uniformly.
   - A uniform limit of continuous functions is continuous (Mathlib `TendstoUniformly.continuous`),
     so `f ∘ inclusion` is continuous on `C`. ∎

### 3.4 Theorems 2.9 and 2.10 — `Submission.lebesgue_eq_hausdorff_and_isodiametric : LebesgueEqHausdorff ∧ IsodiametricInequality`

**Claims.** For `n ∈ ℕ`, real `δ > 0` and any `A ⊆ ℝⁿ`:
- (2.9) `Lⁿ(A) = Hⁿ(A) = Hⁿ_δ(A)`.
- (2.10) `Lⁿ(A) ≤ ω_n (diam A / 2)ⁿ`.

**Proof.**
- (2.9) is `simon_theorem_2_9 n (ENNReal.ofReal_pos.mpr hδ) A` (`EuclideanNormalization.lean:102`), used at
  the positive scale `ENNReal.ofReal δ`. Its `simonHausdorffOuterValue m A` is by definition
  `simonHausdorffOuterMeasureReal m A` (`Hausdorff.lean:276`).
- (2.10) is `simon_theorem_2_10 n A` (`EuclideanNormalization.lean:24`). Its exponent is the real
  number `(n : ℝ)`, which becomes the natural power `n` by `ENNReal.rpow_natCast`.

*Library proof.* (2.10) is proved by successive compact coordinate Steiner symmetrizations (the
printed proof). (2.9) follows from the sharp isodiametric inequality, which identifies the
Gamma-normalized content with Lebesgue measure at every positive scale. ∎

### 3.5 Theorems 3.3 and 3.6 — `Submission.upper_density_comparison_and_theorem : UpperDensityComparison.{u} ∧ UpperDensityTheorem.{u}`

**(3.3).** Let `μ` be Borel regular on a metric space `X`, let `n, t ≥ 0`, and let `A₁ ⊆ A₂`. If
`Θ^{*n}(μ, A₂, x) ≥ t` on `A₁`, then `t · Hⁿ(A₁) ≤ μ(A₂)`.

*Proof.* This is `simon_theorem_3_3` (`DensityComparison.lean:294`), whose statement is identical.

*Library proof.* Following the printed proof:
- restrict `μ` to `A₂`;
- for each `τ < t`, the five-times covering lemma with a finite-tail estimate bounds `Hⁿ(A₁)` by
  `μ(A₂)/τ`;
- take the supremum over `τ < t`. ∎

**(3.6).** If `μ` is Borel regular, `n ≥ 0`, and `A` is `μ`-measurable with `μ(A) < ∞`, then
`Θ^{*n}(μ, A, x) = 0` for `Hⁿ`-a.e. `x ∉ A`.

The Lean proof follows the printed proof.
1. `μ⌞A` is Borel regular (`IsBorelRegularOuterMeasure.restrict`) and finite, hence open σ-finite
   (`V_n = X`). In a metric space every closed set is `G_δ`. Theorem 1.15(2)
   (`Submission.borel_regular_approximation` for `μ⌞A`, with `A` being `μ⌞A`-measurable) and the same
   splitting argument as in step 2 of §3.3 give, for every `ε > 0`, a closed `C ⊆ A` with
   `μ(A \ C) < ε`.
2. Fix real `t > 0` and put `S_t := {x ∉ A : Θ^{*n}(μ, A, x) ≥ t}`, so `S_t ⊆ X \ C`. For
   `x ∈ S_t`, we have `x ∉ C` with `C` closed, so:
   - `Θ^{*n}(μ, A, x) = Θ^{*n}(μ, A \ C, x)` (`dimensionalUpperDensity_sdiff_of_isClosed`,
     `DensityComparison.lean:128`);
   - `Θ^{*n}(μ, A \ C, x) = Θ^{*n}(μ⌞A, X \ C, x)`, since `(μ⌞A)((X \ C) ∩ B) = μ((A \ C) ∩ B)`.
3. Theorem 3.3 for `μ⌞A`, with `A₁ = S_t` and `A₂ = X \ C`, gives
   `t · Hⁿ(S_t) ≤ (μ⌞A)(X \ C) = μ(A \ C) < ε`. Since `ε` is arbitrary, `t · Hⁿ(S_t) = 0`, so
   `Hⁿ(S_t) = 0`.
4. `{x ∉ A : Θ^{*n}(μ, A, x) ≠ 0} ⊆ ⋃_k S_{1/(k+1)}`, a countable union of `Hⁿ`-null sets. This is
   the a.e. statement. ∎

Here Theorem 3.3 is the first half proved in the same declaration. It is reused at the same
universe `u`, which is why the child's type shares `u`.

### 3.6 Lemma 3.12 (Besicovitch) — `Submission.besicovitch_covering : BesicovitchCovering`

**Claim.** For each `n` there is an `N` with the following property. If `B` is any family of
closed balls in `ℝⁿ` (pairs (centre, radius `> 0`)) with bounded radii, then there are `N`
pairwise-disjoint subfamilies of `B` whose balls cover all centres.

**Proof.**
1. Take `N := Besicovitch.multiplicity (EuclideanSpace ℝ (Fin n))` (Mathlib).
2. Apply `exists_besicovitchCovering_families` (`Densities.lean:631`) to the index type `↥B`, with
   centre `b.1`, radius `b.2 > 0`, and the bound `R` from `BddAbove`. It gives `D : Fin N → Set ↥B`
   such that each `D k` is pairwise disjoint for the closed balls and the centres lie in
   `⋃_k ⋃_{i ∈ D k} B_{r_i}(c_i)`.
3. Push each `D k` forward along the injective `Subtype.val`. Injectivity preserves pairwise
   disjointness, and the images are subsets of `B`.

*Library proof.* The library theorem wraps Mathlib's `Besicovitch.exist_disjoint_covering_families`
(`Mathlib/MeasureTheory/Covering/Besicovitch.lean:455`) with
`Besicovitch.isEmpty_satelliteConfig_multiplicity`. That theorem covers the centres by the open
balls; these are enlarged to closed balls. ∎

### 3.7 Theorem 3.16 and Corollary 3.17 — `Submission.general_density_and_differentiation : GeneralDensityTheorem.{u} ∧ LebesgueDifferentiation.{u}`

Let `μ` be Borel regular and open σ-finite, with the Symmetric Vitali Property, on a metric space
`X`.

**(3.16).** Let `A` be `μ`-measurable.

1. `simon_theorem_3_16` (`GeneralDensity.lean:102`) gives, for `hμ.toBorelMeasure`-a.e. `x`,
   ```
   μ(A ∩ B_ρ(x)) / μ(B_ρ(x)) → 1_A(x)   as ρ ↓ 0.
   ```
2. `hμ.toBorelMeasure` agrees with `μ` on **all** sets (`toBorelMeasure_apply_all`), so the
   exceptional set is `μ`-null. This is the outer-measure a.e. statement.
3. At `x ∈ A` the indicator is `1`, and at `x ∉ A` it is `0`. This gives both clauses.

*Library proof.* The general upper-density theorem for relative densities is localized by open
σ-finiteness. It uses the Symmetric Vitali Property, with no separability or doubling hypothesis. ∎

**(3.17).** Let `f` be `μ`-measurable, and suppose every `x` has some `ρ > 0` with
`∫_{B_ρ(x)} |f| dμ < ∞`. Then
`μ(B_ρ(x))⁻¹ ∫_{B_ρ(x)} f dμ → f(x)` for `μ`-a.e. `x`.

The library theorem `simon_corollary_3_17_of_caratheodory` (`GeneralDifferentiation.lean:304`) has
the same hypotheses and conclusion, except that both its integrals are taken against
`hμ.toBorelMeasure`. The child transports between the two measures.
1. **The trim.** On Borel sets, `caratheodoryMeasure μ` takes the value `μ(s)`, by Mathlib's
   `MeasureTheory.toMeasure_apply` since Borel sets are `μ`-measurable. So does `hμ.toBorelMeasure`. Hence the trim
   of `caratheodoryMeasure μ` to `borel X` equals `hμ.toBorelMeasure` (Mathlib `trim_measurableSet_eq`
   and `Measure.ext`).
2. **Measurability.** `f` is a.e.-measurable for `hμ.toBorelMeasure`
   (`IsBorelRegularOuterMeasure.aemeasurable_of_caratheodory`, `GeneralDifferentiation.lean:286`,
   which uses open σ-finiteness). Closed balls are Borel.
3. **Equal integrals.** For every closed ball, the integrals agree for the two measures:
   - for `ofReal |f|`, by Mathlib `setLIntegral_trim_ae`
     (`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:490`);
   - for `f`, by Mathlib `integral_trim_ae` and `restrict_trim`
     (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1332`, `Mathlib/MeasureTheory/Measure/Trim.lean:108`).
4. **Transport.** The local integrability hypothesis therefore transfers to the library's form. The
   library's conclusion transfers back, and its exceptional set is `μ`-null as in (3.16).

*Library proof.* Simon's level-set argument for nonnegative integrable `f`, which uses 3.16, is
extended to signed and then locally integrable `f` through a countable family of integrable balls. ∎

### 3.8 Theorem 3.24 — `Submission.radon_nikodym_theorem : RadonNikodymTheorem`

**Setting.** Let `μ, μ₀` be Borel regular and open σ-finite on a metric space, with `μ₀` having
the Symmetric Vitali Property. Write `Θ := outerRelativeUpperDensity μ μ₀`, which is
`limsup_{ρ↓0} μ(B_ρ(x))/μ₀(B_ρ(x))`.

**Bridge.** As in 3.7:
- The trim of `caratheodoryMeasure μ₀` to `borel X` is `hμ₀.toBorelMeasure`.
- `Θ` is a.e. equal to the Borel-measurable `rnDeriv` of the Borel measures
  (`ae_outerRelativeUpperDensity_eq_rnDeriv`, `RadonNikodymTheorem.lean:28`;
  Mathlib `Measure.measurable_rnDeriv`), so `Θ` is a.e.-measurable for the trim.
- Hence, for every Borel `A`, `∫_A Θ d(toBorelMeasure μ₀) = ∫_A Θ d(caratheodoryMeasure μ₀)`
  (Mathlib `setLIntegral_trim_ae`).

**The four clauses.**
- **(0)** `simon_theorem_3_23_ii` (`RadonNikodymDensity.lean:149`) gives a Borel `S` with
  `μ₀(S) = 0` such that the ratio converges to `Θ(x)` for every `x ∉ S`. The exceptional set of
  clause (0) is contained in `S`, so it is `μ₀`-null.
- **(i)** `simon_theorem_3_24_i` (`RadonNikodymTheorem.lean:39`) has the same absolute continuity
  hypothesis (on all subsets) and gives `μ(A) = ∫_A Θ d(toBorelMeasure μ₀)` for Borel `A`. The
  bridge finishes the clause.
- **(ii)** `simon_theorem_3_24_ii` (`RadonNikodymTheorem.lean:92`) gives a Borel `Z` with
  `μ₀(Z) = 0` and `μ(A) = ∫_A Θ d(toBorelMeasure μ₀) + (μ⌞Z)(A)`. Here `(μ⌞Z)(A) = μ(A ∩ Z) = μ(Z ∩ A)`,
  and the bridge finishes the clause.
- **(iii)** If `μ` also has the Symmetric Vitali Property, `simon_theorem_3_24_iii`
  (`RadonNikodymTheorem.lean:125`) gives the same decomposition for
  `Z = outerInfiniteDensitySet μ μ₀`, together with `μ₀(Z) = 0`. By definition
  (`RadonNikodymTheorem.lean:107`), `Z` is literally `{x : μ(B_ρ(x))/μ₀(B_ρ(x)) → ∞ as ρ ↓ 0}`, the
  set in the contract.

*Library proof.* Following Simon (3.22)–(3.24), the density quotient converges to the
Radon–Nikodym derivative of the Borel measures `μ₀`-a.e. This uses the nonnegative form of 3.17
and the vanishing density of the singular part. ∎

### 3.9 Theorem 3.26 — `Submission.hausdorff_density_bounds : HausdorffDensityBounds`

Let `X` be a metric space, `n ≥ 0`, and `A` an `Hⁿ`-measurable set.

**(1)** If `Hⁿ(A) < ∞`, then `Θ^{*n}(Hⁿ, A, x) ≤ 1` for `Hⁿ`-a.e. `x ∈ A`.

1. **`Hⁿ` is Borel regular.**
   - `Hⁿ` is additive on positively separated sets: by `simonHausdorffOuterMeasureReal_isMetric`
     (`Hausdorff.lean:462`), a real separation `r > 0` gives `Metric.AreSeparated` with constant
     `ofReal r ≠ 0`.
   - Theorem 1.13 (`Submission.caratheodory_criterion`) therefore makes every Borel set
     `Hⁿ`-measurable.
   - Equal-measure Borel hulls exist (`simonHausdorffOuterMeasureReal_isBorelRegular`,
     `Hausdorff.lean:491`, (2.6)).
2. **The restriction `σ := Hⁿ⌞A`.**
   - It is Borel regular (`IsBorelRegularOuterMeasure.restrict`) and finite, hence open σ-finite.
   - For `S ⊆ A`, `Θ^{*n}(σ, S, x) = Θ^{*n}(Hⁿ, S, x)`.
3. **Level sets above 1 are null.** Let `t > 1` and `E ⊆ A` with `Θ^{*n}(Hⁿ, A, x) ≥ t` on `E`.
   1. Fix an open `U ⊇ E`. For `x ∈ E`, `U` is a neighbourhood of `x`, so
      `Θ^{*n}(σ, A ∩ U, x) = Θ^{*n}(Hⁿ, A ∩ U, x) = Θ^{*n}(Hⁿ, A, x) ≥ t`
      (`dimensionalUpperDensity_inter_of_mem_nhds`, `DensityComparison.lean:114`).
   2. Theorem 3.3 (`Submission.upper_density_comparison_and_theorem.1`) for `σ`, with `A₁ = E` and
      `A₂ = A ∩ U`, gives `t · Hⁿ(E) ≤ σ(A ∩ U) ≤ σ(U)`.
   3. Taking the infimum over `U` and using Theorem 1.15(1) for `σ` (`Submission.borel_regular_approximation`;
      closed sets are `G_δ` in metric spaces): `t · Hⁿ(E) ≤ σ(E) = Hⁿ(E)`.
   4. Since `Hⁿ(E) ≤ Hⁿ(A) < ∞` and `t > 1`, this forces `Hⁿ(E) = 0`.
4. **Conclusion.** `{x ∈ A : Θ^{*n}(Hⁿ, A, x) > 1} ⊆ ⋃_{q ∈ ℚ, q > 1} {x ∈ A : Θ^{*n} ≥ q}`
   (Mathlib `ENNReal.lt_iff_exists_rat_btwn`). This is a countable union of null sets. ∎

**(2)** If `Hⁿ_δ(A) < ∞` for every real `δ > 0`, then `Θ^{*n}(Hⁿ_∞, A, x) ≥ 2^{−n}` for `Hⁿ`-a.e.
`x ∈ A`.

*Proof.* `simon_theorem_3_26_ii` (`HausdorffContentDensity.lean:251`) gives
`Hⁿ{x ∈ A : Θ^{*n}(Hⁿ_∞, A, x) < 2^{−n}} = 0`. Here `simonHausdorffContent` unfolds to
`simonHausdorffContentOuter`, so the hypotheses match. This null-set form is the a.e. statement.

*Library proof.* The printed covering argument at infinite scale, completed; the child's reviewed
prose gives the details (§4.3). As the library notes, it does not use measurability of `A`. ∎

### 3.10 Theorem 4.12 — `Submission.riesz_positive : RieszPositive`

**Claim.** Let `X` be locally compact Hausdorff and `Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0`. Then there is
a Radon `μ` with `Λ f = ∫ f dμ` for all `f`.

**Proof.** Give `X` its Borel σ-algebra.
1. Mathlib's Riesz–Markov–Kakutani measure `NNRealRMK.rieszMeasure Λ` is regular (instance
   `NNRealRMK.rieszMeasure_regular`, `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean:66`).
2. It satisfies `∫ f d(rieszMeasure Λ) = Λ f` (`NNRealRMK.integral_rieszMeasure`, `NNReal.lean:47`).
3. Its outer measure is Radon in Simon's sense (`isRadonOuterMeasure_toOuterMeasure`,
   `RadonOuterMeasure.lean:60`, for a regular Borel measure on a Hausdorff space).
4. The contract's `caratheodoryMeasure` of that outer measure is definitionally
   `radonCaratheodoryMeasure (rieszMeasure Λ)`.
5. Continuous `f` is strongly measurable, so its Carathéodory integral equals its Borel integral
   (`integral_radonCaratheodoryMeasure`, `RadonCaratheodoryIntegral.lean:62`). ∎

### 3.11 Theorem 4.14 — `Submission.riesz_vector : RieszVector`

**Claim.** Let `X` be locally compact Hausdorff, `H` a finite-dimensional real inner product
space, and `L : C_c(X, H) →ₗ[ℝ] ℝ` bounded above on `{|f| ≤ 1, spt f ⊆ K}` for each compact `K`.
Then there are a Radon `μ` and a `μ`-measurable `ν` with `|ν| = 1` `μ`-a.e. and
`L f = ∫ ⟨f, ν⟩ dμ`.

**Proof.** Apply `simon_theorem_4_14 L hL` (`RadonPolarRepresentation.lean:206`).
- Its hypothesis `IsLocallyBoundedCcFunctional L` unfolds to the contract's hypothesis.
- Its measure `hμ.toCaratheodoryMeasure` is definitionally `caratheodoryMeasure μ`.
- Its unit-norm clause holds a.e. for that measure. That measure agrees with `μ` on every set
  (`IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all`, `RadonOuterMeasure.lean:246`), so the
  exceptional set is `μ`-null.

*Library proof.* `simon_theorem_4_14` gives `X` and `H` their Borel σ-algebras. It follows Simon's
proof (pp. 36–37) with two changes, which avoid any σ-finiteness or countability hypothesis on
`X`:
- the printed proof's `L¹(μ)` duality is applied on compact pieces, and the results are glued
  (step 3);
- a final modification turns unit norm on each compact set into the global clause (step 5).

File names below are in `Poincare/SimonGMT/Chapter01/`. Line numbers without a file name refer to
`RadonPolarRepresentation.lean`.
1. **Envelope measure.** The positive envelope is `λ(f) = sup{L(ω) : |ω| ≤ f}` on
   `C_c(X, ℝ≥0)`. Mathlib's real Riesz–Markov–Kakutani theorem represents `λ` by a regular Borel
   measure `μ₀ := vectorFunctionalEnvelopeMeasure L hL` (`VectorFunctionalEnvelope.lean:270`).
   - The equality (†) of p. 36, `λ(f) = ∫ f dμ₀`, is `simon_theorem_4_14_positive_envelope`
     (`VectorFunctionalEnvelope.lean:280`).
   - The Radon witness `μ` is the outer measure of `μ₀` (`vectorFunctionalEnvelopeMeasure_isRadon`,
     `VectorFunctionalEnvelope.lean:290`). Write `μ̄` for its Carathéodory measure, which is
     `caratheodoryMeasure μ` in the contract. `μ̄` is regular
     (`IsRadonOuterMeasure.toCaratheodoryMeasure_regular`, `RadonOuterMeasure.lean:260`).
   - `|L ω| ≤ ∫ |ω| dμ₀` (`VectorFunctionalEnvelope.lean:311`).
2. **`L¹` extension.** `C_c(X, H)` is dense in `L¹(μ₀; H)`, so `L` extends to `L̄` on
   `L¹(μ₀; H)` with `‖L̄‖ ≤ 1` (`simon_theorem_4_14_l1_extension`, `VectorFunctionalL1.lean:147`).
3. **A field bounded by one.**
   - For each compact `C`, the restriction `μ₀⌞C` is finite. Riesz representation on
     `L²(μ₀⌞C; H)` gives a Borel field `ν_C` with `|ν_C(x)| ≤ 1` for every `x`. It represents `L̄`
     on functions supported in `C`, extended by zero (`LocalFiniteL1Dual.lean:101`).
   - These fields are glued along a maximal family of pairwise almost-disjoint compact sets of
     positive measure (`RadonCompactDecomposition.lean:179`, `RadonFieldGluing.lean:262`). The
     supports of only countably many members meet a given compact set. The supports of the
     members cover each compact set up to a null set.
   - The glued field `ν` is measurable for the full Carathéodory σ-algebra. This uses the fact
     that a set is `μ`-measurable as soon as its intersection with every compact set is
     (`RadonLocalMeasurability.lean:28`).
   - `|ν(x)| ≤ 1` for every `x`, and `ν = ν_C` almost everywhere on every compact `C`
     (`RadonLocalDualField.lean:64`).
   - Every test function vanishes off a compact set. Hence `L f = ∫ ⟨f, ν⟩ dμ̄` for all
     `f ∈ C_c(X, H)` (`exists_radon_caratheodory_L1_dual_field`,
     `RadonCaratheodoryIntegral.lean:135`, used by `simon_theorem_4_14_bounded_caratheodory`,
     line 135).
4. **Unit norm on each compact set** (`norm_eq_one_on_compact_of_measure_envelope`, line 34). Let
   `K` be compact.
   1. Urysohn's lemma gives `f ∈ C_c(X, ℝ≥0)` with `f = 1` on `K`.
   2. Every `ω` with `|ω| ≤ f` satisfies `L ω = ∫ ⟨ω, ν⟩ dμ̄ ≤ ∫ f |ν| dμ̄`. Taking the supremum
      over `ω` gives `∫ f dμ̄ = λ(f) ≤ ∫ f |ν| dμ̄`.
   3. Since `|ν| ≤ 1`, also `∫ f |ν| dμ̄ ≤ ∫ f dμ̄`. Hence `f |ν| = f` `μ̄`-a.e., so `|ν| = 1`
      `μ̄`-a.e. on `K`.

   This is a separate statement for each compact `K`. `X` need not be σ-compact and `μ̄` need
   not be σ-finite, so it does **not** by itself give `|ν| = 1` `μ̄`-a.e. on `X`.
5. **Global unit norm** (lines 180–198). The two cases are as follows.
   - *`H ≠ {0}`.* Fix a unit vector `e ∈ H`. Put `η(x) := ν(x)` where `|ν(x)| = 1`, and
     `η(x) := e` elsewhere (`exists_unit_modification_on_compacts`, line 104).
     - The set `{|ν| = 1}` is measurable, so `η` is measurable for the Carathéodory σ-algebra.
     - `|η(x)| = 1` for **every** `x`. So the unit-norm clause holds everywhere, and in
       particular `μ̄`-a.e. No global null set is involved.
     - By step 4, `η = ν` `μ̄`-a.e. on every compact set. Every `f ∈ C_c(X, H)` vanishes off the
       compact set `spt f`. Hence `∫ ⟨f, η⟩ dμ̄ = ∫ ⟨f, ν⟩ dμ̄ = L f`
       (`integral_inner_eq_of_ae_eq_on_compacts`, line 87).
     - The library returns `η`.
   - *`H = {0}`.* No unit vector exists.
     - Here `|ν(x)| = 0` for every `x`, so step 4 gives `μ̄(K) = 0` for every compact `K`.
     - `μ̄` is inner regular on the open set `X`, so `μ̄(X) = 0`, that is, `μ̄ = 0`.
     - The unit-norm clause therefore holds vacuously, and the library returns `ν` unchanged.

The child's adapter, above, then passes from `μ̄`-a.e. to `μ`-a.e. ∎

### 3.12 Theorem 4.16 (corrected) — `Submission.radon_compactness : RadonCompactness`

**Claim.** Let `X` be locally compact, Hausdorff and second countable, and let `(μ_k)` be Radon
with `sup_k μ_k(K) < ∞` for each compact `K`. Then some subsequence satisfies
`∫ f dμ_{φ(k)} → ∫ f dμ` for all `f ∈ C_c(X, ℝ)`, for some Radon `μ`.

The proof uses six accepted grandchildren and follows the printed proof on p. 37: compact
exhaustion, a diagonal subsequence, then Theorem 4.12. The Alaoglu step, which yields only a subnet,
is replaced by an explicit countable-dense-family argument. That argument is where second
countability is needed. The "Step" numbers in the Lean docstrings refer to the child's reviewed
proof, not to the book. Here `∫` denotes integration against `caratheodoryMeasure`.

- **`Submission.rc_cc_countable_dense`.** For compact `K` in a Hausdorff second-countable `X`, there
  is a countable family `D` of test functions supported in `K` that is uniformly dense among test
  functions supported in `K`.
  1. `K` is compact Hausdorff and second countable. It embeds in `ℓ^∞` (Mathlib
     `TopologicalSpace.exists_embedding_l_infty`, `Mathlib/Topology/Metrizable/Urysohn.lean:121`).
  2. The coordinates `h_n` separate the points of `K`. By Stone–Weierstrass
     (`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`,
     `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean:264`), the algebra they generate is dense
     in `C(K, ℝ)`.
  3. That algebra is the `ℝ`-span of the countable monoid generated by `{h_n}`. So `C(K, ℝ)` is
     separable.
  4. The restrictions to `K` of the test functions supported in `K` therefore have a countable
     dense subset, and it lifts to `D`.
  5. Off `K`, both functions vanish.
- **`Submission.rc_cc_integrable`.** Every `f ∈ C_c(X, ℝ)` is integrable for the Carathéodory measure
  of a Radon `μ`.
  - Open sets are `μ`-measurable, and the measure is finite on compacts (it agrees with `μ` on all
    sets).
  - Mathlib `Continuous.integrable_of_hasCompactSupport` (`Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:622`)
    concludes.
- **`Submission.rc_cc_integral_abs_le`.** If `|f| ≤ C`, then `|∫ f dμ| ≤ μ(spt f) · C`.
  - `f` vanishes off `spt f` (Mathlib `setIntegral_tsupport`).
  - `spt f` is compact, so it has finite measure.
  - Mathlib `norm_setIntegral_le_of_norm_le_const` (`Mathlib/MeasureTheory/Integral/Bochner/Set.lean:613`) concludes.
- **`Submission.rc_diagonal_subseq`.** Countably many bounded real sequences `k ↦ a_k(i)` have a
  common convergent subsequence.
  - The box `∏_i [−C_i, C_i]` is compact (Tychonoff, Mathlib `isCompact_univ_pi`).
  - `ι → ℝ` is first countable for countable `ι`, so `IsCompact.tendsto_subseq`
    (`Mathlib/Topology/Sequences.lean:298`) gives a subsequence converging in the product topology,
    that is, coordinatewise.
- **`Submission.rc_subseq_integrals_converge`.** There is one subsequence `φ` along which `∫ f dμ_{φ(k)}`
  converges for every `f`.
  1. `X` is σ-compact. Take a compact exhaustion `K_j` (Mathlib `CompactExhaustion.choice`) and put
     `M_j := sup_k μ_k(K_j) < ∞`.
  2. Let `D_j` be the families from `rc_cc_countable_dense` for `K_j`, and `DD := ⋃_j D_j`, which is
     countable.
  3. For `g ∈ D_j` with `|g| ≤ C`, `|∫ g dμ_k| ≤ M_j·|C|` (`rc_cc_integral_abs_le`).
  4. `rc_diagonal_subseq` gives `φ` with `∫ g dμ_{φ(k)}` convergent for every `g ∈ DD`.
  5. For general `f`, choose `j` with `spt f ⊆ K_j`, then `η > 0` with `M_j η < ε/3`, and `g ∈ D_j`
     with `|f − g| ≤ η`. Then `|∫ f dμ_k − ∫ g dμ_k| = |∫ (f − g) dμ_k| ≤ M_j η < ε/3`, using
     `rc_cc_integrable`, `rc_cc_integral_abs_le` and `spt(f−g) ⊆ K_j`.
  6. An `ε/3` argument makes `∫ f dμ_{φ(k)}` Cauchy, hence convergent.
- **`Submission.rc_riesz_real`.** Assume Theorem 4.12 (`RieszPositive`). Then every positive linear
  `Λ : C_c(X, ℝ) → ℝ` is integration against a Radon measure.
  1. Restrict `Λ` to `C_c(X, ℝ≥0)` as the `ℝ≥0`-linear map
     `toNNRealLinear (PositiveLinearMap.mk₀ Λ hΛ)` (Mathlib,
     `Mathlib/Topology/ContinuousMap/CompactlySupported.lean:775`,
     `Mathlib/Algebra/Order/Module/PositiveLinearMap.lean:206`).
  2. 4.12 represents this restriction by a Radon `μ`.
  3. Write `f = f⁺ − f⁻` (`nnrealPart_sub_nnrealPart_neg`). Both parts are integrable
     (`rc_cc_integrable`), so `Λ f = ∫ f⁺ − ∫ f⁻ = ∫ f`.
- **Assembly (`Submission.radon_compactness`).**
  1. Let `φ` and the limits `l(f)` come from `rc_subseq_integrals_converge`.
  2. `F(f) := l(f)` is `ℝ`-linear. This follows from uniqueness of limits and linearity of the
     integral, with integrability from `rc_cc_integrable`.
  3. `F` is positive, as a limit of nonnegative integrals.
  4. `rc_riesz_real`, applied to `Submission.riesz_positive`, gives a Radon `μ` with
     `F(f) = ∫ f dμ`.
  5. Hence `∫ f dμ_{φ(k)} → F(f) = ∫ f dμ`. ∎

## 4. Dependencies, provenance and absence of circularity

### 4.1 Declarations actually referenced by the Lean proofs

Obtained by scanning each proof body of the candidate `Submission.lean` for `Submission.*`.

| Declaration | `Submission.*` declarations it references |
| --- | --- |
| `caratheodory_criterion`, `borel_regular_approximation`, `lebesgue_eq_hausdorff_and_isodiametric`, `besicovitch_covering`, `general_density_and_differentiation`, `radon_nikodym_theorem`, `riesz_positive`, `riesz_vector`, `rc_cc_countable_dense`, `rc_cc_integrable`, `rc_cc_integral_abs_le`, `rc_diagonal_subseq` | none |
| `lusin_theorem` | `borel_regular_approximation` |
| `upper_density_comparison_and_theorem` | `borel_regular_approximation` |
| `hausdorff_density_bounds` | `caratheodory_criterion`, `borel_regular_approximation`, `upper_density_comparison_and_theorem` |
| `rc_subseq_integrals_converge` | `rc_cc_countable_dense`, `rc_cc_integrable`, `rc_cc_integral_abs_le`, `rc_diagonal_subseq` |
| `rc_riesz_real` | `rc_cc_integrable` (and takes `RieszPositive` as an explicit hypothesis) |
| `radon_compactness` | `rc_subseq_integrals_converge`, `rc_cc_integrable`, `rc_riesz_real`, `riesz_positive` |
| `main_theorem` | the twelve root children of §2 |

**No circularity.**
- Lean elaborates `Submission.lean` top to bottom, and a declaration can mention only declarations
  that precede it. The candidate's order is therefore a topological order of the graph above:
  `caratheodory_criterion`, `borel_regular_approximation`, `lusin_theorem`,
  `lebesgue_eq_hausdorff_and_isodiametric`, `upper_density_comparison_and_theorem`,
  `besicovitch_covering`, `general_density_and_differentiation`, `radon_nikodym_theorem`,
  `hausdorff_density_bounds`, `riesz_positive`, `riesz_vector`, the six `rc_*` grandchildren,
  `radon_compactness`, and finally `main_theorem`.
- The libraries (Mathlib, `simongmt`) are upstream packages pinned before this problem existed.
  They cannot refer to any `GMT.Ch01` declaration.
- The 4.16 counterexample is only cited, in a docstring. It is not used.

### 4.2 Historical decomposition versus what is actually used

The accepted decomposition (`nodes/root/decomposition-v1.json`) dispatched twelve children. Its
child `root.radon_compactness-a1` was decomposed further into six grandchildren. All 18 nodes are
`accepted`, and all are used in the current Lean proof.

The DAG also declared planning-level prerequisites that the final Lean proofs do **not** use:
- `general_density_and_differentiation` → `borel_regular_approximation`, and
  `radon_nikodym_theorem` → `borel_regular_approximation`. The formal proofs go through the
  `simongmt` theorems of §3.7–3.8 instead.
- `riesz_vector` → `riesz_positive`. The formal proof applies `simon_theorem_4_14` directly.

These edges are historical only and create no logical dependency. The remaining declared
prerequisites are genuinely used:
- `lusin_theorem` → `borel_regular_approximation` (§3.3);
- `upper_density_comparison_and_theorem` → `borel_regular_approximation` (§3.5);
- `hausdorff_density_bounds` → `caratheodory_criterion`, `borel_regular_approximation` and
  `upper_density_comparison_and_theorem` (§3.9);
- `radon_compactness` → `riesz_positive` (§3.12);
- `rc_riesz_real` → `rc_cc_integrable`;
- `rc_subseq_integrals_converge` → its four sibling prerequisites (§3.12).

### 4.3 Child records

The reviewed natural-language proof of each child is in `proofs/github/20261011t134545z-a770481ea2/<record>/proof.md`
on branch `proof-workspace/gmt-ch01/20261011t134545z-a770481ea2/theorems/solutions/<record>`.

| Child (`Submission.*`) | Issue | Solution PR | Record |
| --- | --- | --- | --- |
| `caratheodory_criterion` | #9 | #152 | `root-caratheodory-criterion-a1-61420aa843` |
| `borel_regular_approximation` | #10 | #173 | `root-borel-regular-approximation-a1-ed6b9292ac` |
| `lusin_theorem` | #11 | #344 | `root-lusin-theorem-a1-548a77c914` |
| `lebesgue_eq_hausdorff_and_isodiametric` | #12 | #89 | `root-lebesgue-eq-hausdorff-and-isodiametric-a1-c91091aab6` |
| `upper_density_comparison_and_theorem` | #13 | #800 | `root-upper-density-comparison-and-theorem-a1-4c23ab6853` |
| `besicovitch_covering` | #14 | #142 | `root-besicovitch-covering-a1-6881bf6f47` |
| `general_density_and_differentiation` | #15 | #721 | `root-general-density-and-differentiation-a1-4350d0d7f0` |
| `radon_nikodym_theorem` | #16 | #286 | `root-radon-nikodym-theorem-a1-4f0c1240c9` |
| `hausdorff_density_bounds` | #17 | #978 | `root-hausdorff-density-bounds-a1-f75e5cf0b3` |
| `riesz_positive` | #18 | #179 | `root-riesz-positive-a1-1631abc604` |
| `riesz_vector` | #19 | #282 | `root-riesz-vector-a1-6826402e64` |
| `radon_compactness` | #20 | #480 | `root-radon-compactness-a1-818e789d32` |
| `rc_cc_integrable` | #80 | #249 | `root-radon-compactness-a1-rc-cc-integrable-a1-6ef647103e` |
| `rc_cc_integral_abs_le` | #81 | #211 | `root-radon-compactness-a1-rc-cc-integral-abs-le-a1-5478b21fcf` |
| `rc_diagonal_subseq` | #82 | #222 | `root-radon-compactness-a1-rc-diagonal-subseq-a1-237322879e` |
| `rc_cc_countable_dense` | #83 | #251 | `root-radon-compactness-a1-rc-cc-countable-dense-a1-e671336dcd` |
| `rc_subseq_integrals_converge` | #84 | #392 | `root-radon-compactness-a1-rc-subseq-integrals-converge-a1-1dfa9a8b24` |
| `rc_riesz_real` | #85 | #312 | `root-radon-compactness-a1-rc-riesz-real-a1-73a3a5acda` |

## 5. History (preserved, not rewritten)

The following records are left untouched under
`.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/nodes/root/`:
- **The original plan scaffold.** `plan-draft-v1.md`, `plan-v1.md` and `plan-source.md`.
- **The accepted natural-language source.** `natural-proof-source.md`: "follow the published proof
  of each conjunct" in `book/sources/chapter-01-source.txt`, sha256 `290b42af…38ed`.
- **The agent-authored root prose.** Drafts `natural-proof-draft-v1.md` and `natural-proof-draft-v2.md`.
  Version `natural-proof-v2.md` was accepted by `natural-review-receipt-v1.json`; the earlier
  feedback is in `natural-feedback-v1.txt` and the audit in `natural-audit-v2.json`.
- **The decomposition.** `decomposition-v1.json`, with its review receipt and audit.

The final Lean route agrees with that outline, with these refinements:
- Conjuncts 1–14 are adapters to kernel-checked `simongmt`/Mathlib theorems, or printed-proof
  formalizations in the cases of 3.6, 3.26(1) and Lusin.
- The corrected 4.16 received a new proof through the six grandchildren.

The speculative root draft `5c877e9` wrote the present `main_theorem` body.

## 6. Changes made while implementing the root

### 6.1 Lean: the declaration-order repair (commit `81b1eaa`)

**The failure.** The comparator rejected the previous candidate `a7bfaca`. Its evidence is in
`cluster-state/verification/results/hoa34/20261012T011631Z-ch01-root-dycwe_uh/`, with
`status: failed` and the error at line 987 of `comparator.log`:

```
GMT/Ch01/Submission.lean:962:4: error: Unknown identifier `Submission.hausdorff_density_bounds`
```

**The cause.** The accepted child `root.hausdorff_density_bounds-a1` was composed (commit `20bf434`)
while `main_theorem` was still `sorry`, and it appended its declaration *after* `main_theorem`. When
that child and the speculative root draft were overlaid, `main_theorem` referred to a declaration
that is elaborated later.

**The fix (commit `81b1eaa`).** The child's docstring and theorem, a 73-line block, were moved
verbatim to directly after `def HausdorffDensityBounds`. That is where every other child sits, and
`main_theorem` stays the last declaration, as in the contract. Checks on the moved text:
- The moved block is byte-identical to the block in the child's own commit `20bf434`.
- The `main_theorem` text is byte-identical to that of `a7bfaca`.
- The diff is a pure move: 74 lines added and 74 removed, the same multiset of lines.

No statement, definition, import or proof text changed.

An earlier version of this prose cited the run-directory log `nodes/root/comparator-v1.log` for this
failure. The controller has since overwritten that file with its later, passing run on `d0b46c7`.
The evidence directory above is the permanent record.

### 6.2 Prose only: corrections after the publication-prose audit

The controller reviewed the previous version of this file and did not accept it. That version is
blob `ae163c100a3fa0915c57c1d43215f8a95a56cdbf` at commit `d0b46c7`; the review is recorded in
`nodes/root/publication-prose-audit-v1.json`, which is left untouched. The audit raised four
issues, and this revision addresses each of them.

`GMT/Ch01/Submission.lean` is unchanged by this revision: it is byte-identical to `81b1eaa`, with
sha256 `518ee03c00e7332a9fc79d2d640a80bb59c528ff903e137a76e81e2ae3db48bf`.

| # | Audit issue | Change in this revision |
| --- | --- | --- |
| 1 | §3.11 did not explain how unit norm on each compact set yields the global a.e. clause. | The library-proof summary in §3.11 now spells this out. Step 4 proves unit norm `μ̄`-a.e. on each compact set separately, and notes that this alone does not give a global statement. Step 5 replaces non-unit values by a fixed unit vector `e`, which keeps agreement on compact sets and hence every test-function integral. It also treats the case `H = {0}` separately (`RadonPolarRepresentation.lean:104`, lines 180–198). |
| 2 | §3.3 step 4 called `μ.toMeasure` a finite measure. | Step 4 now uses continuity from above for `μ̂ = μ.toMeasure`. This needs only `μ̂(E_0) ≤ μ(A) < ∞`, and the text states that `μ̂` need not be finite. Step 5's estimate now reads `≤ Σ_i δ_i < ε`, as in the Lean proof. |
| 3 | §0 said that two children supply two conjuncts each. | §0 now says three and names them, as §2 does. |
| 4 | §8 named `OuterMeasure.toMeasure_apply`. | §8 now names `MeasureTheory.toMeasure_apply`, the declaration at `Mathlib/MeasureTheory/Measure/OuterMeasure.lean:46` inside `namespace MeasureTheory`. §3.3 and §3.7 use the same name. |

While re-checking the whole file against the pinned sources, two further corrections were made:
- the failure citation in §6.1, described above;
- the page range of Simon's proof of 4.14, which is pp. 36–37 (the statement is on p. 35).

All `file:line` citations in §3 were re-checked against the pinned `simongmt` package and the
snapshot's Mathlib.

## 7. Verification by the author

All checks used the pinned toolchain and the shared package tree.
1. **Compilation.** `lean GMT/Ch01/Submission.lean` succeeds with no errors and no warnings in the
   file.
2. **Axioms.** `#print axioms GMT.Ch01.main_theorem` reports `[propext, Classical.choice, Quot.sound]`;
   so does `#print axioms GMT.Ch01.Submission.hausdorff_density_bounds`.
3. **Child interfaces preserved.** For each of the 18 accepted DAG nodes, the frozen `lean_statement`
   was re-elaborated in the contract scope, as the child comparator does:
   `namespace GMT.Ch01`, the contract's `open` lines, and `universe u v`. Each was proved by
   `exact Submission.<lean_name>`. All 18 type-check, each with only the three standard axioms.
4. **Overlay hygiene.**
   - One `namespace GMT.Ch01` / `end GMT.Ch01` and one `universe u v`.
   - No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `implemented_by`, `extern` or `native_decide`.
   - No duplicate declaration names.
   - The contract's header (imports, module docstring, `open`s), all 16 definition blocks and the
     `main_theorem` statement line occur verbatim, exactly once.
   - `Contract.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and `GMT.lean` are
     byte-identical to the frozen commit.
5. **Comparator.** The exact configured command was run on the committed candidate; its result is
   recorded in §7.1.

**Re-run in the §6.2 round.** `GMT/Ch01/Submission.lean` was unchanged (sha256 `518ee03c…48bf`).
Items 1–4 were nevertheless repeated on 2026-10-12.
- A scratch file outside the repository held the whole of `Submission.lean`, followed by one theorem
  for each of the 18 accepted DAG nodes. Each theorem states the node's frozen `lean_statement`,
  taken verbatim from `dag.json`. The theorems sit in `namespace GMT.Ch01.InterfaceCheck`, under the
  contract's `open` lines and `universe u v`. That namespace is nested in `GMT.Ch01`, so names resolve
  as in the contract scope. Each theorem is proved by `exact Submission.<lean_name>`.
- `lake env lean` with the pinned toolchain compiled it with exit status 0 and no errors or warnings.
- `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for `GMT.Ch01.main_theorem` and
  for all 18 interface theorems.
- The text checks of item 4 were repeated with the same results:
  - the contract header is identical;
  - each of the 37 blank-line-separated contract blocks occurs exactly once;
  - there is one `main_theorem`, no forbidden token and no duplicate name;
  - the five build inputs are identical to `ec1c322`.

### 7.1 Comparator result

The exact configured command (`verifier/gmt-compare.py --lean-target GMT/Ch01/Submission.lean …
--frozen-commit ec1c322fab7585cea8deb6a95d4dae2d97d09d8e root`, with the configured `HUMANIZE_*`
environment) **passed twice**. Both runs saw the same `GMT/Ch01/Submission.lean` (sha256
`518ee03c00e7332a9fc79d2d640a80bb59c528ff903e137a76e81e2ae3db48bf`). Commits after `81b1eaa` change
only this prose file, which is not a comparator input.

**Run 2** was on commit `073cb0d14c1378786ef6826cf0e95fbe2aa3008b`, which adds this prose. It used
the wrapper as the operator updated it during this session (sha256 `bac63e47…`). That wrapper turns
Nanoda off by default; `GMT_COMPARE_NANODA=1` re-enables it, and the Lean-kernel check stays
mandatory. Results:
- `status: passed`; checks `exit_zero`, `lean_kernel_accepted` and `final_marker` all `true`.
- Evidence: `cluster-state/verification/results/hoa34/20261012T022307Z-ch01-root-4eipav7g/`, verdict
  key `39c7b281a8ab799bcbe07bca44ae60beda5a325ad2b6eeb5f4705ab1a1841d78`.

**Run 1** was on the candidate commit `81b1eaaf81a646723f1456b6cb24c1032d3b50a1` (tree
`3f5932502005e76a3082f740939d73df9bfeeae2`). It started before the wrapper update, with Nanoda
enabled. Results:
- `status: passed`; checks `exit_zero`, `nanoda_accepted`, `lean_kernel_accepted` and
  `final_marker` all `true`; `post_check_failures: []`.
- Comparator config: challenge `GMT.Ch01.Contract`, solution `GMT.Ch01.Submission`, theorem
  `GMT.Ch01.main_theorem`, permitted axioms `propext`, `Quot.sound`, `Classical.choice`, Nanoda
  enabled.
- Log tail:
  ```
  Building GMT.Ch01.Contract … Build completed successfully (3195 jobs).
  Building GMT.Ch01.Submission … Build completed successfully (3195 jobs).
  Running nanoda kernel on solution
  nanoda kernel accepts the solution
  Running Lean default kernel on solution.
  Lean default kernel accepts the solution
  Your solution is okay!
  ```
- Evidence:
  `cluster-state/verification/results/hoa34/20261012T020149Z-ch01-root-u5l04pi8/`. The verdict key
  is `cd39a2cd430276151c2ede52af70793c8649cc80388f1f99c957f02514338915`, and the candidate
  `Submission.lean` has sha256 `518ee03c00e7332a9fc79d2d640a80bb59c528ff903e137a76e81e2ae3db48bf`.

The previous candidate `a7bfaca` was rejected; see §6.1.

## 8. Reference use

There is exactly one entry, and its source is `local-project`.

- **source:** `local-project`
- **snapshot:** `.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e`
  (`manifest.json`: mode `local-project`, project `ec1c322fab7585cea8deb6a95d4dae2d97d09d8e`, Mathlib
  `25730c7c759d108ef87ab70af2342a196760f79d`)
- **queries** (paths relative to the snapshot):
  - `cat manifest.json`
  - `rg -n "^theorem main_theorem|^def HausdorffDensityBounds|^namespace|^universe|^end|^open" project/GMT/Ch01/Contract.lean`
    → `open` at 63–65, `namespace GMT.Ch01` at 67, `universe u v` at 69,
    `def HausdorffDensityBounds` at 249, `main_theorem … := by sorry` at 313, `end GMT.Ch01` at 315
  - `rg -n "Submission\.|hausdorff_density_bounds" project/GMT` → only `project/GMT/Ch01/README.md:4`
    (prose). **No match** for any `Submission.*` declaration: the accepted children live on the
    candidate branch, not in the snapshot.
  - `rg -c sorry project/GMT/Ch01/Submission.lean` → 1, and
    `cmp project/GMT/Ch01/Contract.lean project/GMT/Ch01/Submission.lean` → identical: the snapshot's
    `Submission.lean` is the unsolved contract copy.
  - `cmp project/GMT/Ch01/Contract.lean <candidate>/GMT/Ch01/Contract.lean` → identical. The same
    holds for `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and `GMT.lean`.
  - `git -C mathlib grep -n -E "theorem (exists_embedding_l_infty|subalgebra_topologicalClosure_eq_top_of_separatesPoints|setLIntegral_trim_ae|integral_trim_ae|restrict_trim|trim_measurableSet_eq|exist_disjoint_covering_families|integral_rieszMeasure|borel_le_caratheodory|isCompact_univ_pi|measurable_rnDeriv|tendsto_measure_iInter_atTop|norm_setIntegral_le_of_norm_le_const|exists_list_of_mem_closure)…" HEAD -- Mathlib`
    (`git grep` was used on the snapshot's Mathlib checkout because a recursive `rg` over the whole
    Mathlib tree on this file system exceeded two minutes) → `Measure/Hausdorff.lean:161`,
    `Covering/Besicovitch.lean:455`, `Integral/RieszMarkovKakutani/NNReal.lean:47,66`,
    `Integral/Lebesgue/Add.lean:490`, `Integral/Bochner/Basic.lean:1332`, `Measure/Trim.lean:53,108`,
    `Topology/Metrizable/Urysohn.lean:121`, `Topology/ContinuousMap/StoneWeierstrass.lean:264`,
    `Topology/Compactness/Compact.lean:1172`, `Topology/Sequences.lean:298`,
    `Measure/Decomposition/Lebesgue.lean:100`, `Measure/Continuity.lean:220`,
    `Integral/Bochner/Set.lean:613`, `Algebra/Group/Submonoid/Membership.lean:260`
  - `git -C mathlib grep … "(theorem|lemma|def) …(integrable_of_hasCompactSupport|setIntegral_tsupport|nnrealPart_sub_nnrealPart_neg|bounded_above_of_compact_support|exists_superset_of_isCompact|IsMetric)"`
    → `Function/LocallyIntegrable.lean:622`, `Integral/Bochner/Set.lean:1049`,
    `Topology/ContinuousMap/CompactlySupported.lean:749`, `Analysis/Normed/Group/Bounded.lean:153`,
    `Topology/Compactness/SigmaCompact.lean:376`, `Measure/Hausdorff.lean:137`.
    Also `def AreSeparated` at `Topology/MetricSpace/MetricSeparated.lean:99`,
    `def toNNRealLinear` at `CompactlySupported.lean:775`, `def mk₀` at
    `Algebra/Order/Module/PositiveLinearMap.lean:206`, `noncomputable def choice` at `SigmaCompact.lean:418`,
    `exists_pos_sum_of_countable'` at `Analysis/SpecificLimits/Basic.lean:649`, and
    `TendstoUniformly.continuous` at `Topology/UniformSpace/UniformApproximation.lean:128`
  - `git -C mathlib grep -n -E "theorem (rpow_natCast|lt_iff_exists_rat_btwn)\b" HEAD -- Mathlib`, and targeted
    `git grep` for `toMeasure_apply`, `multiplicity`, `isEmpty_satelliteConfig_multiplicity`, `tendsto_pi_nhds`
    and `Measure.ext` → `ENNReal.rpow_natCast` at `Analysis/SpecialFunctions/Pow/NNReal.lean:686`,
    `ENNReal.lt_iff_exists_rat_btwn` at `Basic/ENNReal/Basic.lean:585`,
    `MeasureTheory.toMeasure_apply` at `MeasureTheory/Measure/OuterMeasure.lean:46` (inside
    `namespace MeasureTheory`, line 26),
    `Besicovitch.multiplicity` at `MeasureTheory/Covering/BesicovitchVectorSpace.lean:98`,
    `isEmpty_satelliteConfig_multiplicity` at `BesicovitchVectorSpace.lean:488`, `tendsto_pi_nhds` at
    `Topology/Constructions.lean:811`, `Measure.ext` at `MeasureTheory/Measure/MeasureSpaceDef.lean:144`
  - `git -C mathlib grep -c -E "SimonGMT|GMT\.Ch01|simonHausdorff|IsBorelRegularOuterMeasure|HasSymmetricVitaliProperty" HEAD -- Mathlib`
    → **no match** (0 files) for each pattern: the `simongmt` declarations are not in the snapshot.
    They were read in the pinned package `lake-packages-25730c7c/simongmt`
    (`git rev-parse HEAD` = `2b3663083f3fe399b6296fb8eaee52169170e197`, the revision in
    `project/lake-manifest.json`).
  - Queries added in the §6.2 revision:
    - `rg -n "^namespace|^end|theorem toMeasure_apply\b" mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
      → `namespace MeasureTheory` at 26, `theorem toMeasure_apply` at 46, `end MeasureTheory` at 72.
      So the declaration is `MeasureTheory.toMeasure_apply`, not `OuterMeasure.toMeasure_apply`.
    - `rg -n -A3 "theorem tendsto_measure_iInter_atTop" mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
      → line 220. Its only finiteness hypothesis is `hf : ∃ i, μ (s i) ≠ ∞` (line 222), so no finite
      measure is needed (§3.3).
    - `rg -n "simon_theorem_4_14|exists_unit_modification_on_compacts|norm_eq_one_on_compact_of_measure_envelope|integral_inner_eq_of_ae_eq_on_compacts" project`
      → only `project/GMT/Ch01/README.md:41`, a prose row naming `simon_theorem_4_14`. **No match**
      for any of the four declarations in a Lean file of the snapshot.
    - `git -C mathlib grep -c -E "exists_unit_modification_on_compacts|simon_theorem_4_14|RadonPolarRepresentation" HEAD -- Mathlib`
      → **no match** (exit status 1). The unit-modification step of §3.11 is therefore cited from the
      pinned package, `simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`, at lines
      34, 87, 104, 135, 150, 180–198 and 206, all re-read for this revision.
    - `git -C mathlib grep -n -E "(theorem|lemma) ([A-Za-z_.]*\.)?(exists_continuousMap_one_of_isCompact_subset_isOpen|integral_eq_iff_of_ae_le|measure_eq_iSup_isCompact|exists_norm_eq)\b" HEAD -- Mathlib`
      → the Mathlib lemmas used in that library proof:
      - `exists_continuousMap_one_of_isCompact_subset_isOpen` at `Topology/UrysohnsLemma.lean:529`
        (Urysohn);
      - `integral_eq_iff_of_ae_le` at `MeasureTheory/Integral/Bochner/Basic.lean:776`;
      - `IsOpen.measure_eq_iSup_isCompact` at `MeasureTheory/Measure/Regular.lean:1112`;
      - `exists_norm_eq` at `Analysis/Normed/Module/RCLike/Real.lean:108` (the unit vector `e`).

      The query also matches `MeasurableSet.measure_eq_iSup_isCompact` at `Regular.lean:704`, which
      is not used.
    - `rg -n "RieszVector|riesz_vector|Submission\." project/GMT` → `def RieszVector` (line 279)
      and the unsolved `main_theorem … := by sorry` (line 313) in both `Contract.lean` and
      `Submission.lean`, plus `README.md:4,10,41`. **No match** for `riesz_vector` or for any
      `Submission.*` declaration.
- **files:** `manifest.json`, `project/GMT/Ch01/Contract.lean`, `project/GMT/Ch01/Submission.lean`,
  `project/GMT/Ch01/README.md`, `project/lakefile.toml`, `project/lake-manifest.json`, and the Mathlib
  files listed above (all under the snapshot root).
- **conclusion:** The snapshot fixes the frozen statement:
  - fifteen `Prop` definitions, with `main_theorem` at `Contract.lean:313`, in namespace `GMT.Ch01`
    with `universe u v`;
  - an unsolved `Submission.lean` byte-identical to the contract.

  The candidate preserves the contract and all build inputs byte for byte. Every Mathlib declaration
  cited in §3 was located in the pinned Mathlib by the queries above. The `simongmt` theorems are not in
  the snapshot. They are reused from the pinned package with the provenance given in §3, and the root
  comparator verifies them by kernel replay with an axiom check. The root step itself (§2) uses no
  library declaration.

## 9. Citations

- L. Simon, *Introduction to Geometric Measure Theory*, 2014 Tsinghua lecture notes:
  https://web.stanford.edu/class/math285/ts-gmt.pdf. The workspace copies used are
  `book/chapter-01.txt` and `book/sources/chapter-01-source.txt`. Theorem and page numbers above
  are printed pages.
- Mathlib, revision `25730c7c759d108ef87ab70af2342a196760f79d` (declarations as cited in §3 and §8).
- `simongmt` (`Poincare.SimonGMT`), revision `2b3663083f3fe399b6296fb8eaee52169170e197`, pinned in
  `lake-manifest.json` (declarations as cited in §3).
