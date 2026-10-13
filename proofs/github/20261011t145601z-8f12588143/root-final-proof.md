# Final proof of `GMT.Ch03.main_theorem` (root node)

Run `20261011T145601Z-8f12588143`, node `root`, issue
<https://github.com/ZhengyangZhang06/gmt-formalize/issues/7>.
Lean target `GMT/Ch03/Submission.lean`; frozen contract `GMT/Ch03/Contract.lean` at the frozen
commit `d09bc8a18ce60face651f042976e8465f21f0f68` (Lean `v4.35.0-rc3`, Mathlib `25730c7c`,
`simongmt` package `2b366308`).

## 1. Statement

```lean
theorem main_theorem : SubmanifoldCoverCharacterization ∧ ApproximateTangentCharacterization ∧
    WeightedApproximateTangentCharacterization ∧ AreaFormula ∧ CoareaFormula ∧
    SlicesAreRectifiable ∧ RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧
    BesicovitchFedererProjectionTheorem ∧ RectifiabilityTheoremForSets ∧
    GaussGreenRepresentation ∧ DeGiorgiTheorem
```

The twelve conjuncts are the headline results of Simon, *Introduction to Geometric Measure
Theory*, Ch. 3 (`chapter-03.txt`): Lemma 1.2 (ll. 25–65), Theorem 1.6 (ll. 109–274),
Theorem 1.9 (ll. 316–323), the area formula (2.4)–(2.5) (ll. 370–401), the co-area formula
(2.8)–(2.9) and Remark 2.10(2) (ll. 412–442), Lemmas 3.2 and 3.3 (ll. 449–496), the
Besicovitch–Federer Theorem 3.6 (ll. 530–536), Theorem 3.8 (ll. 540–548), the Gauss–Green
representation (4.1) (ll. 555–573) and De Giorgi's Theorem 4.3 (ll. 588–746). Every conjunct is a
closed proposition (a `def … : Prop` of the frozen contract); `main_theorem` has no hypotheses.

## 2. The Lean argument actually used

The proof term of `main_theorem` is an anonymous-constructor assembly of eight accepted child
theorems (all in namespace `GMT.Ch03`):

```lean
  ⟨Submission.submanifoldCoverCharacterization_holds,
    Submission.approximateTangentCharacterizations_hold.1,
    Submission.approximateTangentCharacterizations_hold.2,
    Submission.areaFormula_holds,
    Submission.coareaFormula_and_slices_hold.1,
    Submission.coareaFormula_and_slices_hold.2,
    Submission.section3_decomposition_projection_rectifiability.1,
    Submission.section3_decomposition_projection_rectifiability.2.1,
    Submission.besicovitchFedererProjectionTheorem_holds,
    Submission.section3_decomposition_projection_rectifiability.2.2,
    Submission.gaussGreenRepresentation_holds,
    Submission.deGiorgiTheorem_holds⟩
```

| Conjunct (book item) | Supplied by (frozen type of the accepted child) |
|---|---|
| `SubmanifoldCoverCharacterization` (Lemma 1.2) | `submanifoldCoverCharacterization_holds : SubmanifoldCoverCharacterization` |
| `ApproximateTangentCharacterization` (Thm 1.6) | `approximateTangentCharacterizations_hold.1`; type `ApproximateTangentCharacterization ∧ WeightedApproximateTangentCharacterization` |
| `WeightedApproximateTangentCharacterization` (Thm 1.9) | `approximateTangentCharacterizations_hold.2` |
| `AreaFormula` ((2.4)–(2.5)) | `areaFormula_holds : AreaFormula` |
| `CoareaFormula` ((2.8)–(2.9)) | `coareaFormula_and_slices_hold.1`; type `CoareaFormula ∧ SlicesAreRectifiable` |
| `SlicesAreRectifiable` (Rem. 2.10(2)) | `coareaFormula_and_slices_hold.2` |
| `RectifiableDecomposition` (Lemma 3.2) | `section3_decomposition_projection_rectifiability.1`; type `RectifiableDecomposition ∧ CoordinateProjectionCriterion ∧ RectifiabilityTheoremForSets` |
| `CoordinateProjectionCriterion` (Lemma 3.3) | `section3_decomposition_projection_rectifiability.2.1` |
| `BesicovitchFedererProjectionTheorem` (Thm 3.6) | `besicovitchFedererProjectionTheorem_holds : BesicovitchFedererProjectionTheorem` |
| `RectifiabilityTheoremForSets` (Thm 3.8) | `section3_decomposition_projection_rectifiability.2.2` |
| `GaussGreenRepresentation` ((4.1)) | `gaussGreenRepresentation_holds : GaussGreenRepresentation` |
| `DeGiorgiTheorem` (Thm 4.3) | `deGiorgiTheorem_holds : DeGiorgiTheorem` |

Each child's type is literally the corresponding contract proposition (or a conjunction of
them, projected with `.1`/`.2`), so the assembly needs no further mathematics: the mathematical
content is entirely in the accepted children, summarized in §4.

### Assumptions

* No hypotheses beyond the frozen contract. The contract's text (everything before
  `main_theorem`) is reproduced byte-for-byte; the only header change is one extra import,
  `Poincare.SimonGMT.Chapter03.SubmanifoldCover` (pinned `simongmt` package), which the accepted
  Lemma 1.2 child uses for the "⇐" direction. I checked that this import does not change the
  elaboration of any frozen constant: elaborating the contract preamble with and without it gives
  identical structural hashes for all 54 constants in `GMT.Ch03` (types, definition bodies and the
  auxiliary `_proof_n` terms). The comparator independently checks equality of every constant
  reachable from the statement (§8).
* Axioms: only `propext`, `Quot.sound`, `Classical.choice` (`#print axioms GMT.Ch03.main_theorem`;
  also checked by the comparator). There is no `sorry`, no new `axiom`, and no change to any
  definition or assumption.
* Besides the accepted theorems, the file contains only build infrastructure local to the section
  that holds them (`set_option`s and one `private` tooling elaborator, §3), which affects
  elaboration metadata and memory use, not the elaborated declarations.

## 3. How this candidate was assembled (integration repair)

The previous root candidate `9831a15e` was produced by line-level Git merges of the twelve
accepted child checkpoints and was rejected by the comparator: the merges had interleaved
fragments of different proofs (in `Submission.setIntegral_blowUpMap_image`,
`gaussGreenRep_divergence_integral_local_bound`, `areaFormula_on_chart_piece`,
`bf_coneMass_slab_cover` and `rectifiable_of_approx_tangent_measure`), declared
`setIntegral_blowUpMap_image`, `gaussGreenRep_divergence_integral_local_bound` and
`bf_coneMass_slab_cover` twice (garbled first copies), placed several helpers (e.g.
`gaussGreenRep_c1_uniform_approx`, `lipschitz_uniform_remainder_on_closed_subset`) after their
first use, and left the child theorems *after* `main_theorem` (each child checkpoint places its own
theorem after the contract's `main_theorem := by sorry`), so `main_theorem` could not see them.

This candidate replaces the merged text by a clean union of the accepted checkpoints:

* Sources: the accepted candidate commits of the twelve direct children —
  `c1_approximation` `849b6ec060`, `eilenberg_inequality` `c2a19cb278`,
  `rectifiable_of_tangent_measure` `f0931a9d98`, `chart_tangent_differential` `89498ad9db`,
  `submanifold_cover` `504efa5909`, `tangent_characterizations` `fe8fba36e3`,
  `area_formula` `fd34bbfe66`, `coarea_and_slices` `a6297ede5f`, `besicovitch_federer`
  `b633a94f45`, `section3_consequences` `9477567347`, `gauss_green` `eef5ae893c`,
  `de_giorgi` `f33bed6a50`. Each of these files compiled and passed its own comparator check.
* Each file was split into top-level declarations. Every declaration occurring in several
  checkpoints has the same text in all of them (the only differences were trailing blank lines),
  so the union is well defined: 226 theorems, exactly the 226 accepted DAG nodes below the root
  (every accepted `lean_name` occurs exactly once; no other theorem was added — the only other new
  declaration is the `private` tooling elaborator described below; no duplicated namespace or
  placeholder scaffold remains). Statements and proof bodies are copied verbatim — no
  proof was edited.
* Order: first occurrence when reading the checkpoints in the DAG order above. This is a valid
  dependency order because every checkpoint compiled in its own order; I also extracted the 250
  references between the 226 declarations from the comment-stripped source and checked that none
  points forward.
* The 226 declarations sit in `section AcceptedChildDeclarations … end AcceptedChildDeclarations`;
  `main_theorem` comes after the section, followed by `end GMT.Ch03`.

**Memory (build infrastructure only).** The first comparator run of the plain union was killed by
the out-of-memory killer (`Lean exited with code 137`): the verification workers run in a container
whose cgroup limit is 3.5 GB, and Lean's command-line driver keeps the info tree of every command
until the end of the file (to write the `.ilean`). Measured with `LEAN_NUM_THREADS=4`, the plain
20k-line file reaches 2.67 GB of anonymous memory plus ~1.6 GB of mapped `.olean`s, i.e. it only
fits by thrashing. The section therefore starts with

* `set_option Elab.async false` (elaborate the declarations one at a time),
* a `private` command elaborator `elabDeclarationWithoutInfoTrees`, registered with
  `@[local command_elab Lean.Parser.Command.declaration]`, which turns info-tree recording off,
  calls Lean's builtin `Lean.Elab.Command.elabDeclaration` on the unchanged syntax, and restores the
  flag,
* `set_option linter.unusedTactic false` (Mathlib) and `set_option linter.unreachableTactic false`
  (Batteries), the two linters that read tactic info trees and would otherwise report every
  tactic as unused or never executed.

Info trees are editor metadata (hover, go-to-definition, `.ilean` references); the elaborated
declarations are unchanged and every one is still checked by the kernel. The elaborator is a
tooling `def`, not a theorem, is not reachable from `main_theorem` (so it is not part of the
comparator's export), and everything is local to the section: after `end
AcceptedChildDeclarations` the builtin elaborator is the only one for declarations and
`Elab.async` is back at its default, so `main_theorem` is elaborated with the default settings
(both facts checked with a probe on a test slice). On a 5.8k-line slice the peak anonymous memory
drops from 986 MB to 412 MB (import baseline 257 MB); on the full file from 2.67 GB to 0.69 GB.

## 4. Proof of each conjunct (the accepted children)

Each child below has its own reviewed natural-language proof (`parent-supplied-natural-proof.md`
under `.humanize-workspace/20261011t145601z-8f12588143/root/children/<child>/` and the run's
`nodes/<child>/`), its own decomposition into accepted grandchildren, and a kernel-checked Lean
proof that passed the comparator for its frozen type. The summaries below describe the routes of
the Lean proofs as documented in the declarations' docstrings; departures from the book are
stated.

### 4.0 Four shared auxiliary results (not used directly by `main_theorem`)

* **`lipschitz_c1_approximation`** (issue #21; Simon Ch. 2, Thm 1.5): every Lipschitz
  `f : ℝⁿ → ℝᵖ` agrees, together with its derivative, with a `C¹` map outside a set of
  arbitrarily small Lebesgue measure. Coordinatewise reduction to the scalar case
  `lipschitz_real_c1_approximation`: Rademacher (Mathlib `LipschitzWith.ae_differentiableAt`),
  Lusin for `Df`, and Egoroff for the Taylor remainders give a closed `A` with the uniform
  remainder estimate 1.6(‡); Whitney's extension theorem (Ch. 2, 1.6) is proved inline: off `A`,
  `g` averages the jets `f(p) + Df(p)(· − p)` at nearest points `p ∈ A` with a partition of unity
  (Mathlib `ContDiffBump`) on Vitali-selected balls `B(c, min(1, d(c, A))/100)` of bounded overlap.
* **`eilenberg_upper_integral_inequality`** (issue #22; Ch. 2, 1.8–1.9): for an `L`-Lipschitz
  `f : ℝᴺ → ℝᵐ` and any `A`, a Borel `g ≥ Hᵏ(A ∩ f⁻¹{y})` with `∫ g ≤ C Lᵐ H^{m+k}(A)`: near-optimal
  covers `Cᵢⱼ`, `gᵢ = ∑ⱼ diam(Cᵢⱼ)ᵏ 1_{closure f(Cᵢⱼ)}`, `g = liminf gᵢ`, Fatou, and
  `Lᵐ(closure S) ≤ ωₘ (diam S)ᵐ` in place of the isodiametric inequality; the cases
  `H^{m+k}(A) = ∞` and `L = 0` are treated directly.
* **`rectifiable_of_approx_tangent_measure`** (issue #23; the measure form of Thm 1.6 "⇐",
  ll. 145–274, with Remark 1.5(3)): a locally finite Borel measure with approximate tangent
  planes of positive multiplicity a.e. is carried by a Borel countably `n`-rectifiable set. For
  `n = 0` the lower density bound makes `μ` atomic. For `n ≥ 1`: a countable `1/16`-net of
  `n`-planes, the sets where the density and cone bounds of Simon (9) hold uniformly below a
  scale, bi-Lipschitz projection onto a net plane on each such set (Simon (10), with the corrected
  constant `b = a/(2·32ⁿ)`), hence countably many Lipschitz graphs.
* **`chart_approx_tangent_and_differential`** (issue #24; Remarks 1.5(2), 1.8(1), Ch. 2
  (4.8)–(4.10)): for a `C¹` immersion `ψ` and a.e. parameter `u` with `ψ(u) ∈ M`, (A) `range Dψ(u)`
  is the weighted approximate tangent space of `M` at `ψ(u)`, (B) `f ∘ ψ` is differentiable at `u`,
  (C) `D(f∘ψ)(u)w` is the line derivative of `f` at `ψ(u)` in direction `Dψ(u)w`. (A): local
  bi-Lipschitz balls, the upper-density theorem and Lebesgue differentiation give the density
  conditions a.e. on `M ∩ ψ(B)`, and the blow-ups of the `C¹` piece converge to `range Dψ(u)`.

### 4.1 Lemma 1.2 — `submanifoldCoverCharacterization_holds` (issue #25)

"⇐": `Poincare.SimonGMT.Chapter03.countablyRectifiable_of_submanifold_cover` (pinned library;
`Chapter02.IsSimonSubmanifold 1` is `IsC1Submanifold n` with the conditions reordered). "⇒":
`lipschitz_c1_approximation` gives `C¹` maps `Gⱼᵢ` with `Lⁿ{Fⱼ ≠ Gⱼᵢ} < 1/i`; with
`Zⱼ = ℝⁿ ∖ ⋃ᵢ {Fⱼ = Gⱼᵢ}`, `Fⱼ(ℝⁿ) ⊆ Fⱼ(Zⱼ) ∪ ⋃ᵢ Gⱼᵢ(ℝⁿ)` and `Hⁿ(Fⱼ(Zⱼ)) = 0` (erratum: the
book's (1) is printed as `graph Fⱼ ⊂ Eⱼ ∩ …`). For one `C¹` map `G`
(`c1_range_null_union_submanifolds`): the critical image is `Hⁿ`-null — Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` cuts the critical set into pieces on
which `G` is `δ`-close to a non-injective linear map, and a stretch along its kernel gives
`Hⁿ(G(P)) ≤ (‖A‖+1)ⁿ δ Lⁿ(P)`; each regular point has a ball whose image is an embedded `C¹`
submanifold; Lindelöf gives countably many.

### 4.2 Theorems 1.6 and 1.9 — `approximateTangentCharacterizations_hold` (issue #26)

Theorem 1.9 is proved first and Theorem 1.6 is its case `θ ≡ 1` (admissible because
`Hⁿ(M ∩ K) < ∞`, and then Def. 1.7 is Def. 1.4). "⇒": Lemma 1.2 gives `M ⊆ N₀ ∪ ⋃ⱼ Nⱼ`; in every
`C¹` chart the weighted tangent plane at `ψ(u)` is `range Dψ(u)` for a.e. `u`
(`chart_approx_tangent_and_differential` with `f = 0`), and the chartwise transfer
`ae_of_ae_on_submanifold_charts` (Lindelöf; chart images of `Lⁿ`-null sets are `Hⁿ`-null) makes
this `Hⁿ`-a.e. on `M`. "⇐": `μ = θ Hⁿ⌞M` is finite on compacts, has the null sets
`{S : Hⁿ(M ∩ S) = 0}`, and has approximate tangent plane `P` with multiplicity `θ(x) > 0` wherever
`M` has weighted tangent plane `P` (change of variables under `η_{x,r}`,
`weightedMeasure_finite_null_tangent`); `rectifiable_of_approx_tangent_measure` gives a Borel
rectifiable `R` with `μ(Rᶜ) = 0`, i.e. `Hⁿ(M ∖ R) = 0`.

### 4.3 Area formula — `areaFormula_holds` (issue #27)

Lemma 1.2 and `areaFormula_good_chart_pieces` cover `M`, up to an `Hⁿ`-null set, by countably
many compact chart pieces `ψ_α(D_α)` with `ψ_α` bi-Lipschitz and `f ∘ ψ_α` Lipschitz. At a.e.
parameter, `chart_approx_tangent_and_differential` and `areaFormula_chart_jacobian_identity`
(uniqueness of tangent spaces and line derivatives; Mathlib `LinearMap.normDet_comp`) give
`T_xM = range Dψ_α(u)`, the tangential differential, and `J^M_f(ψ_α u)·Jψ_α(u) = J(f∘ψ_α)(u)`;
this proves (a). On one piece (`areaFormula_on_chart_piece`) the weighted area formula with
multiplicity of Simon Ch. 2 (3.2), (3.4)–(3.5) is applied to `ψ_α` and `f ∘ ψ_α`; since the SimonGMT
modules proving it are not imported, it is derived in the file from the linear case (Mathlib
`LinearMap.euclideanHausdorffMeasure_image`) by comparison with linear maps on the pieces of
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`. `areaFormula_glue_pieces` sums over
the pieces; the uncovered part and its image are `Hⁿ`-null
(`areaFormula_image_null_of_locallyLipschitzOn`); (2.4) is the case `h ≡ 1`. Erratum: outer
integrals over the target `ℝ^{n+ℓ₁}`.

### 4.4 Co-area formula and slices — `coareaFormula_and_slices_hold` (issue #28)

`rectifiable_c1_chart_pieces` (Lemma 1.2 and `lipschitz_c1_approximation`) covers `M`, up to an
`Hⁿ`-null set, by Borel pieces `ψ_j(E_j)` of injective `C¹` charts on which `f ∘ ψ_j` agrees to
first order with a `C¹` map `G_j`. (a) is `coarea_tangent_existence` (chart lemma plus
`chart_coarea_jacobian_identification`). On one piece, `chart_piece_coarea_formula` combines the
`C¹` parametric co-area formula `c1_parametric_coarea_formula` (Simon Ch. 2, 6.3/6.6, whose proof
Simon omits: critical part with `Hᵏ`-null slices for a.e. `y` via a cube-subdivision covering,
implicit-function charts, the flat Jacobian identity, Tonelli on `ℝᵐ × ℝᵏ` and change of
variables) with the injective `C¹` area formula and Lusin–Souslin, and the Jacobian identification
`J^{M*}_f(ψ u)·Jψ(u) = normDet(Dψ(u)∘ι_{ker DG(u)})·normDet(DG(u)*)`. `coarea_gluing_of_pieces`
sums the pieces, null sets having `Hᵏ`-null slices for a.e. `y` by
`coarea_null_slices_of_eilenberg` (Eilenberg's inequality applied to Lipschitz extensions,
`LipschitzOnWith.extend_finite_dimension`); (2.8) is (2.9) with `g ≡ 1`; `m = 0` is direct.
Slices: `c1_level_slices_countablyRectifiable` (regular parts are implicit-function `C¹` images,
critical parts are `Hᵏ`-null for a.e. `y`). Erratum: (2.9) is stated with `A` on both sides.

### 4.5 Besicovitch–Federer — `besicovitchFedererProjectionTheorem_holds` (issue #29)

The book gives no proof (l. 536: "see [Fed69] or [Ros84]"); the accepted proof follows P. Mattila,
*Geometry of Sets and Measures in Euclidean Spaces*, Ch. 15 and 18, as presented in M. G.
Dall'Alba, *The Besicovitch–Federer Projection Theorem* (Padova 2020), Thm. 5.1. Step 0: `n = 0`
forces `Q = ∅`, `ℓ = 0` forces `Hⁿ(Q) = 0`. Step 1 (`bf_compact_cover_reduction`): Borel hulls and
SimonGMT's measurable Lemma 3.2 (`measurable_rectifiable_purelyUnrectifiable_decomposition`) plus
inner regularity cover `Q` by a null set and compact purely unrectifiable sets of finite measure.
Steps 2–10 (`bf_compact_projection_null`): cone-free sets are rectifiable, so the cone density is
positive a.e.; where it is infinite the projection is null (Vitali covering); the cone trichotomy
holds for a.e. frame (`bf_coneTrichotomy_ae_frames`: sphere density dichotomy for slab cones,
averaging over `O(N)` with Haar measure (Mathlib `Measure.haarMeasure`) and transfer to
Lebesgue-a.e. frames, the contract's encoding `ForAlmostAllProjections` of "σ-a.e. projection");
so outside null sets every point has an infinite fibre, and infinite fibres have null projection
by `eilenberg_upper_integral_inequality` (`k = 0`).

### 4.6 Lemmas 3.2, 3.3 and Theorem 3.8 — `section3_decomposition_projection_rectifiability` (issue #30)

3.2 (`section3_rectifiableDecomposition`): `Poincare.SimonGMT.Chapter03.simon_lemma_3_2` with the
cover `(Aⱼ)`. 3.3 (`section3_coordinateProjectionCriterion_of_submanifoldCover`): by Lemma 1.2 and
Lindelöf it suffices that `R ∩ Nⱼ ∩ W = ψ(T)` is null for each chart `ψ : V → W`; if `Lⁿ(T) = 0`
then `Hⁿ(ψ(T)) = 0` (`C¹` images of null sets); otherwise some coordinate projection `p_J` with
`#J = n` is injective on the tangent plane, `p_J ∘ ψ` is anti-Lipschitz near a density point of `T`,
and `Hⁿ(p_J(S)) > 0`, a contradiction. 3.8
(`section3_rectifiabilityTheorem_of_besicovitchFederer`): split `A = R ∪ P` by 3.2; by 3.6,
`Hⁿ(p(P)) = 0` for almost all `p`, so the hypothesis with `B = P` forces `Hⁿ(P) = 0`. Erratum:
l. 540 "by combining 3.2 and 3.7" should read "3.2 and 3.6".

### 4.7 Gauss–Green representation — `gaussGreenRepresentation_holds` (issue #31)

"⇐" (`gaussGreenRep_isLocallyBV_of_pair`): the pair identity bounds `∫_W χ_E div g` by
`μ(W̄) sup|g|`. "⇒": the BV bound extends `g ↦ ∫_{E∩U} div g` from `C¹` fields to a locally bounded
functional `Λ` on continuous compactly supported fields (`gaussGreenRep_bv_functional_extension`,
uniform `C¹` approximation); the Riesz representation on the open set `U`
(`gaussGreenRep_riesz_on_open`, Simon Ch. 1, 4.14) gives `Λ g = ∫⟨g, ν₀⟩ dμ`, and the pair is
`(μ, −ν₀)`. The vector Riesz step (`gaussGreenRep_riesz_sigmaCompact_borel`) splits each component
functional into positive parts, represents them with Mathlib's Riesz–Markov–Kakutani
`RealRMK.rieszMeasure`, and takes Radon–Nikodym densities and the polar decomposition.
Uniqueness: two pairs pair equally with continuous fields (`gaussGreenRep_pairing_eq_continuous`);
the variation formula `μ(O) = sup ∫⟨g, ν⟩ dμ` (`gaussGreenRep_measure_eq_iSup_pairing`, Lusin and a
unit-field extension) makes the measures agree on open subsets of `U`, hence everywhere
(`gaussGreenRep_measure_eq_of_open_eq`, π–λ); the normals agree `μ`-a.e. by the fundamental lemma
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).

### 4.8 De Giorgi — `deGiorgiTheorem_holds` (issue #32)

A pair exists by 4.7. For any pair `(μ, ν)` and `x ∈ ∂*E`: the density estimates
(`deGiorgi_density_estimates`: Simon (1)–(6), (10), (11), using the complement pair `(μ, −ν)` of
`U ∖ E`, an upper mass bound, and a lower volume bound from an `L¹` Sobolev inequality for `ζχ_G`,
the Gagliardo–Nirenberg–Sobolev inequality being proved in the file because Mathlib's
`SobolevInequality` module is not imported); compactness of the blow-ups `η_{x,r}(E)` in `L¹_loc`
(`deGiorgi_indicator_compactness`: translation estimates, mollification, diagonal
Arzelà–Ascoli); half-space rigidity of every limit (`deGiorgi_halfSpace_rigidity`), giving (‡‡)
(`deGiorgi_blowUp_tendsto_halfSpace`; erratum: (9) and the final display must read
`{x^{n+1} > λ}`, `{x^{n+1} > 0}`); (‡) with multiplicity 1 from the blow-up Gauss–Green identity,
the excess decay and the mass bound (`deGiorgi_tangent_measure`). Then `∂*E` is Borel
(`deGiorgi_measurableSet_reducedBoundary`) and carries `μ` (`deGiorgi_measure_compl_reducedBoundary`,
Lebesgue–Besicovitch differentiation), and `deGiorgi_rectifiable_measure_eq_hausdorff` — which
takes `rectifiable_of_approx_tangent_measure` and `approximateTangentCharacterizations_hold.1` as
inputs — gives rectifiability of `∂*E` and `μ = Hⁿ⌞∂*E` via `Hⁿ(A) ≤ μ(A) ≤ 2ⁿHⁿ(A)` on `∂*E` and a
density comparison (Mathlib `Besicovitch.ae_tendsto_rnDeriv`). This completes the book's sketch at
l. 604 ("By 1.6 and 3.6 of Ch. 1").

### Dependency structure (extracted from the Lean source)

Lemma 1.2 ← `lipschitz_c1_approximation`; 1.6/1.9 ← Lemma 1.2,
`rectifiable_of_approx_tangent_measure`, `chart_approx_tangent_and_differential`; area ← Lemma 1.2,
chart lemma; co-area/slices ← Lemma 1.2, `lipschitz_c1_approximation`,
`eilenberg_upper_integral_inequality`, chart lemma; 3.6 ← Eilenberg; 3.2/3.3/3.8 ← Lemma 1.2, 3.6;
(4.1) ← none; 4.3 ← (4.1), `rectifiable_of_approx_tangent_measure`, 1.6/1.9. The graph is acyclic,
and no child depends on `main_theorem`.

## 5. Historical decomposition versus lemmas actually used

* The root's accepted outline (`nodes/root/natural-proof-source.md`: "follow the published proof"
  for each of the twelve conjuncts) and plan (`nodes/root/plan-source.md`: decompose along the
  conjuncts) are unchanged history; the reviewed decomposition is `nodes/root/decomposition-v1.json`
  (12 children). The final Lean route is exactly that decomposition.
* Of the 226 accepted declarations, 225 are reachable from `main_theorem`. The exception is
  `Submission.gaussGreenRep_riesz_caratheodory_borel_version` (node
  `root.gauss_green-a1.riesz_on_open-a1.caratheodory_borel_version-a1`), which its parent's final
  proof does not use; it is kept unchanged to preserve the accepted child interface.
* Where a child's reviewed outline named a library lemma that the final Lean proof does not use,
  the Lean route is the one stated in §4: Whitney's extension theorem is proved inline (not taken
  from SimonGMT), the Riesz step uses Mathlib's `RealRMK.rieszMeasure` (not SimonGMT's Ch. 1,
  4.14), and the Lipschitz area formula on parameter domains is derived in the file from Mathlib's
  linear case (not SimonGMT's Ch. 2 area formula).

## 6. Library reuse provenance

All reused library results are existing, pinned declarations, used with their own proofs:

* `simongmt` (`Poincare.SimonGMT`, rev `2b3663083f3f`):
  `Chapter03.countablyRectifiable_of_submanifold_cover` (Lemma 1.2 "⇐"),
  `Chapter03.simon_lemma_3_2` (Lemma 3.2),
  `Chapter03.measurable_rectifiable_purelyUnrectifiable_decomposition` (3.6, Step 1),
  `Chapter03.HasWeightedApproximateTangentSpaceAt.unique`, `Chapter03.countablyRectifiable_iUnion`,
  `countablyRectifiable_sUnion`, `countablyRectifiable_range`, `countablyRectifiable_of_measure_zero`,
  `Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule`,
  `Chapter03.support_euclideanHausdorffMeasure_restrict_submodule`,
  `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`, and the divergence API used by the
  contract (`Chapter02.euclideanDivergence`, `euclideanDivergence_eq_sum_inner`,
  `support_euclideanDivergence_subset`, `compactlySupportedSupNorm`).
* Mathlib (rev `25730c7c`), e.g. `LipschitzWith.ae_differentiableAt` (Rademacher),
  `LinearMap.normDet_comp`/`normDet_sq`, `LinearMap.euclideanHausdorffMeasure_image`,
  `exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, `Besicovitch.ae_tendsto_rnDeriv`,
  Vitali covering `exists_disjoint_covering_ae`, `Measure.haarMeasure`, `RealRMK.rieszMeasure`,
  `ContDiffBump`, `LipschitzOnWith.extend_finite_dimension`,
  `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

## 7. Reference use

`reference_use` (exactly one entry):

* **source:** `local-project` — snapshot
  `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063`
  (manifest: project `d09bc8a18ce6`, mathlib `25730c7c759d`).
  **Queries and findings:**
  `cmp project/GMT/Ch03/Contract.lean <frozen contract>` — identical (the snapshot's
  `Submission.lean` is also a byte copy of the contract);
  `rg -n "theorem Submission\." project/GMT/` — **no match** (all 226 helper declarations come
  from this run's accepted checkpoints, none from the snapshot);
  `rg -n "SubmanifoldCover" project/GMT/Ch03/README.md` — ll. 16, 29: Lemma 1.2 "⇐" is
  `Chapter03.countablyRectifiable_of_submanifold_cover` in `Chapter03/SubmanifoldCover.lean`
  (justifies the one added import);
  `rg -l "CountablyRectifiable|PurelyUnrectifiable" mathlib/Mathlib/{MeasureTheory,Analysis,Topology}`
  — **no match** (rectifiability is not in Mathlib; it comes from `simongmt` and this run);
  `rg -n "SobolevInequality|RieszMarkovKakutani" project/GMT/Ch03/` — **no match** (neither is
  imported by the contract);
  `rg -n "def rieszMeasure" mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/` —
  `Real.lean:65` (`RealRMK.rieszMeasure`, used in 4.7);
  `rg -n "theorem ae_tendsto_rnDeriv" mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean` —
  l. 1078 (used in 4.8);
  `rg -n "theorem LipschitzWith.ae_differentiableAt" mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
  — l. 385; `rg -n "theorem normDet_comp|theorem normDet_sq" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
  — ll. 294, 324; `rg -n "def haarMeasure" mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean` —
  l. 520; `rg -n "theorem exists_disjoint_covering_ae" mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
  — l. 237.
  Compatibility: every cited declaration is from the pinned Mathlib/`simongmt` revisions used by the
  build, and the comparator's axiom check covers them.

## 8. Verification

* `lake build GMT.Ch03.Submission` (local, this worktree): succeeded; `GMT.Ch03.Submission` built
  in 1035 s with no errors and no `sorry` (only the module-system import warnings that the frozen
  contract itself produces).
* `#print axioms GMT.Ch03.main_theorem`: `[propext, Classical.choice, Quot.sound]`.
* Child interfaces: all 226 accepted children's frozen `lean_statement`s (from the run's
  `dag.json`, normalized by the workflow validator `lean_contract.py`) were elaborated in the
  comparator's replayed contract scope after `import GMT.Ch03.Submission` and closed by
  `exact Submission.<lean_name>`: 226/226 succeed, 0 errors.
* Comparator: COMPARATOR_PENDING
