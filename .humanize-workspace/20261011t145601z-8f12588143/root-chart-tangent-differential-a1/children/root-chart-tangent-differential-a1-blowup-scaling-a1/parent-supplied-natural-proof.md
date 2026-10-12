# Parent-supplied natural-language proof

- Parent DAG node: `root.chart_tangent_differential-a1`
- Child DAG node: `root.chart_tangent_differential-a1.blowup_scaling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the change of variables (F1) of the parent proof (Notation, (F1)); it is the identity used implicitly in Simon's proof of Theorem 1.6 '⇒' (chapter-03.txt lines 113-143), where ∫_{η_{x,λ}(M)} f dHⁿ is compared with integrals over M, and in Definition 1.7 (lines 284-295). It uses only the scaling and translation behaviour of Hausdorff measure. All lemmas cited are available after `import GMT.Ch03.Submission`.

Notation. η := η_{x,r}, μ := Hⁿ = μHE[n] on ℝ^N. For S ⊆ ℝ^N, μ⌞S is the restriction (Mathlib μ.restrict S): (μ⌞S)(T) = μ(T ∩ S) for every Borel T; S itself need not be measurable.

1. η(y) = r⁻¹(y − x) is an affine bijection of ℝ^N with inverse η⁻¹(y) = x + r·y. Both maps are continuous, so η is a homeomorphism, hence a measurable equivalence of (ℝ^N, Borel σ-algebra); in particular η is a measurable embedding and η⁻¹(T) is Borel for Borel T.

2. Scaling of Hⁿ. For every set S ⊆ ℝ^N (measurable or not), μ(η⁻¹(S)) = rⁿ μ(S). Indeed η⁻¹(S) = {x + r y : y ∈ S} = h(S + x), where S + x is the translate of S and h := AffineMap.homothety x r, h(z) = r(z − x) + x (so h(y + x) = r y + x). Translations are isometries, so μ(S + x) = μ(S) (Isometry.euclideanHausdorffMeasure_image), and μ(h(S')) = ‖r‖₊ⁿ μ(S') for every S' because r ≠ 0 (MeasureTheory.euclideanHausdorffMeasure_homothety_image); as r > 0, ‖r‖₊ⁿ = rⁿ. (Equivalently, η⁻¹(S) = h'⁻¹(S + x) for h' := AffineMap.homothety x r⁻¹, and MeasureTheory.euclideanHausdorffMeasure_homothety_preimage gives μ(h'⁻¹(S')) = (‖r⁻¹‖₊⁻¹)ⁿ μ(S') = rⁿ μ(S').) These are identities of the Hausdorff outer measure, valid for arbitrary sets.

3. Push-forward identity: η_#(μ⌞A) = rⁿ · (μ⌞η(A)) as Borel measures. Let T be Borel. Then η_#(μ⌞A)(T) = (μ⌞A)(η⁻¹(T)) = μ(η⁻¹(T) ∩ A) (η⁻¹(T) is Borel). Since η is a bijection, η⁻¹(T) ∩ A = η⁻¹(T ∩ η(A)), so by step 2 this equals rⁿ μ(T ∩ η(A)) = rⁿ (μ⌞η(A))(T). Two Borel measures that agree on all Borel sets are equal.

4. Integrals. Since 0 < rⁿ < ∞, step 3 gives μ⌞η(A) = r^{-n} · η_#(μ⌞A). For every g : ℝ^N → ℝ:
 ∫ g d(μ⌞η(A)) = r^{-n} ∫ g d(η_#(μ⌞A)) (integral against a constant multiple of a measure, Mathlib integral_smul_measure; valid for every g, both sides being 0 when g is not integrable),
 = r^{-n} ∫ g∘η d(μ⌞A) (change of variables along the measurable embedding η, Mathlib MeasurableEmbedding.integral_map; valid for every g, since g is η_#(μ⌞A)-integrable iff g∘η is μ⌞A-integrable and both Bochner integrals are 0 otherwise).
 This is exactly ∫_{η(A)} g dHⁿ = r^{-n} ∫_A g(η(z)) dHⁿ(z).

5. Remark on n = 0. Then rⁿ = 1 and the statement is the invariance of the counting measure H⁰ under the bijection η; the argument of steps 1-4 covers this case without change. ∎

## Key steps

1. η_{x,r} is an affine homeomorphism of ℝ^N (a measurable equivalence) with inverse y ↦ x + r y.
2. Hⁿ(η⁻¹(S)) = rⁿ Hⁿ(S) for every set S, by homothety scaling (euclideanHausdorffMeasure_homothety_image/_preimage) and translation invariance.
3. η_#(Hⁿ⌞A) = rⁿ·Hⁿ⌞η(A) on Borel sets, using η⁻¹(T) ∩ A = η⁻¹(T ∩ η(A)).
4. integral_smul_measure and MeasurableEmbedding.integral_map give ∫_{η(A)} g dHⁿ = r^{-n}∫_A g∘η dHⁿ for every g.

## Reference use

### local-project

Queries:
- `rg -n "^def |^noncomputable def |^abbrev " project/GMT/Ch03/Contract.lean (Rn, IsPositiveLocallyIntegrableWeight, HasTangentialDifferentialAt; contract scope replayed via verifier/gmt-compare.py contract_scope)`
- `grep -n "def blowUpMap|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|IsLocallyIntegrableMultiplicity" simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn "theorem simon_theorem_3_6|simon_remark_3_7_of_openSigmaFinite|ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite|def dimensionalUpperDensity|def dimensionalDensityQuotient|def IsBorelRegularOuterMeasure|def IsOpenSigmaFinite|measure_toOuterMeasure_isBorelRegular|realUnitBallVolume_pos" simongmt/Poincare/SimonGMT/Chapter01`
- `grep -rn "injective_area_formula_lipschitzOn|weighted_area_formula_lipschitzOn_fiberSum|def weightedAreaFiberSum|def areaFiber|areaJacobianWithin|euclideanHausdorffMeasure_image_le_of_lipschitzOn|nullMeasurableSet_image_of_lipschitzOn|rademacher_ae_differentiableAt|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure" simongmt/Poincare/SimonGMT/Chapter02`
- `rg -n "euclideanHausdorffMeasure_homothety_image|euclideanHausdorffMeasure_homothety_preimage|euclideanHausdorffMeasure_smul₀|Isometry.euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n "normDet_sq|euclideanHausdorffMeasure_image_eq_normDet_mul_volume|hausdorffMeasure_image" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "ae_tendsto_average_norm_sub|tendsto_filterAt|ae_tendsto_rnDeriv" mathlib/Mathlib/MeasureTheory/Covering`
- `rg -n "ae_differentiableWithinAt_of_mem|LipschitzWith.ae_differentiableAt" mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n "isOpen_biUnion_countable|ae_ball_iff|isCompact_closure|addHaar_closedBall|image_of_continuousOn_injOn|exists_antilipschitzWith|finrank_range_of_inj|integral_inter_add_sdiff₀|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|exists_measurable_subset_ae_eq|ContDiffAt.exists_lipschitzOnWith|continuousOn_fderiv_of_isOpen|lipschitzOnWith_of_nnnorm_fderiv_le|tendsto_integral_filter_of_dominated_convergence|integral_comp_smul|integral_withDensity_eq_integral_smul|measurable_fderiv" mathlib/Mathlib`
- `lake env lean GMT/Scratch/ChartCheckAvail*.lean (#check availability of every cited lemma after `import GMT.Ch03.Submission`)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`

Snapshot manifest: project d09bc8a (Contract.lean byte-identical to the workspace), Mathlib 25730c7c, plus the pinned simongmt package. Found and cited by the children: SimonGMT blowUpMap, HasApproximateTangentSpaceAt (Def. 1.4) and HasWeightedApproximateTangentSpaceAt (Def. 1.7). Also cited: SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn (F2) and nullMeasurableSet_image_of_lipschitzOn (Simon 1.8(i)), and weighted_area_formula_lipschitzOn_fiberSum (injective area formula on an open Lipschitz domain; needs import Chapter02.AreaDomain). Also: the density machinery ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite / simon_remark_3_7_of_openSigmaFinite (Simon 1.3.6, 3.7(2); needs import Chapter01.DensityComparison), with measure_toOuterMeasure_isBorelRegular and simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (needs import Chapter02.AreaLiteral). Mathlib: euclideanHausdorffMeasure_homothety_image/_preimage, Isometry.euclideanHausdorffMeasure_image, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume, ContinuousLinearMap.normDet_sq, VitaliFamily.ae_tendsto_average_norm_sub with Besicovitch.vitaliFamily/tendsto_filterAt, and LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher). Further Mathlib lemmas: MeasurableSet.image_of_continuousOn_injOn (Lusin-Souslin), Measure.addHaar_closedBall, LinearMap.exists_antilipschitzWith, Convex.lipschitzOnWith_of_nnnorm_fderiv_le, ContDiffAt.exists_lipschitzOnWith, tendsto_integral_filter_of_dominated_convergence, Measure.integral_comp_smul, integral_withDensity_eq_integral_smul, TopologicalSpace.isOpen_biUnion_countable and ae_ball_iff. Every Mathlib lemma cited is visible after `import GMT.Ch03.Submission` (checked with #check). No match in the snapshot for: a ready-made 'C¹ chart image has the classical tangent plane as approximate tangent space' lemma, a weighted locality lemma for approximate tangent planes, a blow-up change-of-variables lemma for blowUpMap, or a ρⁿ-normalized Lebesgue-point lemma for Hⁿ⌞S. These are supplied as children blowup_scaling, chart_blowup_tangent, weighted_tangent_combination and lebesgue_points. SimonGMT's Chapter03 Differential.lean tangential notions are not used.
