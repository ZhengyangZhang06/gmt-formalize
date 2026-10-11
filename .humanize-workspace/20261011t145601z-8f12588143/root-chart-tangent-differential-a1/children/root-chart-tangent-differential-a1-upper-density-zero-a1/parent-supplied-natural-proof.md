# Parent-supplied natural-language proof

- Parent DAG node: `root.chart_tangent_differential-a1`
- Child DAG node: `root.chart_tangent_differential-a1.upper_density_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 1, Theorem 3.6 (Upper Density Theorem) and Remark 3.7(2) (chapter-01.txt lines 700-715), used in the parent proof Step 3 for (P1) (measure ν₁ = θHⁿ⌞(M ∖ Σ), set M ∖ Σ) and (P2) (measure Hⁿ⌞Σ, set Σ ∖ M). SimonGMT Chapter01: ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite (the a.e. form of simon_remark_3_7_of_openSigmaFinite), measure_toOuterMeasure_isBorelRegular, realUnitBallVolume_pos, realUnitBallVolume_ne_top; SimonGMT Chapter02: simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure. Import note: the density theorem lives in Poincare.SimonGMT.Chapter01.DensityComparison and the normalization identity in Poincare.SimonGMT.Chapter02.AreaLiteral, which GMT.Ch03.Submission does not import; the formalization adds these two imports (prebuilt, pinned package; the verifier allows extra imports in the Submission and new files under GMT/Ch03/, and the frozen statements elaborate identically with them).

1. Borel kernel. Since A is Hⁿ-null-measurable, there is a Borel set A₀ ⊆ A with Hⁿ(A ∖ A₀) = 0 (Mathlib NullMeasurableSet.exists_measurable_subset_ae_eq). Every x ∉ A satisfies x ∉ A₀.

2. The measure ν. Let ν be the Borel measure on ℝ^N with ν(E) = ∫_{E ∩ A₀} |w| dHⁿ for Borel E, i.e. ν = (Hⁿ⌞A₀) with density |w| (Mathlib (μHE[n].restrict A₀).withDensity (fun z ↦ ‖w z‖ₑ)). For each k ∈ ℕ, ν(B_k(0)) ≤ ∫_{A ∩ B̄_k(0)} |w| dHⁿ < ∞ by the hypothesis with the compact set K = B̄_k(0) (A₀ ⊆ A). The open balls B_k(0) cover ℝ^N, so ν is open-σ-finite (SimonGMT IsOpenSigmaFinite). Moreover ν(ℝ^N ∖ A₀) = 0, hence ν(A₀ ∩ E) = ν(E) for every set E.

3. ν is Borel regular as an outer measure (SimonGMT Chapter01.measure_toOuterMeasure_isBorelRegular, for any Mathlib measure on a Borel space); in particular Borel sets, such as A₀, are Carathéodory-measurable for ν.

4. Density theorem. Apply Simon's Upper Density Theorem 3.6 in the form of Remark 3.7(2) (SimonGMT ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite, with the outer measure of ν, the real dimension (n : ℝ) ≥ 0, and the set A₀; hypotheses from steps 2-3): for simonHausdorffMeasureReal n-a.e. x, x ∉ A₀ implies Θ^{*n}(ν, A₀, x) = 0, where Θ^{*n}(ν, A₀, x) = limsup_{ρ↓0} q(ρ), q(ρ) := ν(A₀ ∩ B̄_ρ(x)) / (ω_n · ENNReal.ofReal(ρ)ⁿ) (SimonGMT dimensionalUpperDensity, closed balls), with ω_n := realUnitBallVolume n ∈ (0, ∞) (realUnitBallVolume_pos, realUnitBallVolume_ne_top). Since simonHausdorffMeasureReal (n : ℝ) = μHE[n] = Hⁿ (SimonGMT simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure), this holds for Hⁿ-a.e. x.

5. Conclusion at such a point. Fix x ∉ A with Θ^{*n}(ν, A₀, x) = 0 (Hⁿ-a.e. x ∉ A qualifies by steps 1 and 4). Since q ≥ 0 and limsup q = 0, q(ρ) → 0 as ρ ↓ 0 (e.g. tendsto_of_le_liminf_of_limsup_le). For 0 < ρ ≤ 1: |w| is integrable on A ∩ B_ρ(x) ⊆ A ∩ B̄_1(x) (compact); A ∩ B_ρ(x) and A₀ ∩ B_ρ(x) differ by an Hⁿ-null set; and the real (Bochner) integral of a nonnegative integrable function is the toReal of its lower Lebesgue integral. Hence ∫_{A ∩ B_ρ(x)} |w| dHⁿ = ∫_{A₀ ∩ B_ρ(x)} |w| dHⁿ = ν(B_ρ(x)) (finite) ≤ ν(B̄_ρ(x)) = ν(A₀ ∩ B̄_ρ(x)) = ω_n ρⁿ q(ρ) (using ENNReal.ofReal(ρ)ⁿ = ENNReal.ofReal(ρⁿ) for ρ > 0). Therefore 0 ≤ ρ^{-n}∫_{A ∩ B_ρ(x)} |w| dHⁿ ≤ ω_n·q(ρ) → 0 (as real numbers, ω_n < ∞), which is the claim. (For n = 0, H⁰ is the counting measure and ω_0 = 1; the argument applies verbatim. Hⁿ need not be σ-finite on ℝ^N: Simon's theorem bounds the Hausdorff outer measure of the exceptional set directly.) ∎

## Key steps

1. Replace A by a Borel kernel A₀ ⊆ A with Hⁿ(A ∖ A₀) = 0.
2. ν := |w|·Hⁿ⌞A₀ is Borel-regular (measure_toOuterMeasure_isBorelRegular), open-σ-finite (local integrability) and concentrated on A₀.
3. Simon's Upper Density Theorem 3.6 + Remark 3.7(2) (SimonGMT ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite, import Chapter01.DensityComparison): Θ^{*n}(ν, A₀, x) = 0 for Hⁿ-a.e. x ∉ A₀; Simon's Hⁿ equals μHE[n] (import Chapter02.AreaLiteral).
4. ρ^{-n}∫_{A∩B_ρ(x)} |w| dHⁿ = ρ^{-n}ν(B_ρ(x)) ≤ ω_n ν(A₀ ∩ B̄_ρ(x))/(ω_nρⁿ) → 0.

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
