# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- Child DAG node: `root.density_one_implies_regular-a1.imrep_mass_and_support-a1.action_integral_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (Simon Ch. 6, 3.1 (‡) and 3.2(3)). The parent bounds the integrand with the Euclidean bound of its step 1. Here the same bound is used in operator-norm form, which avoids the Cauchy–Binet computation.
Notation: M = R.carrier, θ = R.mult, ξ = R.orient, ν := μHE[n].restrict M = Hⁿ⌞M, μ := R.measure = ν.withDensity (x ↦ (θ(x) : ℝ≥0∞)), f(x) := ξ(x)(ω(x)), K := tsupport ω. For an n-covector α, ‖α‖ is its operator norm as a continuous alternating map.
1. ω is C^∞, hence continuous, and has compact support. So K is compact, closed and Borel, and K ⊆ U because ω ∈ 𝒟ⁿ(U).
2. θ is measurable (R.measurable_mult; ℕ carries the discrete σ-algebra), so x ↦ (θ(x) : ℝ≥0) is measurable. A measure with a density is absolutely continuous, so μ ≪ ν (withDensity_absolutelyContinuous).
3. (Measurability.) ξ is ν-a.e. strongly measurable (R.aestronglyMeasurable_orient), hence μ-a.e. strongly measurable since μ ≪ ν. ω is continuous, hence strongly measurable. Evaluation Λₙ × Λⁿ → ℝ, (ζ, α) ↦ ζ(α), is continuous (bounded bilinear; isBoundedBilinearMap_apply.continuous). So f is μ-a.e. strongly measurable (Continuous.comp_aestronglyMeasurable₂).
4. (Pointwise bound.)
 - By R.orients, for ν-a.e. x (hence μ-a.e. x) there are an orthonormal family τ and s ∈ {1, −1} with ξ(x)(α) = s·α(τ) for all α. Then |f(x)| = |ω(x)(τ)| ≤ ‖ω(x)‖·∏_j ‖τ_j‖ = ‖ω(x)‖ (ContinuousAlternatingMap.le_opNorm).
 - Since ω is continuous with compact support, there is C with ‖ω(x)‖ ≤ C for all x (Continuous.bounded_above_of_compact_support).
 - If x ∉ K then ω(x) = 0, so f(x) = ξ(x)(0) = 0.
 Hence |f| ≤ C·1_K μ-a.e.
5. (Finiteness.) Since K is measurable, μ(K) = ∫_K θ dν = ∫_{M∩K} θ dHⁿ. This is finite by R.locallyIntegrable_mult, as K is compact and K ⊆ U. So C·1_K is μ-integrable, and by step 3 and domination (Integrable.mono'), f is μ-integrable.
6. (Integral identity.) For measurable g : ℝ^P → ℝ≥0 and any function h, ∫ h d(ν.withDensity g) = ∫ g(x)·h(x) dν(x). This is integral_withDensity_eq_integral_smul and needs no integrability hypothesis. Take g = θ, noting (θ(x) : ℝ≥0∞) = ((θ(x) : ℝ≥0) : ℝ≥0∞). Then
 ∫ f dμ = ∫ θ(x)·f(x) dν(x) = ∫_M θ(x)·ξ(x)(ω(x)) dHⁿ(x) = R.action ω.
 Together with step 5 this proves both claims. (A machine-checked Lean proof of exactly this argument exists: /tmp/imrep-ms-decomp/C2Check.lean.)

## Key steps

1. f(x) = ξ(x)(ω(x)) is μ_R-a.e. strongly measurable: ξ is, μ_R ≪ Hⁿ⌞M, and evaluation is continuous.
2. μ_R-a.e. |f| ≤ ‖ω‖ ≤ C·1_{spt ω}, because ξ(x) = ±ev_τ with τ orthonormal.
3. μ_R(spt ω) = ∫_{M∩spt ω} θ dHⁿ < ∞ by locallyIntegrable_mult, so f is integrable.
4. ∫ f dμ_R = ∫_M θ f dHⁿ = R.action ω by the withDensity integral formula.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n -i lusin <snapshot>/mathlib/Mathlib (also -l)`
- `rg -n 'TietzeExtension' <snapshot>/mathlib/Mathlib (Topology/TietzeExtension.lean, Analysis/Complex/Tietze.lean)`
- `rg -n 'exists_hasCompactSupport_integral_sub_le|exists_hasCompactSupport_eLpNorm_sub_le' <snapshot>/mathlib/Mathlib`
- `rg -n 'dist_normed_convolution_le|convolution_tendsto_right' <snapshot>/mathlib/Mathlib`
- `rg -n 'instance.*Regular|InnerRegularCompactLTTop' Mathlib/MeasureTheory/Measure/Regular.lean Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `sed -n 1,80p Mathlib/MeasureTheory/Measure/Support.lean | rg 'def|theorem|lemma' (Measure.support, mem_support_iff_forall)`
- `rg -n 'exists_cthickening_subset_open|closure_eq_iInter_thickening|cthickening_eq_iInter_thickening' Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'le_of_forall_nnreal_lt|le_of_forall_pos_le_add' Mathlib/Basic/ENNReal`
- `rg -n 'integral_indicator_one|integral_withDensity_eq_integral_smul|withDensity_absolutelyContinuous|exists_measurable_superset_of_null|AbsolutelyContinuous.ae_le|comp_aestronglyMeasurable₂|image_eq_zero_of_notMem_tsupport' <snapshot>/mathlib/Mathlib`
- `rg -n 'covectorEuclideanNorm' lake-packages-25730c7c/simongmt/Poincare/SimonGMT; rg -n '^(theorem|lemma|def|abbrev) ' Chapter06/{WedgeForms,FormsDuality,GeometricPointProduct,Representation}.lean`
- `grep -rln FormsDuality simongmt (not imported by the Ch07 contract)`
- `grep dor_ims_{unitOrientation_dual,action_eq_integral,massOn_le_measure,lusin_continuousOn,smooth_unit_approx,measure_le_massOn,support_of_massOn_eq} in dag.json, simongmt/Poincare, GMT/, mathlib/Mathlib (no match)`
- `lake env lean /tmp/imrep-ms-decomp/Parent.lean; Children.lean; Sanity.lean; C2Check.lean; C4Skeleton.lean; final/Final.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-support-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Tietze.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/imrep-ms-decomp/final/Final.lean`
- `/tmp/imrep-ms-decomp/final/statements.json`
- `/tmp/imrep-ms-decomp/C2Check.lean`
- `/tmp/imrep-ms-decomp/Sanity.lean`
- `/tmp/imrep-ms-decomp/C4Skeleton.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reusable facts found:
- SimonGMT Chapter06/Mass.lean: covectorEuclideanNorm, massAdmissibleOn, GeometricCurrentOn.massOn and le_massOn.
- Chapter06/CurrentLocalEquality.lean: VanishesOn, zeroRegion and support (spt T = U ∖ zeroRegion).
- Chapter06/FormsDuality.lean: wedgeCovectors and wedgeCovectors_apply_det give the coordinate covectors dx^I and the frame covector δ_τ used in the Cauchy–Binet child. The module is not imported by the Ch07 contract, so it must be imported in Submission.
- Mathlib: Measure.mem_support_iff_forall; finite measures on completely metrizable spaces are InnerRegular (RegularityCompacts.lean); Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure.
- Mathlib Tietze: ContinuousMap.exists_restrict_eq with RCLike.instTietzeExtensionTVS for finite-dimensional real spaces.
- Mathlib bump functions: ContDiffBump.dist_normed_convolution_le and convolution_tendsto_right_of_continuous.
- Mathlib Integrable.exists_hasCompactSupport_integral_sub_le (not needed on the chosen route).
- Mathlib measure and topology API: IsCompact.exists_cthickening_subset_open, tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop, ENNReal.le_of_forall_nnreal_lt, integral_withDensity_eq_integral_smul, integral_indicator_one, Continuous.comp_aestronglyMeasurable₂ (with isBoundedBilinearMap_apply.continuous).

Not available:
- Lusin's continuity theorem. Only Lusin–Souslin and Lusin separation are present (Polish/Basic.lean), so it becomes the child lusin_covector.
- The mass formula M_W(T) = μ_T(W) for the contract's Euclidean coefficient norm. Chapter06/Representation.lean has only the assumed comass MassRepresentation field.
- A Cauchy–Binet / exterior-power coefficient expansion for continuous alternating maps.

Lean checks:
- All seven exact child types elaborate in the comparator scope, and `exact Submission.X` closes each.
- The parent assembly from C3, C4 and C5 type-checks, with sorryAx only from the stubs.
- C2 and C5 are fully proved with propext, Classical.choice and Quot.sound only.
- C3 is proved from the C1 and C2 types.
- C4 is proved from the types of C1, C2, Lusin and the smooth approximation.
- The seven dor_ims_* names have no matches anywhere.
