# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1`
- Child DAG node: `root.de_giorgi-a1.halfspace_rigidity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof Parts 3c, 3d (with the corrected sign, erratum E1) and the end of 3e; Simon, Ch. 3, proof of Theorem 4.3, chapter-03.txt lines 656-688 (∫_F D_iζ = 0 for i = 1, ..., n, "F = ℝⁿ × H", "H is non-decreasing", (9) corrected to F = {x^{n+1} > λ}) and line 733 ("(10) and (11) evidently tell us that λ = 0"). The parent's two mollification arguments (for the horizontal derivatives in 3c, and for "the distributional derivative of χ_H is a non-negative measure, so χ_H agrees a.e. with a non-decreasing function" in 3d) are carried out together, in coordinates adapted to e.

Notation. L^N = volume; u := χ_G (bounded, locally integrable); D_vζ(y) := Dζ(y)v (Lean fderiv ℝ ζ y v); φ_σ (σ > 0) an even standard mollifier (C^∞, ≥ 0, ∫φ_σ = 1, spt φ_σ ⊆ B̄_σ(0)); u_σ := φ_σ * u.

Step 0. N ≥ 1, because |e| = 1 while ℝ⁰ = {0}.

Step 1 (mollified derivatives; Simon (7)-(8) and the vertical sign). u_σ is C^∞ with 0 ≤ u_σ ≤ 1 and, differentiating under the integral sign, D_v u_σ(y) = ∫ u(z) (D_vφ_σ)(y − z) dz for all y, v. For fixed y, ζ_y(z) := φ_σ(y − z) is C^∞ with compact support, ζ_y ≥ 0, and D_vζ_y(z) = −(D_vφ_σ)(y − z). Hence D_v u_σ(y) = −∫_G D_vζ_y(z) dz. By (H), D_v u_σ ≡ 0 for every v with ⟨v, e⟩ = 0 (horizontal invariance); by (M), D_e u_σ(y) = −∫_G D_eζ_y ≥ 0 for every y (vertical monotonicity).

Step 2 (one-variable structure; "F = ℝⁿ × H"). For y ∈ ℝ^N let π(y) := y − ⟨y, e⟩e, so ⟨π(y), e⟩ = 0. Along the segment s ↦ ⟨y, e⟩e + sπ(y), s ∈ [0, 1], the derivative of u_σ is D_{π(y)}u_σ = 0, so u_σ(y) = u_σ(⟨y, e⟩e). Thus u_σ(y) = w_σ(⟨y, e⟩) with w_σ(t) := u_σ(te), a C^∞ function with values in [0, 1] and w_σ'(t) = D_e u_σ(te) ≥ 0; so w_σ is non-decreasing.

Step 3 (limit). By the Lebesgue differentiation theorem (u ∈ L¹_loc), u_{σ_j} → u a.e. for σ_j := 1/j (Mathlib ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable). Define w(t) := limsup_j w_{σ_j}(t) ∈ [0, 1]; as a pointwise limsup of non-decreasing functions, w is non-decreasing. For a.e. y, u(y) = lim_j w_{σ_j}(⟨y, e⟩) = w(⟨y, e⟩). Let Z := {y : u(y) ≠ w(⟨y, e⟩)}, an L^N-null set.

Step 4 (half-line; Simon (9) with the corrected inequality). Extend e to an orthonormal basis b_1, ..., b_{N−1}, b_N = e of ℝ^N and let T(z, t) := Σ_{i<N} z_i b_i + te. T is a linear isometry ℝ^{N−1} × ℝ → ℝ^N carrying L^{N−1} ⊗ L¹ to L^N (coordinate identification of ℝ^{N−1} × ℝ with ℝ^N followed by the linear isometry sending the standard basis to (b_1, ..., b_N); Mathlib LinearIsometryEquiv.measurePreserving), and ⟨T(z, t), e⟩ = t. Let Z' ⊇ Z be a Borel L^N-null set. By Fubini applied to the Borel set T⁻¹(Z'), for L¹-a.e. t the slice {z : T(z, t) ∈ Z'} is L^{N−1}-null, hence not all of ℝ^{N−1} (L^{N−1}(ℝ^{N−1}) > 0, also for N = 1); for such t pick z with T(z, t) ∉ Z' ⊇ Z, so w(t) = u(T(z, t)) ∈ {0, 1}. Thus w(t) ∈ {0, 1} for a.e. t. Let λ := sup{t ∈ ℝ : w(t) < 1/2} ∈ [−∞, +∞] (sup ∅ = −∞). By monotonicity w(t) ≥ 1/2 for t > λ and w(t) < 1/2 for t < λ; hence w = 1 a.e. on (λ, ∞) and w = 0 a.e. on (−∞, λ). Since u = w(⟨·, e⟩) off the null set Z', Fubini (via T, applied to Borel null supersets as above) gives u = 1 a.e. on {y : ⟨y, e⟩ > λ} and u = 0 a.e. on {y : ⟨y, e⟩ < λ}; for finite λ the hyperplane {⟨y, e⟩ = λ} is null. Therefore L^N(G Δ {y : ⟨y, e⟩ > λ}) = 0, with the conventions {⟨y, e⟩ > −∞} := ℝ^N and {⟨y, e⟩ > +∞} := ∅.

Step 5 (λ = 0). If λ > 0 (possibly λ = +∞), let R := min(λ, 1) > 0. Every y ∈ B_R(0) has ⟨y, e⟩ ≤ |y| < R ≤ λ, so B_R(0) ⊆ {⟨y, e⟩ < λ} and Step 4 gives L^N(G ∩ B_R(0)) = 0, contradicting (P). If λ < 0 (possibly λ = −∞), let R := min(−λ, 1) > 0; then B_R(0) ⊆ {⟨y, e⟩ > λ}, so L^N(B_R(0) ∖ G) = 0, again contradicting (P). Hence λ = 0, and L^N(G Δ {y : ⟨y, e⟩ > 0}) = 0. ∎

## Key steps

1. Mollify u = χ_G: D_v u_σ(y) = −∫_G D_v[φ_σ(y − ·)], so D_v u_σ ≡ 0 for v ⊥ e by (H) and D_e u_σ ≥ 0 by (M).
2. Hence u_σ(y) = w_σ(⟨y, e⟩) with w_σ non-decreasing; along σ_j → 0, u = w(⟨·, e⟩) a.e. with w = limsup w_{σ_j} non-decreasing.
3. Fubini in coordinates (z, t) adapted to e: w ∈ {0, 1} a.e., so G = {⟨y, e⟩ > λ} up to a null set, λ ∈ [−∞, ∞].
4. (P) in the ball B_{min(|λ|,1)}(0) rules out λ > 0 and λ < 0, so λ = 0.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `grep -n 'def IsGaussGreenPair|def normalAverage|def reducedBoundary|def reducedNormal|def HasApproxTangentPlaneWithMultiplicity|def DeGiorgiTheorem|def ApproximateTangentCharacterization|def GaussGreenRepresentation' <snapshot>/project/GMT/Ch03/Contract.lean`
- `grep -rn -i 'de.?giorgi|reducedBoundary' <snapshot>/mathlib/Mathlib .lake/packages/simongmt/Poincare`
- `grep -n -i 'compactness|arzela' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/*.lean`
- `grep -n 'def blowUpMap|def HasApproximateTangentSpaceAt|theorem countablyRectifiable_iUnion' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'def euclideanDivergence|support_euclideanDivergence_subset|euclideanDivergence_eq_sum_inner|def IsLocallyBV|isLocallyBV_of_locallyL1_of_uniform_bound' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `grep -rn 'simon_theorem_3_3|def dimensionalUpperDensity|def dimensionalDensityQuotient|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|def realUnitBallVolume' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'WeakDerivativesZero|constancyMollifier' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `grep 'theorem ae_tendsto_rnDeriv|theorem ae_tendsto_average|theorem tendsto_filterAt|protected def vitaliFamily' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering`
- `grep 'theorem Monotone.ae_differentiableAt|theorem eLpNorm_le_eLpNorm_fderiv_of_eq|theorem LipschitzWith.ae_differentiableAt|theorem tendsto_of_subseq_tendsto|theorem arzela_ascoli|theorem integral_Ioi_of_hasDerivAt_of_tendsto' <snapshot>/mathlib/Mathlib`
- `grep 'MonotoneOn.intervalIntegral_deriv_mem_uIcc|MonotoneOn.intervalIntegral_slope_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral`
- `grep 'StronglyMeasurable.integral_prod_right|measurable_measure_prodMk_left|measurableSet_exists_tendsto|StronglyMeasurable.limUnder' <snapshot>/mathlib/Mathlib`
- `grep 'euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety_image|measurePreserving_euclideanHausdorffMeasure|theorem hausdorffMeasure_image|notation "μHE[' <snapshot>/mathlib/Mathlib`
- `grep 'withDensity_rnDeriv_eq|addHaar_image_homothety|theorem addHaar_smul|ae_convolution_tendsto_right_of_locallyIntegrable|finrank_orthogonal_span_singleton|LinearIsometryEquiv.measurePreserving|tendsto_measure_iUnion_atTop|Filter.Tendsto.limUnder_eq|HasCompactSupport.contDiff_convolution_left|OrthonormalBasis.volume_parallelepiped' <snapshot>/mathlib/Mathlib`
- `python3 -I (importlib of verifier/gmt-compare.py) contract_scope(Contract.lean, 'GMT.Ch03.main_theorem') -> NodeChallenge prefix; lake env lean /tmp/dg-decomp/challenges/Challenge_*.lean (10 files), /tmp/dg-decomp/Assembly.lean, /tmp/dg-decomp/Interfaces.lean`
- `python3 -I lean_name collision check against dag.json (73 nodes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/StronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dg-decomp/Assembly.lean`
- `/tmp/dg-decomp/Interfaces.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). Neither Mathlib nor the pinned SimonGMT has a De Giorgi theorem, BV subsequence compactness, a Lipschitz Gauss–Green identity, density estimates for the reduced boundary, half-space rigidity, or measurability of the reduced boundary. SimonGMT FinitePerimeter.lean records only the definitions, and BV.lean states that subsequence extraction 'remains the compactness obligation'. These obligations therefore become children. Library facts located for the child proofs: Besicovitch differentiation (VitaliFamily.ae_tendsto_average, Besicovitch.ae_tendsto_rnDeriv, Besicovitch.tendsto_filterAt); the Gagliardo–Nirenberg–Sobolev inequality (eLpNorm_le_eLpNorm_fderiv_of_eq); Monotone.ae_differentiableAt and MonotoneOn.intervalIntegral_deriv_mem_uIcc; Rademacher; Arzelà–Ascoli; a.e. convergence of mollifiers; product measurability; μHE scaling and isometry invariance; SimonGMT simon_theorem_3_3 with simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure; countablyRectifiable_iUnion; WeakDerivativesZero. All ten child types elaborate in the exact NodeChallenge scope. The parent assembly and the sibling-interface checks compile against stubs, with propext, Classical.choice, Quot.sound and the stubs' sorryAx as the only axioms. No lean_name collides with dag.json.
