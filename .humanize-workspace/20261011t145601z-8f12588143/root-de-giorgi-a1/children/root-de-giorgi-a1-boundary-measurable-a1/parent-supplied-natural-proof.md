# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1`
- Child DAG node: `root.de_giorgi-a1.boundary_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof Part 5b (needed so that Hⁿ⌞∂*E is a restriction to a Borel set); this is the argument Simon uses for Borel measurability of densities, Ch. 1, §3, chapter-01.txt lines 575-592 (semicontinuity in the centre and monotone dependence on the radius reduce the limit to countably many radii).

Notation. B_ρ(x) open ball; a_x(ρ) := normalAverage μ ν x ρ = μ(B_ρ(x)).toReal⁻¹ • ∫_{B_ρ(x)} ν dμ; ∂* := reducedBoundary U μ ν ⊆ U.

Step 1 (σ-finiteness). U is the increasing union of the compact sets K_i := {y : |y| ≤ i, infEdist(y, Uᶜ) ≥ 1/i} ⊆ U (i ≥ 1; Uᶜ is closed, and infEdist(y, ∅) = ∞); μ(K_i) < ∞ and μ(Uᶜ) = 0, so μ is σ-finite, in particular s-finite.

Step 2 (a measurable version of ν). Choose a strongly measurable ν̃ with ν̃ = ν μ-a.e. Then ∫_B ν dμ = ∫_B ν̃ dμ for every Borel B, so a_x(ρ) is the same for ν and ν̃ and ∂* = reducedBoundary U μ ν̃; also |ν̃| = 1 μ-a.e.

Step 3 (measurability in x for fixed ρ). The set D_ρ := {(x, y) : dist(x, y) < ρ} is open in ℝ^N × ℝ^N, hence measurable for the product σ-algebra (ℝ^N is second countable). By Step 1 and the measurability part of Fubini-Tonelli (Mathlib measurable_measure_prodMk_left, MeasureTheory.StronglyMeasurable.integral_prod_right), x ↦ μ(B_ρ(x)) = μ({y : (x, y) ∈ D_ρ}) is measurable, and x ↦ ∫_{B_ρ(x)} ν̃ dμ = ∫ 1_{D_ρ}(x, y)ν̃(y) dμ(y) is strongly measurable (this is the Bochner integral, equal to 0 when the integrand is not integrable, consistently with the definition of normalAverage). Hence x ↦ a_x(ρ) is measurable for each fixed ρ.

Step 4 (left continuity in ρ). Let x ∈ U and choose ρ_x > 0 with B̄_{ρ_x}(x) ⊆ U, so μ(B_ρ(x)) ≤ μ(B̄_{ρ_x}(x)) < ∞ for ρ ≤ ρ_x. Let ρ ∈ (0, ρ_x] and ρ' ↑ ρ. Then B_{ρ'}(x) ↑ B_ρ(x), so μ(B_{ρ'}(x)) → μ(B_ρ(x)) (continuity from below) and ∫_{B_{ρ'}(x)} ν̃ dμ → ∫_{B_ρ(x)} ν̃ dμ (dominated convergence: |ν̃| ≤ 1 a.e., finite measure). If μ(B_ρ(x)) > 0, the map t ↦ t⁻¹ is continuous at μ(B_ρ(x)).toReal > 0, so a_x(ρ') → a_x(ρ). If μ(B_ρ(x)) = 0, then μ(B_{ρ'}(x)) = 0 and a_x(ρ') = 0 = a_x(ρ) for all ρ' ≤ ρ. So ρ ↦ a_x(ρ) is left-continuous on (0, ρ_x].

Step 5 (countable characterization). For x ∈ U the following are equivalent:
 (A) there is v with |v| = 1 and a_x(ρ) → v as ρ ↓ 0;
 (B) for every integer m ≥ 1 there is an integer j ≥ 1 with |a_x(q) − a_x(q')| ≤ 1/m for all rationals q, q' ∈ (0, 1/j), and the limit L(x) := lim_{j→∞} a_x(1/j) (which exists under the preceding Cauchy condition) satisfies |L(x)| = 1.
 (A) ⇒ (B): convergence implies the Cauchy condition along rationals, and L(x) = v. (B) ⇒ (A): given m, take j from (B), enlarged so that 1/j ≤ ρ_x (the condition persists for larger j). For real ρ, ρ' ∈ (0, 1/j) choose rationals q_i ↑ ρ and q_i' ↑ ρ' in (0, 1/j); by Step 4, |a_x(ρ) − a_x(ρ')| = lim_i |a_x(q_i) − a_x(q_i')| ≤ 1/m. Thus a_x satisfies the Cauchy criterion as ρ ↓ 0 in the complete space ℝ^N and converges to some v; necessarily v = lim_j a_x(1/j) = L(x), so |v| = 1.

Step 6 (measurability). Let C := ⋂_{m≥1} ⋃_{j≥1} ⋂_{q, q' ∈ ℚ ∩ (0, 1/j)} {x : |a_x(q) − a_x(q')| ≤ 1/m}, a countable combination of measurable sets (Step 3). Put L(x) := limUnder atTop (j ↦ a_x(1/(j+1))); as a limit of measurable functions it is measurable (Mathlib StronglyMeasurable.limUnder, measurableSet_exists_tendsto), and on C it equals the limit in (B). By Step 5 (∂* ⊆ U by definition), ∂* = U ∩ C ∩ {x : |L(x)| = 1}, an intersection of an open set and two measurable sets. Hence reducedBoundary U μ ν is measurable. ∎

## Key steps

1. μ is σ-finite (μ(Uᶜ) = 0, U σ-compact); replacing ν by a strongly measurable version does not change normalAverage or the reduced boundary.
2. For fixed ρ, x ↦ μ(B_ρ(x)) and x ↦ ∫_{B_ρ(x)}ν dμ are measurable (product measurability of {dist < ρ}), so x ↦ normalAverage(x, ρ) is measurable.
3. For x ∈ U, ρ ↦ normalAverage(x, ρ) is left-continuous on (0, ρ_x] (continuity from below and dominated convergence).
4. Hence x ∈ ∂*E iff x ∈ U, the Cauchy condition holds along rational radii and |lim_j normalAverage(x, 1/j)| = 1, a countable measurable description.

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
