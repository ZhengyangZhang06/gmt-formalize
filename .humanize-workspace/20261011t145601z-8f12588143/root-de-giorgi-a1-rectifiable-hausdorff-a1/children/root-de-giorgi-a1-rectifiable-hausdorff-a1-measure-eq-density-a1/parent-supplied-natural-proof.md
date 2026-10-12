# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child DAG node: `root.de_giorgi-a1.rectifiable_hausdorff-a1.measure_eq_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 8 (equality), for measures finite on all compact sets. Ingredients: the Besicovitch differentiation theorem (Simon Ch. 1, Theorems 3.22–3.24; Mathlib Besicovitch.ae_tendsto_rnDeriv) and the Radon–Nikodym theorem (Mathlib Measure.withDensity_rnDeriv_eq).

Notation. ω_n := Lⁿ(B_1(0)) ∈ (0, ∞), being the measure of a nonempty bounded open set. Quotients are taken in [0, ∞].

1. Local finiteness. Every x ∈ ℝ^N has the compact neighbourhood B̄_1(x), which has finite μ- and σ-measure. So μ and σ are locally finite Borel measures on ℝ^N, and in particular σ is σ-finite.

2. Besicovitch differentiation. ℝ^N is a finite-dimensional normed space, so it has the Besicovitch covering property. For locally finite μ and σ, the Besicovitch differentiation theorem gives, for σ-a.e. x, μ(B̄_ρ(x))/σ(B̄_ρ(x)) → D(x) as ρ ↓ 0, where D := dμ/dσ is the Radon–Nikodym derivative.

3. Identification of the limit. Let x be a point at which the conclusion of step 2 and both density hypotheses hold; σ-a.e. x is such a point, being in the intersection of finitely many σ-full sets.
   - For ρ > 0 put c := ρⁿ ∈ (0, ∞).
   - Cancelling the finite nonzero factor c⁻¹ in [0, ∞] gives μ(B̄_ρ(x))/σ(B̄_ρ(x)) = [μ(B̄_ρ(x))/c]/[σ(B̄_ρ(x))/c].
   - As ρ ↓ 0 the numerator and the denominator both tend to ω_n. Division on [0, ∞] is continuous at (ω_n, ω_n) because ω_n ≠ 0 and ω_n ≠ ∞.
   - Hence μ(B̄_ρ(x))/σ(B̄_ρ(x)) → ω_n/ω_n = 1.

4. Limits in the Hausdorff space [0, ∞] are unique, so D(x) = 1 for σ-a.e. x.

5. Conclusion. Since μ ≪ σ and σ is σ-finite, the Radon–Nikodym theorem gives μ = D·σ, the measure B ↦ ∫_B D dσ. By step 4, D·σ = 1·σ = σ. Hence μ = σ. ∎

## Key steps

1. Measures finite on compacts are locally finite, and σ is σ-finite
2. Besicovitch: μ(B̄_ρ(x))/σ(B̄_ρ(x)) → dμ/dσ(x) for σ-a.e. x
3. The ratio equals (μ(B̄_ρ)/ρⁿ)/(σ(B̄_ρ)/ρⁿ) → ω_n/ω_n = 1
4. Uniqueness of limits gives dμ/dσ = 1 σ-a.e.
5. Radon–Nikodym: μ = (dμ/dσ)·σ = σ

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `grep -n 'def HasApproxTangentPlaneWithMultiplicity|def ApproximateTangentCharacterization' <snapshot>/project/GMT/Ch03/Contract.lean`
- `grep -rn 'simon_theorem_3_3|def dimensionalUpperDensity|def dimensionalDensityQuotient|def realUnitBallVolume|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'def IsBorelRegularOuterMeasure|theorem measure_toOuterMeasure_isBorelRegular' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `grep -n 'def simonHausdorffOuterMeasureReal|def simonHausdorffMeasureReal|theorem simonHausdorffMeasureReal_toOuterMeasure' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `grep -n 'theorem realUnitBallVolume_nat_eq|theorem volume_euclidean_ball_eq' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `grep -rn 'dimensionalUpperDensity.*≤ |2 ^ n' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01 (no 2^n upper-density bound present)`
- `grep -n 'def CountablyRectifiable|theorem countablyRectifiable_of_measure_zero|theorem countablyRectifiable_iUnion|def blowUpMap|def HasApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'theorem ae_tendsto_rnDeriv|theorem tendsto_filterAt|protected def vitaliFamily' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -rn 'theorem withDensity_rnDeriv_eq' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Decomposition`
- `grep -rn 'theorem restrict_iUnion_congr|exists_iUnion_isCompact|IsOpen.exists_iUnion_' <snapshot>/mathlib/Mathlib (restrict_iUnion_congr found; no ready-made exhaustion lemma for open subsets)`
- `grep -n 'theorem addHaar_closedBall|theorem addHaar_ball_of_pos|theorem addHaar_closedBall_eq_addHaar_ball' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `sed -n 1,200p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_def, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_smul₀, euclideanHausdorffMeasure_homothety_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -n 'theorem _root_.Set.measure_eq_iInf_isOpen' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `grep -rn 'theorem.*infEDist_zero|theorem.*infEDist_pos' <snapshot>/mathlib/Mathlib/Topology`
- `sed -n 560,640p book/chapter-01.txt (Simon Thm 3.3) and book/chapter-03.txt (Thm 4.3 proof, line 604)`
- `python3 -I dag.json lean_name collision check (143 nodes): none`
- `python3 -I verifier/gmt-compare.py child_modules(contract mode) and verifier/lean_contract.py validate_lean_statement on the 10 statements; lake env lean on the 10 generated NodeChallenge files: all OK`
- `lake env lean GMT/Scratch/RectifiableHausdorffSplitDecision.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/RectifiableHausdorffSplitDecision.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). Neither Mathlib nor the pinned SimonGMT contains this statement, the 2^n upper-density covering bound (only the reverse comparison, simon_theorem_3_3, is present), a vague-limit-to-plane squeeze, or a ready-made exhaustion of open subsets. Those become children. The children's proofs can draw on the following library facts: Besicovitch.ae_tendsto_rnDeriv; Measure.withDensity_rnDeriv_eq (needs import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym); Measure.restrict_iUnion_congr; Set.measure_eq_iInf_isOpen with OuterRegular inferred from IsFiniteMeasureOnCompacts; Measure.addHaar_closedBall; Isometry.euclideanHausdorffMeasure_image; euclideanHausdorffMeasure_smul₀; EuclideanSpace.euclideanHausdorffMeasure_eq_volume; Metric.infEDist lemmas; SimonGMT simon_theorem_3_3, measure_toOuterMeasure_isBorelRegular, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, simonHausdorffMeasureReal_toOuterMeasure, volume_euclidean_ball_eq, countablyRectifiable_iUnion and countablyRectifiable_of_measure_zero. All ten child types elaborate in the exact NodeChallenge scope. The scratch assembly compiles the parent and the core child against stubs. Five children are already proved there with standard axioms only.
