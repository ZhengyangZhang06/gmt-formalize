# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child DAG node: `root.de_giorgi-a1.rectifiable_hausdorff-a1.vague_unit_ball-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 3, together with the identical squeeze in Step 7, isolated as a statement about a family of measures. Step 1 is supplied by the sibling plane_ball_measure.

Notation and setup.
- Hⁿ := μHE[n], and ∫_P f dHⁿ is the integral of f over the set P with respect to Hⁿ.
- ω := ω_n := Lⁿ(B_1(0)), where Lⁿ is Lebesgue measure on ℝⁿ.
- 0 < ω < ∞: B_1(0) is a nonempty open set, which Lebesgue measure charges, and it is bounded.
- By hypothesis (i), choose r₀ > 0 with ν_r(B̄_2(0)) < ∞ for all r ∈ (0, r₀).

1. Cut-off functions. For τ ∈ (0, 1/2) define f_τ(y) := min{1, max{0, (1 + τ − |y|)/τ}} and g_τ(y) := min{1, max{0, (1 − |y|)/τ}}.
   - Both are continuous with values in [0, 1].
   - f_τ(y) = 1 for |y| ≤ 1 and f_τ(y) = 0 for |y| ≥ 1 + τ.
   - g_τ(y) = 1 for |y| ≤ 1 − τ and g_τ(y) = 0 for |y| ≥ 1.
   - Their supports lie in the compact ball B̄_{1+τ}(0), so f_τ, g_τ ∈ C_c(ℝ^N, ℝ).

2. Pointwise comparisons. From step 1, and since 1 + τ < 2:
   1_{B̄_{1−τ}(0)} ≤ g_τ ≤ 1_{B̄_1(0)} ≤ f_τ ≤ 1_{B̄_{1+τ}(0)} ≤ 1_{B̄_2(0)}.

3. Integrals over the plane.
   - By plane_ball_measure (dim P = n), Hⁿ(P ∩ B̄_s(0)) = sⁿω < ∞ for every s > 0.
   - In particular Hⁿ⌞P is finite on B̄_2(0). So f_τ, g_τ and the indicators of step 2 are integrable over P.
   - Monotonicity of the integral then gives
     ∫_P g_τ dHⁿ ≥ Hⁿ(P ∩ B̄_{1−τ}(0)) = (1 − τ)ⁿω, and
     ∫_P f_τ dHⁿ ≤ Hⁿ(P ∩ B̄_{1+τ}(0)) = (1 + τ)ⁿω.

4. Squeeze for a fixed r ∈ (0, r₀).
   - The functions f_τ, g_τ and 1_{B̄_1(0)} are bounded by 1_{B̄_2(0)}, whose ν_r-integral is finite. So all three are ν_r-integrable.
   - Hence a_r := ν_r(B̄_1(0)) ≤ ν_r(B̄_2(0)) is a finite real number, and it equals the real integral ∫ 1_{B̄_1(0)} dν_r.
   - By step 2 and monotonicity of the integral, ∫ g_τ dν_r ≤ a_r ≤ ∫ f_τ dν_r.

5. Passage to the limit.
   - By hypothesis (ii), ∫ g_τ dν_r → ∫_P g_τ dHⁿ and ∫ f_τ dν_r → ∫_P f_τ dHⁿ as r ↓ 0.
   - Let ε > 0. Since (1 ± τ)ⁿω → ω as τ ↓ 0 (for n = 0 they already equal ω), fix τ ∈ (0, 1/2) with (1 − τ)ⁿω > ω − ε and (1 + τ)ⁿω < ω + ε.
   - By step 3, ∫_P g_τ dHⁿ > ω − ε and ∫_P f_τ dHⁿ < ω + ε.
   - So there is r₁ ∈ (0, r₀] such that for all r ∈ (0, r₁) we have ∫ g_τ dν_r > ω − ε and ∫ f_τ dν_r < ω + ε.
   - By step 4, ω − ε < a_r < ω + ε for all r ∈ (0, r₁).

6. Conclusion. By step 5, the real numbers a_r = ν_r(B̄_1(0)), for r ∈ (0, r₀), converge to ω as r ↓ 0. On (0, r₀) the value ν_r(B̄_1(0)) ∈ [0, ∞] equals the finite number a_r, and the inclusion of [0, ∞) into [0, ∞] is continuous. Hence ν_r(B̄_1(0)) → ω = ω_n in [0, ∞] as r ↓ 0. ∎

## Key steps

1. Cut-offs f_τ, g_τ ∈ C_c with 1_{B̄_{1−τ}} ≤ g_τ ≤ 1_{B̄_1} ≤ f_τ ≤ 1_{B̄_{1+τ}} ≤ 1_{B̄_2}
2. By plane_ball_measure, ∫_P g_τ dHⁿ ≥ (1−τ)ⁿω_n and ∫_P f_τ dHⁿ ≤ (1+τ)ⁿω_n
3. For small r all integrands are integrable and ∫ g_τ dν_r ≤ ν_r(B̄_1(0)) ≤ ∫ f_τ dν_r
4. Letting r ↓ 0 with hypothesis (ii) traps ν_r(B̄_1(0)) in (ω_n − ε, ω_n + ε) for τ small
5. Convert the real limit to convergence in [0, ∞]

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
