# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child DAG node: `root.de_giorgi-a1.rectifiable_hausdorff-a1.plane_ball_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 1 (n-planes).

Notation. Hⁿ := μHE[n]; Lⁿ is Lebesgue measure (volume) on ℝⁿ = Rn n; ω_n := Lⁿ(B_1(0)). Each ball is taken in the space indicated.

1. Isometric parametrization of P.
   - Since dim P = n, the subspace P, with the inner product of ℝ^N, has an orthonormal basis (v_1, …, v_n). For instance, take the standard orthonormal basis of P and reindex it by {1, …, n} using dim P = n.
   - Let e : P → ℝⁿ be the coordinate isomorphism of this basis. It is a linear isometric isomorphism.
   - Put ι := (inclusion P ↪ ℝ^N) ∘ e⁻¹ : ℝⁿ → ℝ^N.
   - Then ι is linear, |ι(t)| = |t| for every t (so ι is an isometry), and ι(ℝⁿ) = P.

2. P ∩ B̄_s(0) = ι(B̄_s(0)), where the second ball is in ℝⁿ.
   - If y ∈ P and |y| ≤ s, then t := e(y) satisfies |t| = |y| ≤ s and ι(t) = y.
   - Conversely, if t ∈ ℝⁿ with |t| ≤ s, then ι(t) ∈ P and |ι(t)| = |t| ≤ s.

3. Isometry invariance. Hausdorff measure is invariant under isometric maps (Mathlib Isometry.euclideanHausdorffMeasure_image). So Hⁿ(ι(B̄_s(0))) = Hⁿ(B̄_s(0)), the latter computed in ℝⁿ.

4. On ℝⁿ the measure Hⁿ coincides with Lⁿ (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). So Hⁿ(B̄_s(0)) = Lⁿ(B̄_s(0)).

5. Scaling. Lⁿ is an additive Haar measure on the n-dimensional space ℝⁿ, so for s ≥ 0, Lⁿ(B̄_s(0)) = sⁿ·Lⁿ(B_1(0)) = sⁿω_n (Mathlib Measure.addHaar_closedBall, with dim ℝⁿ = n).
   - Dilation by s multiplies Lⁿ by sⁿ, and for n ≥ 1 the unit sphere is Lⁿ-null.
   - For n = 0, ℝ⁰ is a single point, both balls equal ℝ⁰, and both sides equal 1 = s⁰ω₀.

6. Combining steps 2–5: Hⁿ(P ∩ B̄_s(0)) = Hⁿ(ι(B̄_s(0))) = Lⁿ(B̄_s(0)) = sⁿω_n. In [0, ∞] the factor sⁿ is ofReal(sⁿ). ∎

## Key steps

1. An orthonormal basis of P gives a linear isometry ι: ℝⁿ → ℝ^N with range P
2. P ∩ B̄_s(0) = ι(B̄_s(0))
3. Hⁿ is invariant under isometries
4. Hⁿ = Lⁿ on ℝⁿ
5. Haar scaling gives Lⁿ(B̄_s(0)) = sⁿ·Lⁿ(B_1(0)) = sⁿω_n

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
