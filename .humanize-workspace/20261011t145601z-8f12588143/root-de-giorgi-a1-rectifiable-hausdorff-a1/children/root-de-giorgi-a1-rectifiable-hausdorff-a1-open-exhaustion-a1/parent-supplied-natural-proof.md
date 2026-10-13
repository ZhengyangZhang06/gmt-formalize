# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child DAG node: `root.de_giorgi-a1.rectifiable_hausdorff-a1.open_exhaustion-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 2 (localization), with all details supplied.

Notation.
- |·| is the Euclidean norm on ℝ^N, and Uᶜ := ℝ^N ∖ U.
- d(y) := inf{|y − z| : z ∈ Uᶜ} ∈ [0, ∞] is the extended distance from y to Uᶜ. If U = ℝ^N then d ≡ ∞. In Lean this is Metric.infEDist y Uᶜ.
- For i ∈ ℕ let c_i := 1/i ∈ (0, ∞], with the convention 1/0 = ∞. Thus c_i > 0 for every i.

1. Continuity. For all y, y′ ∈ ℝ^N and z ∈ Uᶜ we have |y − z| ≤ |y − y′| + |y′ − z|, hence d(y) ≤ d(y′) + |y − y′|. So d is 1-Lipschitz as a map into [0, ∞], and in particular continuous. The norm y ↦ |y| is also continuous.

2. Definition and openness. Put W_i := {y ∈ ℝ^N : |y| < i and c_i < d(y)}. W_i is the intersection of two sets: the preimage of the open set {t < i} under |·|, and the preimage of the open set {c_i < t} under d. By step 1 both are open, so W_i is open.

3. Compact closure.
   - Put K_i := {y : |y| ≤ i and c_i ≤ d(y)}. It is closed, being an intersection of preimages of closed sets under the continuous maps of step 1.
   - W_i ⊆ K_i, so closure(W_i) ⊆ K_i.
   - K_i ⊆ B̄_i(0), and closed balls of ℝ^N are compact (Heine–Borel).
   - Hence closure(W_i) is a closed subset of a compact set, so it is compact.

4. Closure inside U. Let y ∈ K_i and suppose y ∉ U. Then y ∈ Uᶜ, so d(y) = 0. But then c_i ≤ d(y) = 0 contradicts c_i > 0. Hence K_i ⊆ U, and therefore closure(W_i) ⊆ K_i ⊆ U.

5. ⋃_i W_i ⊆ U, because W_i ⊆ closure(W_i) ⊆ U for every i (step 4).

6. U ⊆ ⋃_i W_i.
   - Let y ∈ U. Since U is open, Uᶜ is closed and y ∉ Uᶜ.
   - Therefore d(y) > 0. Indeed, d(y) = 0 would put y in the closure of Uᶜ, which is Uᶜ itself.
   - Choose k ∈ ℕ with 1/k < d(y); this is possible because d(y) > 0, and necessarily k ≥ 1.
   - Choose m ∈ ℕ with m > |y|, and set i := max(k, m) + 1.
   - Then |y| < m < i. Also c_i = 1/i ≤ 1/k < d(y), since i ≥ k.
   - Hence y ∈ W_i.

7. By steps 2–6, every W_i is open, closure(W_i) is compact and contained in U, and ⋃_{i∈ℕ} W_i = U. ∎

## Key steps

1. Define W_i := {y : |y| < i and 1/i < infEdist(y, Uᶜ)}, with 1/0 = ∞
2. W_i is open because the norm and the extended distance to Uᶜ are continuous
3. closure(W_i) ⊆ K_i := {|y| ≤ i, 1/i ≤ infEdist(y, Uᶜ)}, a closed bounded and hence compact set
4. K_i ⊆ U because infEdist vanishes on Uᶜ while 1/i > 0
5. Every y ∈ U has positive distance to the closed set Uᶜ, so y ∈ W_i for large i; hence ⋃ W_i = U

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
