# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.good_center-a1.periodic_maximal-a1`
- Child DAG node: `root.deformation-a1.good_center-a1.periodic_maximal-a1.tubes_disjoint-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof. It proves Simon's parenthetical claim (Ch. 6, §5, p. 164) that 'p_j⁻¹B_{σ_ℓ}(b_ℓ + z), ℓ = 1, 2, …, z ∈ ℤ^{n+ℓ} ∩ S_j, is a pairwise disjoint collection'. Here the claim is proved for the periodic open sets in E, before pulling back by the projection; in the parent, U(b, σ_b) = ⋃_z B_{σ_b}(b + z) and T(b, σ_b) = p⁻¹(U(b, σ_b)).

Notation. For y, g ∈ E and z ∈ ℤ^ι, write g + z and y − z for the points of E with coordinates g_i + z_i and y_i − z_i. Regard z itself as the point of E with coordinates z_i. |v| = (Σ_i v_i²)^{1/2} is the Euclidean norm, and B̄_ρ(c) = {w ∈ E : |w − c| ≤ ρ}.

1. Squared distances. For y, g ∈ E and z ∈ ℤ^ι, the vector y − (g + z) has coordinates y_i − g_i − z_i, so |y − (g + z)|² = Σ_{i∈ι}(y_i − g_i − z_i)². Let τ > 0 with Σ_i(y_i − g_i − z_i)² < τ². Then |y − (g + z)| < τ: otherwise |y − (g + z)| ≥ τ > 0 would give |y − (g + z)|² ≥ τ².
2. Setup. Suppose, for a contradiction, that y ∈ U(b, σ) ∩ U(b′, σ′). Then there are z, z′ ∈ ℤ^ι with Σ_i(y_i − b_i − z_i)² < σ² and Σ_i(y_i − b′_i − z′_i)² < σ′². Since σ > 0 and σ′ > 0, step 1 gives |y − (b + z)| < σ and |y − (b′ + z′)| < σ′.
3. Case z = z′. Put w := y − z. Comparing coordinates (y_i − z_i − b_i = y_i − b_i − z_i), w − b = y − (b + z) and w − b′ = y − (b′ + z). Hence |w − b| < σ and |w − b′| < σ′, so w ∈ B̄_σ(b) ∩ B̄_{σ′}(b′). This contradicts the hypothesis that these closed balls are disjoint.
4. Case z ≠ z′. By the triangle inequality and translation invariance of the distance (|(b + z) − (g₀ + z)| = |b − g₀|):
   |y − (g₀ + z)| ≤ |y − (b + z)| + |b − g₀| < σ + 1/4 < 1/4 + 1/4 = 1/2.
   In the same way, |y − (g₀ + z′)| ≤ |y − (b′ + z′)| + |b′ − g₀| < σ′ + 1/4 < 1/2. Hence, again by translation invariance and the triangle inequality:
   |z − z′| = |(g₀ + z) − (g₀ + z′)| ≤ |(g₀ + z) − y| + |y − (g₀ + z′)| < 1/2 + 1/2 = 1.
   On the other hand z ≠ z′, so z_j ≠ z′_j for some j ∈ ι. Then z_j − z′_j is a nonzero integer, so |z_j − z′_j| ≥ 1. Since (z_j − z′_j)² ≤ Σ_i(z_i − z′_i)² = |z − z′|², we get |z − z′| ≥ |z_j − z′_j| ≥ 1. Contradiction.
5. Both cases are impossible, so no point lies in U(b, σ) ∩ U(b′, σ′); that is, U(b, σ) and U(b′, σ′) are disjoint. ∎

## Key steps

1. |y − (g + z)|² = Σ_i (y_i − g_i − z_i)², so for τ > 0 the defining inequality gives |y − (g + z)| < τ.
2. A common point y yields z, z′ ∈ ℤ^ι with |y − (b + z)| < σ and |y − (b′ + z′)| < σ′.
3. If z = z′, then w = y − z lies in B̄_σ(b) ∩ B̄_{σ′}(b′), contradicting their disjointness.
4. If z ≠ z′, then |y − (g₀ + z)|, |y − (g₀ + z′)| < 1/2 give |z − z′| < 1, whereas some |z_j − z′_j| ≥ 1 gives |z − z′| ≥ 1: contradiction.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD = d8d46c95...; lake-manifest.json mathlib rev 25730c7c..., simongmt rev 2b366308...`
- `cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (all byte-identical)`
- `grep -n 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall' mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean (158: radii bounded by R, enlargement factor τ > 3; used with τ = 5)`
- `grep -n 'volume_pi_closedBall|volume_pi_ball|volume_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean (278: Real.volume_pi_closedBall = ofReal ((2r)^card ι), sup metric, r ≥ 0)`
- `grep -n 'volume_preserving' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean (124: EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp; 134: PiLp.volume_preserving_ofLp)`
- `grep -rn 'theorem volume_closedBall|theorem volume_ball' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean (307/324: exact Gamma-function formulas, not needed)`
- `grep -n 'theorem countable_meas_pos_of_disjoint_iUnion' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean (305)`
- `grep -n 'theorem tsum_meas_le_meas_iUnion_of_disjoint' mathlib/Mathlib/MeasureTheory/Measure/Basic.lean (167: arbitrary index type)`
- `grep -n 'theorem measure_biUnion_le ' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean (74: countable index set, arbitrary sets)`
- `grep -n 'theorem dist_apply_le' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean (652); grep -n 'theorem EuclideanSpace.dist_eq' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean (158)`
- `grep -n 'theorem exists_fiveTimesCovering' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean (26: Simon Ch. 1, 3.4; equivalent alternative to Mathlib's Vitali)`
- `rg -n -i 'vitali|fiveTimes|five.times|closedBall.*volume|volume.*closedBall|2 \* r\) \^' local-references/197bdd4b88278494/project/GMT (only Ch01 Vitali-property and Ch05 density statements; no ball-volume bound, Vitali measure bound or periodic-tube lemma)`
- `rg -n 'volume \(closedBall|volume_closedBall|volume_pi_closedBall' lake-packages-25730c7c/simongmt/Poincare (only exact-formula uses; no (2r)^k bound for EuclideanSpace ℝ ι)`
- `rg -n 'dgc_pm_|dgc_lattice|dgc_vitali|dgc_closedBall' over project, simongmt/Poincare, mathlib/Mathlib and workspace GMT (no match)`
- `python3 -I scan of dag.json (610 nodes): regex volume (closedBall|Vitali|PairwiseDisjoint|2 * r) ^ over lean_statement (only the accepted fiw_tb_tda_ps_ball_volume_le: ∀ n r, 0 ≤ r → volume (closedBall (0 : Eucl n) r) ≤ ofReal ((2r)^n), a different type, so not reusable); lean_name collision check for dgc_pm_ball_volume_le / dgc_pm_lattice_tubes_disjoint / dgc_pm_vitali_volume_bound (none)`
- `sed -n 1640,1700p book/chapter-06.txt (printed (1)–(4) of the proof of 5.1, 'pairwise disjoint collection', L^{n+1}(B_j) ≤ β⁻¹5^{n+1}ω_{n+1}, pp. 163–164)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on the three child statements and the parent statement (all valid); verifier/gmt-compare.py child_modules/contract_scope read to reproduce the challenge scope`
- `PATH=toolchains/lean-4.35.0-rc3-linux/bin:$PATH lake env lean /tmp/pm-split-7c41/Final.lean (full proofs of the three children; Submission.dgc_periodic_maximal proved from them; comparator-style theorem _root_.HumanizeNodeComparator.target_i : (stmt) := by exact Submission.X for all four; no sorry; #print axioms = [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-good-center-a1-periodic-maximal-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/pm-split-7c41/Final.lean`
- `/tmp/pm-split-7c41/statements.json`

Pinned revisions are confirmed (project d8d46c95, Mathlib 25730c7c, simongmt 2b366308). The frozen Contract is byte-identical to both the Submission and the snapshot.

Neither the project nor SimonGMT has a (2r)^k bound for EuclideanSpace ℝ ι balls, a Vitali packing measure bound or a periodic-tube disjointness lemma. The DAG's accepted fiw_tb_tda_ps_ball_volume_le is a Fin n / centre-0 variant with a different frozen type, so it cannot be reused.

The children are therefore built on pinned Mathlib primitives:
- ball_volume: PiLp.volume_preserving_ofLp, Real.volume_pi_closedBall, PiLp.dist_apply_le and dist_pi_le_iff.
- tubes_disjoint: EuclideanSpace.dist_eq, PiLp.dist_apply_le and Int.one_le_abs.
- vitali_bound: Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (τ = 5) and measure_biUnion_le. SimonGMT's Chapter01.exists_fiveTimesCovering is an equivalent alternative.
- Parent glue: Measure.countable_meas_pos_of_disjoint_iUnion and tsum_meas_le_meas_iUnion_of_disjoint.

All three child types validate and elaborate in the comparator's exact contract scope. All were fully proved in scratch, and Submission.dgc_periodic_maximal was kernel-checked from them with axioms [propext, Classical.choice, Quot.sound] and no sorry. No name collides with anything, and no Matrix/IsUnit construction occurs.
