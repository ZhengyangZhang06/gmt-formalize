# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.density_rep-a1.vitali_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5 (Vitali covering; a non-sharp constant suffices), stated for an arbitrary set A and filled in.

Notation: ω_n := unitBallVolume n = volume(B_1(0) ⊆ ℝⁿ); μH[n] is Mathlib's unnormalized Hausdorff measure; B_r(x) and B̄_r(x) are the open and closed balls; all quantities lie in [0, ∞].

1. Constants. 0 < ω_n < ∞, because B_1(0) is a nonempty bounded open subset of ℝⁿ and volume on Euclid n is an additive Haar measure (measure_ball_pos, measure_ball_lt_top). Put c := ofReal(η/2)·ω_n. Then 0 < c < ∞.

2. Arbitrarily small good radii. Let x ∈ A and δ > 0. As η > 0, ofReal(η/2) < ofReal(η) ≤ liminf_{r↓0} μ(B_r(x))/(ω_n·ofReal(rⁿ)). Hence the quotient exceeds ofReal(η/2) for all r in some set belonging to 𝓝[>]0 (Filter.eventually_lt_of_lt_liminf). Intersect with (0, δ) ∈ 𝓝[>]0 (Ioo_mem_nhdsGT); since 𝓝[>]0 is a proper filter, there is ρ ∈ (0, δ) with ofReal(η/2) < μ(B_ρ(x))/(ω_n·ofReal(ρⁿ)). Then c·ofReal(ρⁿ) = ofReal(η/2)·(ω_n·ofReal(ρⁿ)) ≤ μ(B_ρ(x)) ≤ μ(B̄_ρ(x)) (ENNReal.mul_le_of_le_div and monotonicity).

3. Radii at scale k. For k ∈ ℕ let δ_k := 1/(k+1). By step 2 and choice there are functions r_k : ℝ^P → ℝ with, for all x ∈ A, 0 < r_k(x) < δ_k and c·ofReal(r_k(x)ⁿ) ≤ μ(B̄_{r_k(x)}(x)).

4. Vitali subfamily. Apply the Vitali covering lemma (Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall) with index set A, centers x ↦ x, radii r_k ≤ δ_k and τ = 5 > 3. It gives u_k ⊆ A such that the balls B̄_{r_k(b)}(b), b ∈ u_k, are pairwise disjoint, and every a ∈ A has some b ∈ u_k with B̄_{r_k(a)}(a) ⊆ B̄_{5r_k(b)}(b). Since a ∈ B̄_{r_k(a)}(a), A ⊆ ⋃_{b∈u_k} B̄_{5r_k(b)}(b). Each B̄_{r_k(b)}(b) contains the nonempty open ball B_{r_k(b)}(b), so it has nonempty interior. As ℝ^P is separable, u_k is countable (Set.PairwiseDisjoint.countable_of_nonempty_interior).

5. Radius sum. Countable additivity over the disjoint Borel balls (measure_biUnion) gives Σ_{b∈u_k} μ(B̄_{r_k(b)}(b)) = μ(⋃_{b∈u_k} B̄_{r_k(b)}(b)) ≤ μ(ℝ^P). With step 3, c·Σ_{b∈u_k} ofReal(r_k(b)ⁿ) ≤ μ(ℝ^P) (ENNReal.tsum_mul_left). Multiplying by c⁻¹ (c ≠ 0, ∞) gives Σ_{b∈u_k} ofReal(r_k(b)ⁿ) ≤ c⁻¹μ(ℝ^P).

6. Diameters. For y, z ∈ B̄_{5r}(b), dist(y, z) ≤ dist(y, b) + dist(z, b) ≤ 10r. So diam B̄_{5r_k(b)}(b) ≤ ofReal(10r_k(b)) ≤ ofReal(10δ_k) (Metric.ediam_le_of_forall_dist_le). The map t ↦ tⁿ is monotone on [0, ∞] (ENNReal.rpow_le_rpow, exponent n ≥ 0), and ofReal(10r)ⁿ = 10ⁿ·ofReal(rⁿ) for r ≥ 0. Hence Σ_{b∈u_k} (diam B̄_{5r_k(b)}(b))ⁿ ≤ 10ⁿ·Σ_{b∈u_k} ofReal(r_k(b)ⁿ) ≤ 10ⁿ·c⁻¹·μ(ℝ^P) =: Λ. Λ < ∞ because μ(ℝ^P) < ∞ and c > 0.

7. Hausdorff bound. For each k, the countable family (B̄_{5r_k(b)}(b))_{b∈u_k} covers A, with diameters ≤ ofReal(10δ_k) → 0 as k → ∞. Apply Measure.hausdorffMeasure_le_liminf_tsum with exponent n, filter atTop on ℕ, and index types the countable subtypes u_k. It gives μH[n](A) ≤ liminf_k Σ_{b∈u_k} (diam B̄_{5r_k(b)}(b))ⁿ ≤ Λ, since every term is ≤ Λ (Filter.liminf_le_of_frequently_le').

8. Conclusion. By definition μHE[n] = s·μH[n], where s = addHaarScalarFactor(volume, μH[n]) is a finite nonnegative real (euclideanHausdorffMeasure_def). Hence μHE[n](A) ≤ s·Λ < ∞. ∎

## Key steps

1. From the liminf hypothesis, choose radii r_k(x) < 1/(k+1) with c·r_k(x)ⁿ ≤ μ(B̄_{r_k(x)}(x)), where c = (η/2)·ω_n ∈ (0, ∞).
2. Vitali 5r-lemma: a countable disjoint subfamily u_k ⊆ A with A ⊆ ⋃_{b∈u_k} B̄_{5r_k(b)}(b).
3. Σ diam(B̄_{5r_k(b)}(b))ⁿ ≤ 10ⁿ·Σ r_k(b)ⁿ ≤ 10ⁿ·c⁻¹·μ(ℝ^P) =: Λ < ∞, with diameters ≤ 10/(k+1).
4. hausdorffMeasure_le_liminf_tsum gives μH[n](A) ≤ Λ; μHE[n] is a finite multiple of μH[n].

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean and GMT/Ch07/Submission.lean (all identical); lake-manifest.json mathlib rev 25730c7c759d108ef87ab70af2342a196760f79d`
- `grep -rn in the snapshot mathlib/Mathlib for: theorem exists_disjoint_subfamily_covering_enlargement_closedBall; theorem hausdorffMeasure_le_liminf_tsum; def euclideanHausdorffMeasure / euclideanHausdorffMeasure_def; countable_of_nonempty_interior; theorem mul_le_of_le_div; theorem eventually_lt_of_lt_liminf; exists_antilipschitzWith; theorem IsCompact.sSup_mem; theorem monotone_sort; theorem map_perm; map_eq_zero_of_not_injective; theorem map_sum; map_smul_univ; def apply (ContinuousAlternatingMap); le_opNorm; theorem integral_withDensity_eq_integral_toReal_smul; singularPart_eq_zero_of_ac; theorem haveLebesgueDecomposition_add; theorem rnDeriv_lt_top; theorem measurable_rnDeriv; theorem withDensity_apply; theorem integral_eq_zero_iff_of_nonneg_ae; theorem measure_ball_pos; ediam_le_of_forall_dist_le; theorem liminf_le_of_frequently_le'; of_le_add_mul; le_mul_norm_sub; theorem of_injective (FiniteDimensional); theorem sum_repr / basisFun_repr; pi_norm_le_iff_of_nonneg; Integrable.of_bound; toReal_le_of_le_ofReal. All were found.`
- `grep -rn 'Module.Finite\|FiniteDimensional' restricted to multilinear/alternating files in the snapshot Mathlib: no instance for ContinuousAlternatingMap (only Module.Finite.multilinearMap), so finite-dimensionality is derived from an injective coordinate map`
- `python3 -I scan of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json lean_statement/title fields with regexes 'covectorEuclideanNorm β ≤ 1', '‖α‖ ≤ .*covectorEuclideanNorm', 'covectorEuclideanNorm α = 0 →', '(?i)vitali|upper density|lower density.*Hausdorff|dual norm|comass|attain'. Found accepted regcomp_covectorEuclideanNorm_seminorm_retract, rsd_mw_tfa_norm_props, regcomp_covector_unit_ball_dense_seq, regcomp_covector_field_near_maximizer, cmr_coordinate_covectors_span, dorag_lip_vitali_two_measure_bound, cmr_vr_cd_density_representation and regcomp_atl_upper_density_zero. None has the type of a needed child.`
- `grep -c '"<name>"' dag.json and grep -rn <name> GMT/ plus the snapshot project for the five proposed lean_names: 0 matches. Python count: 1331 DAG lean names, 0 with prefix cbr_ci_dr`
- `sed of lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, GeometricCurrentOn.massOn), Forms.lean (Covector, DifferentialForm, IsTestForm) and Currents.lean (TestFormOn, GeometricCurrentOn)`
- `grep of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py check_source_delta (one theorem per leaf; no helper declarations or set_option) and runtime.py _existing_lean_name_problem/_solve_children (cross-branch reuse only for accepted nodes with identical types)`
- `lake env lean /tmp/dr-decomp/lean/{Types,Assembly,C1,C2,C3,C4,C5,Full}.lean from the workspace root. All succeed. Full.lean: #print axioms dr_full_check = [propext, Classical.choice, Quot.sound]`
- `python3 -I /tmp/dr-decomp/py/validate.py: verifier/lean_contract.py validate_lean_statement passes on all five child statements, and each exact string occurs in Types.lean and Full.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-af13c47156/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-af13c47156/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Multilinear/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dr-decomp/lean/Types.lean`
- `/tmp/dr-decomp/lean/Assembly.lean`
- `/tmp/dr-decomp/lean/C1.lean`
- `/tmp/dr-decomp/lean/C2.lean`
- `/tmp/dr-decomp/lean/C3.lean`
- `/tmp/dr-decomp/lean/C4.lean`
- `/tmp/dr-decomp/lean/C5.lean`
- `/tmp/dr-decomp/lean/Full.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c).

Every Mathlib lemma the child proofs rely on exists in the snapshot and is reachable from `import GMT.Ch07.Submission`, including:
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall and Measure.hausdorffMeasure_le_liminf_tsum
- euclideanHausdorffMeasure_def (finite NNReal scalar)
- haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac and rnDeriv_lt_top
- integral_withDensity_eq_integral_toReal_smul
- LinearMap.exists_antilipschitzWith, Tuple.monotone_sort and AlternatingMap.map_perm

Mathlib has no FiniteDimensional instance for continuous alternating maps; the dual_norm proof derives it from the injective coordinate map.

No accepted DAG declaration matches a needed child type exactly. The covector-norm toolkits lack definiteness and the lower bound, the two-measure Vitali bound is circular for Hⁿ, and the C_c density representation has no carrier. The five fresh names (prefix cbr_ci_dr_) collide with nothing.

All five exact child types elaborate, pass validate_lean_statement and have complete Lean proofs (C1–C5). Assembly and Full prove the exact frozen parent type from them using only propext, Classical.choice and Quot.sound.
