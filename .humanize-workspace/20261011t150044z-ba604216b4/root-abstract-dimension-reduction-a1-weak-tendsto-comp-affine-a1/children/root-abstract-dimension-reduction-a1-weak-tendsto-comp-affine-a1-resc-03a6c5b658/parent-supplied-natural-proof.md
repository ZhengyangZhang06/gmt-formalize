# Parent-supplied natural-language proof

- Parent DAG node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1`
- Child DAG node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1.rescaled_translate_converge-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof of `adr_weak_tendsto_comp_affine`: f_k(w) = f((w − y)/c_k) → f_∞(w) = f(w − y) uniformly, with supports in a fixed compact ball. c_k⁻¹ denotes the real inverse (0⁻¹ = 0 in Lean); this convention is irrelevant because c_k > 1/2 eventually. No positivity of c_k is assumed.
1. A radius. tsupport f is compact, hence bounded, so there is R₀ with tsupport f ⊆ B̄_{R₀}(0). Put R := max(R₀, 1) > 0. If ‖x‖ > R then x ∉ tsupport f, hence f(x) = 0.
2. The compact set. Let K := B̄_{2R}(y), the closed ball of radius 2R about y. It is compact because ℝ^P is finite-dimensional (a proper space). If w ∉ K then ‖w − y‖ > 2R > R, so f(w − y) = 0 by step 1. This is (i).
3. Eventual support. Since c_k → 1 and the open interval (1/2, 2) is a neighbourhood of 1, there is k₀ with 1/2 < c_k < 2 for all k ≥ k₀. For such k and every w ∉ K we have c_k > 0 and ‖c_k⁻¹(w − y)‖ = ‖w − y‖ / c_k > 2R / c_k > 2R / 2 = R. So f(c_k⁻¹(w − y)) = 0 by step 1. This is (ii).
4. Uniform convergence. A continuous function with compact support is uniformly continuous (Heine–Cantor: it is continuous and tends to 0 at infinity). Let ε > 0 and choose δ > 0 such that |f(a) − f(b)| < ε whenever ‖a − b‖ < δ. Since c_k → 1 and t ↦ t⁻¹ is continuous at 1, c_k⁻¹ → 1; choose k₁ with |c_k⁻¹ − 1| < δ/(2R) for all k ≥ k₁. Let k ≥ max(k₀, k₁) and w ∈ ℝ^P.
(a) If ‖w − y‖ ≤ 2R, then ‖(w − y) − c_k⁻¹(w − y)‖ = |1 − c_k⁻¹|·‖w − y‖ ≤ |c_k⁻¹ − 1|·2R < (δ/(2R))·2R = δ. Hence |f(w − y) − f(c_k⁻¹(w − y))| < ε.
(b) If ‖w − y‖ > 2R, then w ∉ K. So f(w − y) = 0 by step 2 and f(c_k⁻¹(w − y)) = 0 by step 3 (k ≥ k₀), and the difference is 0 < ε.
Thus for every ε > 0 there is k₂ := max(k₀, k₁) such that |f(w − y) − f(c_k⁻¹(w − y))| < ε for all k ≥ k₂ and all w ∈ ℝ^P. This is the uniform convergence (iii). ∎
Formalization notes (verified in a scratch build of exactly this statement; standard axioms only; no additional imports):
- `hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)`; `image_eq_zero_of_notMem_tsupport`.
- `hmus (Ioo_mem_nhds (by norm_num) (by norm_num))` for k₀.
- Norm computations by `norm_smul, norm_inv, Real.norm_of_nonneg, inv_mul_eq_div, lt_div_iff₀` and `nlinarith`.
- `HasCompactSupport.uniformContinuous_of_continuous` with `Metric.uniformContinuous_iff`; `hmus.inv₀ one_ne_zero`; `Metric.tendstoUniformly_iff`.

## Key steps

1. choose R ≥ 1 with f(x) = 0 whenever ‖x‖ > R (tsupport f is compact, hence bounded)
2. K := closed ball of radius 2R about y; f(· − y) vanishes off K
3. eventually 1/2 < c_k < 2, so ‖c_k⁻¹(w − y)‖ > R and f(c_k⁻¹(w − y)) = 0 for w ∉ K
4. f is uniformly continuous; on the ball the argument moves by at most |c_k⁻¹ − 1|·2R → 0, and off K both values vanish

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; cmp of the 11 cited snapshot Mathlib files against lake-packages-25730c7c/mathlib (all byte-identical)`
- `grep -n 'hausdorffMeasure_smul|map_homothety|IsAddLeftInvariant|hausdorffMeasure_image|map_hausdorffMeasure|hausdorffMeasure_preimage|isometry' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'theorem|lemma' mathlib/Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`
- `grep -rn 'integrable_smul_left_of_hasCompactSupport|integrableOn_isCompact' mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `grep -rn 'uniformContinuous_of_continuous' mathlib/Mathlib --include=*.lean`
- `grep -rn 'MeasurableEmbedding.integral_map|integral_smul_measure|integral_add_left_eq_self|completeSpace_coe|isBounded_range_of_tendsto|tendstoUniformly_iff|mkContinuous_norm_le|def mkOfBound|norm_le' mathlib/Mathlib --include=*.lean`
- `grep -rn 'def LinearMap.mkContinuous' mathlib/Mathlib --include=*.lean (variable context in Analysis/Normed/Operator/ContinuousLinearMap.lean)`
- `grep -n 'continuous_eval_const|theorem continuous_coe' mathlib/Mathlib/Topology/ContinuousMap/Bounded/*.lean`
- `grep -rln 'banach_steinhaus|hausdorffMeasure_smul₀|map_homothety_hausdorffMeasure|TendstoUniformly' lake-packages-25730c7c/simongmt --include=*.lean`
- `grep -c <each proposed lean_name> runs/20261011T150044Z-ba604216b4/dag.json; grep -rl <name> gmt-ch07/GMT .swarm-worktrees/*/gmt-ch07/GMT`
- `grep -n 'byte|Submission|candidate_inputs' verifier/gmt-compare.py; grep '^import' .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean`
- `sed -n 110,140p book/chapter-A.txt`
- `lake env lean /tmp/wtca-decomp/Final.lean (four exact child types + parent proved from their stubs + #print axioms)`
- `lake env lean /tmp/wtca-decomp/AllFinal.lean (complete proofs of the four children and of the parent; #print axioms each)`
- `lake env lean /tmp/wtca-decomp/Exp4.lean, Exp7.lean (trace.Meta.synthInstance), Exp8.lean, Exp9.lean (Submodule ℝ (Euclid P →ᵇ ℝ) instance probes; BaireSpace availability without extra imports)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/tmp/wtca-decomp/Final.lean`
- `/tmp/wtca-decomp/AllFinal.lean`
- `/tmp/wtca-decomp/ChildA.lean`
- `/tmp/wtca-decomp/ChildBC.lean`
- `/tmp/wtca-decomp/ChildD.lean`
- `/tmp/wtca-decomp/Exp7.lean`
- `/tmp/wtca-decomp/Exp9.lean`

The snapshot Contract.lean is byte-identical to the workspace Submission.lean, and the 11 cited snapshot Mathlib files are byte-identical to the build packages.

Mathlib supplies every tool the children need:
- integral_comp_affine: map_homothety_hausdorffMeasure, hausdorffMeasure_smul₀ and the IsAddLeftInvariant instance for μH[d] (Hausdorff.lean); MeasurableEmbedding.integral_map, integral_smul_nnreal_measure, integral_add_left_eq_self.
- weak_uniform_bound: banach_steinhaus (BanachSteinhaus.lean); IsClosed.completeSpace_coe, BoundedContinuousFunction.continuous_coe/mkOfBound/norm_le/norm_coe_le_norm, LinearMap.mkContinuous, ContinuousLinearMap.le_of_opNorm_le; LocallyIntegrable.integrable_smul_left_of_hasCompactSupport and integrableOn_isCompact.
- weak_tendsto_moving_tests: Metric.isBounded_range_of_tendsto, Metric.tendstoUniformly_iff.
- rescaled_translate_converge: HasCompactSupport.uniformContinuous_of_continuous (HeineCantor.lean).

BanachSteinhaus.lean is not imported by the contract header. Its olean exists in the package tree, and adding the import to Submission.lean compiles and is allowed by gmt-compare.py, which byte-checks only frozen inputs other than Submission.lean. Baire's nonempty_interior_of_iUnion_of_closed and BaireSpace for complete metric spaces are available without it.

Instance pitfall: for X : Submodule ℝ (Euclid P →ᵇ ℝ), typeclass search does not find SeminormedAddCommGroup ↥X inside Norm (↥X →L[ℝ] Euclid Q). letI Submodule.seminormedAddCommGroup X and Submodule.normedSpace X fix this, together with explicit (E := X) arguments to mkContinuous and banach_steinhaus.

simongmt has no Banach–Steinhaus or Hausdorff change-of-variables lemma; its only TendstoUniformly hits are test-form topology for currents in Chapter06, so it has no relevant match.

The four exact child types elaborate in the contract scope, and the parent compiles from their stubs. Complete scratch proofs of all four children and of the parent use only propext, Classical.choice and Quot.sound. The proposed names collide with nothing in dag.json or any worktree.
