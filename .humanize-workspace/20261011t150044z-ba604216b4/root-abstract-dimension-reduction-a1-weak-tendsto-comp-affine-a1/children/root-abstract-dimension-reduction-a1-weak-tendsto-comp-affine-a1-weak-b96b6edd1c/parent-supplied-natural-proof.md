# Parent-supplied natural-language proof

- Parent DAG node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1`
- Child DAG node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1.weak_uniform_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof of `adr_weak_tendsto_comp_affine`. This is the uniform bound that the weak limits of Simon, chapter-A.txt lines 125–133, need tacitly (departure [D2] of the A.4 decomposition), stated here for an arbitrary measure μ and an arbitrary compact K. For the uniform boundedness principle see e.g. W. Rudin, Functional Analysis, Ch. 2 (Banach–Steinhaus theorem); in Mathlib, `banach_steinhaus`.
Notation: BC is the real vector space of bounded continuous functions u : ℝ^P → ℝ with the sup norm ‖u‖ := sup_x |u(x)|, so |u(x)| ≤ ‖u‖ for all x.
1. BC is a Banach space: a uniform limit of bounded continuous real functions is bounded and continuous, and ℝ is complete. In Mathlib, `Euclid P →ᵇ ℝ` is a `CompleteSpace`.
2. Let X_K := {u ∈ BC : u(x) = 0 for every x ∉ K}. It is a linear subspace of BC. It is closed: for each x the evaluation u ↦ u(x) is continuous on BC, since |u(x) − v(x)| ≤ ‖u − v‖. So X_K = ⋂_{x ∉ K} {u : u(x) = 0} is an intersection of closed sets. A closed subset of a complete metric space is complete, so X_K with the sup norm is a Banach space.
3. Every u ∈ X_K has compact support. Indeed support(u) ⊆ K, and K is closed (a compact subset of the Hausdorff space ℝ^P), so tsupport(u) = closure(support u) ⊆ K is a closed subset of a compact set. Consequently, for every k, x ↦ u(x)·g_k(x) is μ-integrable: g_k is μ-integrable on the compact set K by local integrability, u is continuous (hence measurable) and bounded by ‖u‖, and u·g_k vanishes outside K (Mathlib `LocallyIntegrable.integrable_smul_left_of_hasCompactSupport`).
4. For k ∈ ℕ define Λ_k : X_K → ℝ^Q by Λ_k(u) := ∫ u(x)·g_k(x) dμ(x). By step 3 every integrand is integrable, so additivity and homogeneity of the Bochner integral make Λ_k linear. Put B_k := ∫_K ‖g_k‖ dμ < ∞. For u ∈ X_K, since u = 0 outside K and |u(x)| ≤ ‖u‖,
‖Λ_k(u)‖ ≤ ∫ ‖u(x)·g_k(x)‖ dμ = ∫_K |u(x)|·‖g_k(x)‖ dμ ≤ ∫_K ‖u‖·‖g_k(x)‖ dμ = B_k·‖u‖.
Hence each Λ_k is a bounded (= continuous) linear operator X_K → ℝ^Q.
5. Pointwise boundedness. For u ∈ X_K, u is continuous with compact support (step 3), so the hypothesis gives C_u with ‖Λ_k(u)‖ ≤ C_u for all k.
6. Uniform boundedness principle: a pointwise bounded family of continuous linear operators from a Banach space to a normed space is bounded in operator norm. By steps 2, 4 and 5 there is M′ ∈ ℝ with ‖Λ_k‖ ≤ M′ for all k. Put M := max(M′, 0).
7. Let k ∈ ℕ, let h be continuous with h = 0 outside K, and let C ∈ ℝ with |h(x)| ≤ C for all x. Then C ≥ |h(0)| ≥ 0. Being continuous and bounded, h is an element u_h of BC with ‖u_h‖ = sup|h| ≤ C, and u_h ∈ X_K because h vanishes outside K. Therefore
‖∫ h·g_k dμ‖ = ‖Λ_k(u_h)‖ ≤ ‖Λ_k‖·‖u_h‖ ≤ M′·‖u_h‖ ≤ M·‖u_h‖ ≤ M·C,
using ‖u_h‖ ≥ 0, M′ ≤ M, M ≥ 0 and ‖u_h‖ ≤ C. Since k, h and C were arbitrary, M is as required. ∎
Formalization notes (verified in a scratch build of exactly this statement; standard axioms only):
(i) Import. `banach_steinhaus` is in `Mathlib.Analysis.Normed.Operator.BanachSteinhaus`, which the contract header does not import. Either add that import to GMT/Ch07/Submission.lean (the comparator byte-checks only frozen inputs other than Submission.lean), or re-derive step 6 from the Baire category theorem `nonempty_interior_of_iUnion_of_closed`. That theorem, with the `BaireSpace` instance for complete metric spaces, is already available.
(ii) Realize X_K as `X : Submodule ℝ (Euclid P →ᵇ ℝ)` (with `open scoped BoundedContinuousFunction`) with carrier `{u | ∀ x ∉ K, u x = 0}`. Closedness: `isClosed_iInter` and `isClosed_eq ((continuous_apply x).comp BoundedContinuousFunction.continuous_coe) continuous_const`. Completeness: `IsClosed.completeSpace_coe`.
(iii) Instances. Typeclass search does not find `SeminormedAddCommGroup ↥X` inside `Norm (↥X →L[ℝ] Euclid Q)`. Add `letI : SeminormedAddCommGroup X := Submodule.seminormedAddCommGroup X` and `letI : NormedSpace ℝ X := Submodule.normedSpace X`. Also pass `(𝕜 := ℝ) (𝕜₂ := ℝ) (E := X) (F := Euclid Q)` to `LinearMap.mkContinuous` and to `banach_steinhaus`.
(iv) Step 4: `norm_integral_le_integral_norm`, `setIntegral_eq_integral_of_forall_compl_eq_zero`, `setIntegral_mono_on`, `BoundedContinuousFunction.norm_coe_le_norm`, `integral_const_mul`.
(v) Step 7: `BoundedContinuousFunction.mkOfBound`, `BoundedContinuousFunction.norm_le`, `ContinuousLinearMap.le_of_opNorm_le`.

## Key steps

1. X_K := bounded continuous functions vanishing off K is a closed subspace of the Banach space of bounded continuous functions (sup norm), hence complete
2. each u ∈ X_K has compact support, so u·g_k is integrable and Λ_k(u) := ∫ u g_k dμ is linear with ‖Λ_k u‖ ≤ (∫_K ‖g_k‖ dμ)·‖u‖
3. the hypothesis makes (Λ_k u)_k bounded for each u ∈ X_K
4. uniform boundedness principle: ‖Λ_k‖ ≤ M′ for all k; put M := max(M′, 0)
5. a continuous h vanishing off K with |h| ≤ C is an element of X_K of sup norm ≤ C, so ‖∫ h g_k dμ‖ ≤ M·C

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
