# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.approx_tangent_graph-a1.approx_tangent_le_flat-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–8 of the parent-supplied proof of dgcr_approxTangent_eq_graph_tangent, generalized as follows:
- the graph Σ becomes an arbitrary set S;
- the plane L = range DΦ(v₀) becomes an arbitrary subspace T;
- the coercivity and differentiability estimates of supplied steps 1 and 4, as used in step 5, become the flatness hypothesis.
The quantity the supplied proof calls ε (namely infDist(y, L)) is called δ here, because ε now denotes the flatness parameter.

Notation:
- ℝ^P = Euclid P and Hⁿ = μHE[n].
- For λ ∈ ℝ, η_λ(a) := blowUpMap x λ a = λ⁻¹(a − x) (Poincare.SimonGMT.Chapter03.blowUpMap).
- N := (A ∩ B_r(x)) ∖ S, so Hⁿ(N) = 0 by hypothesis.
- HasApproximateTangentSpaceAt n A x Q means: finrank Q = n and, for every f ∈ C_c(ℝ^P, ℝ), ∫_{η_λ(A)} f dHⁿ → ∫_Q f dHⁿ as λ → 0⁺. Each integral is against Hⁿ restricted to the indicated set.

Formalization note: unless split further, this is a machine leaf: one theorem appended to GMT/Ch07/Submission.lean, with no new import or helper. Every lemma cited below is in the import closure of GMT.Ch07.Submission.

1. T is a finite-dimensional subspace of ℝ^P, hence closed (Submodule.closed_of_finiteDimensional), and it is nonempty since 0 ∈ T. Let y ∈ Q; we show y ∈ T. Suppose, for contradiction, that y ∉ T.

2. Then δ := infDist(y, T) > 0 (IsClosed.notMem_iff_infDist_pos). Put R := ‖y‖ + δ > 0 and ε := δ/(4R) > 0.

3. Let g(w) := max(0, δ/2 − dist(w, y)).
- g is continuous and g ≥ 0.
- g(w) = 0 whenever w ∉ B̄_{δ/2}(y), since then δ/2 − dist(w, y) < 0.
- g(w) > 0 whenever w ∈ B_{δ/2}(y).
Closed balls of ℝ^P are compact, so g has compact support (HasCompactSupport.intro). Hence g defines f ∈ C_c(ℝ^P, ℝ) with f(w) = g(w) for all w.

4. Apply the flatness hypothesis with this ε. It gives ρ > 0 such that every a ∈ S with dist(a, x) < ρ admits t ∈ T with ‖a − x − t‖ ≤ ε‖a − x‖. Put λ₀ := min(ρ, r)/R > 0.

5. Claim: for every λ with 0 < λ < λ₀, η_λ(A) ∩ B̄_{δ/2}(y) ⊆ η_λ(N).
Let a ∈ A with w := η_λ(a) ∈ B̄_{δ/2}(y).
- Bounds. a − x = λw, and ‖w‖ ≤ ‖y‖ + dist(w, y) ≤ ‖y‖ + δ/2 < R. Hence ‖a − x‖ = λ‖w‖ < λR < min(ρ, r), the last step because λ < λ₀. In particular a ∈ B_r(x).
- Suppose a ∈ S. Since dist(a, x) = ‖a − x‖ < ρ, step 4 gives t ∈ T with ‖a − x − t‖ ≤ ε‖a − x‖.
- Then λ⁻¹t ∈ T and w − λ⁻¹t = λ⁻¹(a − x − t). Therefore dist(w, λ⁻¹t) = λ⁻¹‖a − x − t‖ ≤ λ⁻¹ε‖a − x‖ = ε‖w‖ < εR = δ/4.
- So infDist(w, T) ≤ dist(w, λ⁻¹t) < δ/4 (Metric.infDist_le_dist_of_mem).
- But infDist(y, T) ≤ infDist(w, T) + dist(y, w) (Metric.infDist_le_infDist_add_dist), and dist(y, w) ≤ δ/2. Together these give infDist(w, T) ≥ δ − δ/2 = δ/2, a contradiction.
Hence a ∉ S. So a ∈ (A ∩ B_r(x)) ∖ S = N, and w = η_λ(a) ∈ η_λ(N).

6. Fix λ > 0. The map η_λ is λ⁻¹-Lipschitz on ℝ^P, since ‖η_λ(a) − η_λ(b)‖ = λ⁻¹‖a − b‖. Hence Hⁿ(η_λ(N)) ≤ (λ⁻¹)ⁿ·Hⁿ(N) = 0 (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, with constant Real.toNNReal λ⁻¹). By step 5 and monotonicity, Hⁿ(η_λ(A) ∩ B̄_{δ/2}(y)) = 0 for every λ ∈ (0, λ₀).

7. Fix λ ∈ (0, λ₀).
- The closed ball is measurable, so (Hⁿ⌞η_λ(A))(B̄_{δ/2}(y)) = Hⁿ(B̄_{δ/2}(y) ∩ η_λ(A)) = 0 by step 6 (Measure.restrict_apply). Measurability of η_λ(A) is not needed.
- Hence Hⁿ⌞η_λ(A)-almost every w lies outside B̄_{δ/2}(y) (measure_eq_zero_iff_ae_notMem), and there f(w) = 0 by step 3.
- So f = 0 almost everywhere for Hⁿ⌞η_λ(A), and ∫_{η_λ(A)} f dHⁿ = 0 (integral_eq_zero_of_ae).

8. The interval (0, λ₀) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT).
- By step 7, the function λ ↦ ∫_{η_λ(A)} f dHⁿ is eventually equal to the constant 0 along 𝓝[>] 0, so it tends to 0 (Tendsto.congr' with tendsto_const_nhds).
- By the hypothesis HasApproximateTangentSpaceAt n A x Q applied to f, the same function tends to ∫_Q f dHⁿ.
- Since 𝓝[>] 0 is a nontrivial filter, uniqueness of limits (tendsto_nhds_unique) gives ∫_Q f dHⁿ = 0.

9. On the other hand, finrank Q = n. Hence:
- μ_Q := Hⁿ⌞Q is a regular measure, in particular finite on compact sets (Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule);
- its support is Q (Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule).
f is continuous with compact support, so it is μ_Q-integrable (Continuous.integrable_of_hasCompactSupport), and f ≥ 0. The support of f contains the open ball B_{δ/2}(y), which is a neighbourhood of y. As y ∈ Q = supp μ_Q, μ_Q(support f) ≥ μ_Q(B_{δ/2}(y)) > 0 (Measure.mem_support_iff_forall). Hence ∫_Q f dHⁿ > 0 (integral_pos_iff_support_of_nonneg). This contradicts step 8.

10. Therefore y ∈ T. As y ∈ Q was arbitrary, Q ≤ T. ∎

## Key steps

1. Assume y ∈ Q ∖ T. Since T is closed, δ := infDist(y, T) > 0. Put R := ‖y‖ + δ and ε := δ/(4R), and test with f := max(0, δ/2 − dist(·, y)) ∈ C_c(ℝ^P, ℝ).
2. Flatness at ε gives ρ. For 0 < λ < min(ρ, r)/R, η_λ(A) ∩ B̄_{δ/2}(y) ⊆ η_λ((A ∩ B_r(x)) ∖ S): a point a ∈ S would put η_λ(a) within δ/4 of T, whereas infDist(·, T) ≥ δ/2 on B̄_{δ/2}(y).
3. η_λ is λ⁻¹-Lipschitz, so that image is Hⁿ-null. Since f vanishes off B̄_{δ/2}(y), ∫_{η_λ(A)} f dHⁿ = 0 for all λ ∈ (0, min(ρ, r)/R).
4. The approximate-tangent limit along 𝓝[>] 0 and uniqueness of limits give ∫_Q f dHⁿ = 0.
5. Hⁿ⌞Q is locally finite with support Q ∋ y, and f > 0 on B_{δ/2}(y), so ∫_Q f dHⁿ > 0. This contradiction shows Q ≤ T.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; python3 read lake-manifest.json package revs; git rev-parse HEAD in .lake/packages/mathlib`
- `grep -n "def HasApproximateTangentSpaceAt\|def blowUpMap\|theorem HasApproximateTangentSpaceAt\|lemma HasApproximateTangentSpaceAt\|support_euclideanHausdorffMeasure_restrict_submodule\|regular_euclideanHausdorffMeasure_restrict_submodule\|^import" Chapter03/Rectifiable.lean (simongmt)`
- `grep -n -A12 "theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" Chapter02/Lipschitz.lean; grep -n "^namespace\|^end" Chapter02/Lipschitz.lean`
- `rg -n "theorem .*[Aa]pproximateTangent|theorem .*approxTangent" --glob '*.lean' simongmt/Poincare/SimonGMT`
- `rg -n "theorem measure_eq_zero_iff_ae_notMem|theorem IsClosed.notMem_iff_infDist_pos|theorem infDist_le_infDist_add_dist|theorem infDist_le_dist_of_mem|theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero|theorem eq_of_le_of_finrank_eq|theorem integral_pos_iff_support_of_nonneg\b|theorem Continuous.integrable_of_hasCompactSupport|lemma mem_support_iff_forall|theorem finrank_euclideanSpace_fin|theorem ContDiffOn.differentiableOn\b|theorem integral_eq_zero_of_ae|theorem eventually_nhds_iff\b" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n "notMem_iff_infDist_pos|finrank_range_of_inj|closed_of_finiteDimensional|HasFDerivAt.isLittleO|HasFDerivAt.const_add|theorem intro \[|Ioo_mem_nhdsGT" local-references/123e8435b4a2469b/mathlib/Mathlib (snapshot)`
- `python3 scan of every lean_name in dag.json and nodes/*/*.json (566 names); grep -rl dgcr_atg over the run's nodes/ and dag.json; git grep -l dgcr_atg <all 979 refs> -- GMT/Ch07/Submission.lean (exit 1: no match)`
- `read nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/decomposition-v{1,2}.json and decomposition-audit-v{1,2}.json (atsm_approxTangent_le_of_flat); nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json (sibling types); git show <accepted child ref>:GMT/Ch07/Submission.lean (child placement)`
- `python3 -I /tmp/atg-work/gen_cmp.py (lean_contract.validate_lean_statement + gmt-compare.child_modules contract mode); lake env lean /tmp/atg-work/{Parent,Types,B2,All,CmpCheck,Inlined}.lean with #check and #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-b5ecd87c13/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-b5ecd87c13/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-regular-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/decomposition-audit-v2.json`
- `/tmp/atg-work/gen_cmp.py`
- `/tmp/atg-work/children.json`
- `/tmp/atg-work/Types.lean`
- `/tmp/atg-work/All.lean`
- `/tmp/atg-work/CmpCheck.lean`
- `/tmp/atg-work/Inlined.lean`

Snapshot, project and package revisions agree:
- The snapshot manifest records project b4d606d and Mathlib 25730c7c, equal to the workspace HEAD and the lake-manifest Mathlib pin.
- simongmt is pinned at 2b36630.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean, and Submission.lean is byte-identical to the contract.

Reusable facts, all in the import closure of GMT.Ch07.Submission (checked by compiling files that import only that module):
- From simongmt Chapter03/Rectifiable.lean: HasApproximateTangentSpaceAt (finrank Q = n plus convergence of ∫_{blowUpMap x r '' M} f dμHE[n] along 𝓝[>] 0 for f ∈ C_c), HasApproximateTangentSpaceAt.finrank_eq, blowUpMap x r y = r⁻¹ • (y − x), regular_ and support_euclideanHausdorffMeasure_restrict_submodule.
- From Chapter02/Lipschitz.lean: Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- From snapshot Mathlib: measure_eq_zero_iff_ae_notMem, IsClosed.notMem_iff_infDist_pos, infDist_le_infDist_add_dist, infDist_le_dist_of_mem, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero, Submodule.eq_of_le_of_finrank_eq, LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin, integral_pos_iff_support_of_nonneg, Continuous.integrable_of_hasCompactSupport, Measure.mem_support_iff_forall, integral_eq_zero_of_ae, HasFDerivAt.isLittleO and HasFDerivAt.const_add (aliases), Submodule.closed_of_finiteDimensional, HasCompactSupport.intro (to_additive), Ioo_mem_nhdsGT (confirmed by #check).
- ContDiffOn.differentiableOn takes n ≠ 0 in this Mathlib.

Existing lemmas and names:
- No existing simongmt lemma bounds an approximate tangent plane by a flat direction; the Chapter04 approximate-tangent results concern density.
- The analogous atsm_approxTangent_le_of_flat (global null hypothesis) is only reserved in another branch's decomposition and is not comparator-accepted, so a uniquely named local variant is used.
- No dgcr_atg_ name collides anywhere: DAG, node JSONs, and all 979 git refs.

Lean checks:
- All three child types and the parent type pass validate_lean_statement and elaborate in the exact comparator contract scope generated by gmt-compare.child_modules.
- The exact frozen parent type follows from the three exact child types without sorry.
- Complete single-theorem proofs of all three children compile, also when inserted into a byte copy of Submission.lean.
- Only propext, Classical.choice and Quot.sound are used.
