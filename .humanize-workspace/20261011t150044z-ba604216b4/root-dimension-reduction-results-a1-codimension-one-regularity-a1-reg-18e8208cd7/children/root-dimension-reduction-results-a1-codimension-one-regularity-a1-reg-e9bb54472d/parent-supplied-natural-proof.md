# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1.fderiv_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 1 of the parent proof: 'Let a ∈ B and v ∈ ℝ^n. Since B is open, a + tv ∈ B for small t > 0, and then mt|v| ≤ |g(a + tv) − g(a)|. Dividing by t and letting t ↓ 0 gives m|v| ≤ |Dg(a)v|.' Here the open ball B is replaced by the open set U, and the two-point lower bound is needed only with base point a.
Notation: L := Dg(a) = fderiv ℝ g a. For t ≠ 0, q(t) := t^{-1}(g(a + tv) − g(a)).

1. (Difference quotients converge.)
- Fix v ∈ ℝ^n. Since g is differentiable at a with derivative L, g(a + w) − g(a) − Lw = o(|w|) as w → 0.
- Take w = tv with t > 0 and t → 0. Then q(t) − Lv = t^{-1}(g(a + tv) − g(a) − L(tv)) → 0. (If v = 0 this is trivial, since then q(t) = 0 = Lv.)
- Hence q(t) → Lv as t ↓ 0, i.e. along the filter 𝓝[>] 0.
- In Mathlib this is HasFDerivAt.lim with c(t) = t^{-1}. Here |c(t)| → ∞ along 𝓝[>] 0 by tendsto_inv_nhdsGT_zero and tendsto_norm_atTop_atTop. Also c(t)(g(a + c(t)^{-1}v) − g(a)) = q(t), because (t^{-1})^{-1} = t.

2. (Points of U.) Since U is open and a ∈ U, U is a neighbourhood of a. The map t ↦ a + tv is continuous and equals a at t = 0. So a + tv ∈ U for all t in a neighbourhood of 0, and in particular eventually along 𝓝[>] 0.

3. (Inequality for small t.)
- Let t > 0 with a + tv ∈ U. By step 2 this holds eventually along 𝓝[>] 0, and t > 0 holds on 𝓝[>] 0 by definition.
- The hypothesis with x = a + tv gives m|(a + tv) − a| ≤ |g(a + tv) − g(a)|.
- Since (a + tv) − a = tv and |tv| = t|v|, this reads t·(m|v|) ≤ |g(a + tv) − g(a)|.
- Dividing by t > 0 gives m|v| ≤ t^{-1}|g(a + tv) − g(a)| = |q(t)|, using |t^{-1}| = t^{-1}.

4. (Passage to the limit.)
- By step 1 and continuity of the norm, |q(t)| → |Lv| along 𝓝[>] 0.
- The filter 𝓝[>] 0 on ℝ is nontrivial, and by step 3 the inequality m|v| ≤ |q(t)| holds eventually along it.
- The set {y ∈ ℝ : m|v| ≤ y} is closed, so the limit satisfies m|v| ≤ |Lv| (Mathlib: ge_of_tendsto).
- Since v was arbitrary, m|v| ≤ |Dg(a)v| for every v ∈ ℝ^n. ∎

Implementation note (not part of the mathematics). Mathlib alone suffices. Useful names: HasFDerivAt.lim (with hg.hasFDerivAt and simpa only [inv_inv]), tendsto_inv_nhdsGT_zero, tendsto_norm_atTop_atTop, Tendsto.norm, IsOpen.mem_nhds, nhdsWithin_le_nhds, self_mem_nhdsWithin, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg, le_inv_mul_iff₀, ge_of_tendsto.

## Key steps

1. Differentiability of g at a gives t^{-1}(g(a + tv) − g(a)) → Dg(a)v as t ↓ 0.
2. Since U is open, a + tv ∈ U for small t > 0. Then t·m|v| ≤ |g(a + tv) − g(a)|, i.e. m|v| ≤ |t^{-1}(g(a + tv) − g(a))|.
3. Let t ↓ 0 along the nontrivial filter 𝓝[>] 0. The non-strict inequality passes to the limit: m|v| ≤ |Dg(a)v|.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5…, mathlib 25730c7c759d…)`
- `python3 scans of .humanize/.../dag.json: selected node record (depth 5, status decomposing, no children); all lean_statements containing fderiv/normDet/areaJacobian/blowUpMap/HasApproximateTangentSpaceAt (pit_*, ptd_piece_image_approxTangent_ae, codim1_lur_piece_image_approxTangent_ae, setIntegral_blowUpMap_image_eq_inv_pow_mul …); collision check for codim1_rdo_c1pt_fderiv_lower_bound / _rescaled_area_formula / _linear_range_integral / _rescaled_integral_tendsto (0 matches)`
- `rg -n 'codim1_rdo_c1pt' over local-references/123e8435b4a2469b, lake-packages-25730c7c/simongmt/Poincare and workspace GMT/ (0 files); rg -n 'codim1_rdo|HasApproximateTangentSpaceAt|blowUpMap' project/GMT/Ch07/*.lean; rg -n 'abbrev Euclid' project/GMT/Ch07/Contract.lean`
- `rg -n in snapshot mathlib/Mathlib: 'theorem tendsto_integral_filter_of_dominated_convergence', 'theorem HasFDerivAt.lim', 'setIntegral_eq_of_subset_of_forall_sdiff_eq_zero', 'setIntegral_eq_integral_of_forall_compl_eq_zero', 'euclideanHausdorffMeasure_eq_volume', 'continuous_det', 'finrank_range_of_inj', 'theorem coe_range [RingHomSurjective', 'protected theorem fderiv', 'bounded_above_of_compact_support', 'exists_bound_of_continuousOn', 'theorem tendsto_inv_nhdsGT_zero'`
- `sed -n SimonGMT Chapter03/Rectifiable.lean 1-160 (blowUpMap, HasApproximateTangentSpaceAt); Chapter02/WeightedArea.lean 1-175 (integral_area_formula_of_injective_derivative); Chapter02/Area.lean 1-70 (areaJacobianAt, areaJacobianAt_eq_sqrt_det_adjoint_comp); Chapter02/AreaApproximation.lean 1-60 (continuous_normDet, measurable_areaJacobianAt); ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 (WeightedArea.olean prebuilt)`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean for accepted nodes (713eebc5c1, 7c29ce33ec; Chapter02 import headers of accepted nodes, e.g. dor_graph_supported_cycle_regular imports Chapter02.WeightedArea)`
- `sed -n runtime.py _decompose (depth gate node.depth >= max_depth) and _existing_lean_name_problem; gmt-compare.py contract_scope/child_modules (replayed scope) via python3 -I /tmp/c1pt-decomp-k7q2-scripts/scope.py; lean_contract.validate_lean_statement on all types via /tmp/c1pt-decomp-k7q2-scripts/extract.py`
- `lake env lean /tmp/c1pt-decomp-k7q2/Avail.lean (normDet, areaJacobianAt, continuous_normDet unknown after import GMT.Ch07.Submission; blowUpMap, μHE, euclideanHausdorffMeasure_eq_volume, tendsto_integral_filter_of_dominated_convergence available)`
- `lake env lean -DautoImplicit=false /tmp/c1pt-decomp-k7q2/Types.lean (four child types in comparator scope; ContinuousLinearMap.det/adjoint/continuous_det available)`
- `lake env lean -DautoImplicit=false /tmp/c1pt-decomp-k7q2/Assembly.lean (parent from child stubs + comparator-style targets)`
- `lake env lean -DautoImplicit=false /tmp/c1pt-decomp-k7q2/{Area,Analysis,Combined}.lean (full draft proofs of the four children and the parent; #print axioms)`
- `sed -n book/chapter-02.txt 735-800 (Simon (3.1)-(3.5)); sed -n book/chapter-03.txt 100-130 (Theorem 1.6 '⇒')`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Linear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-18e8208cd7/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-18e8208cd7/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/c1pt-decomp-k7q2/Avail.lean`
- `/tmp/c1pt-decomp-k7q2/Types.lean`
- `/tmp/c1pt-decomp-k7q2/Assembly.lean`
- `/tmp/c1pt-decomp-k7q2/Area.lean`
- `/tmp/c1pt-decomp-k7q2/Analysis.lean`
- `/tmp/c1pt-decomp-k7q2/Combined.lean`
- `/tmp/c1pt-decomp-k7q2/statements.json`

Pins and scope.
- The snapshot manifest (project b4d606db, Mathlib 25730c7c) matches the workspace.
- The comparator replays this scope: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end.
- Children are declared as `theorem Submission.X` in namespace GMT.Ch07, as in accepted commits 713eebc5c1 and 7c29ce33ec.

What is available.
- SimonGMT Chapter03.Rectifiable defines blowUpMap and HasApproximateTangentSpaceAt (finrank P = n and a Tendsto over 𝓝[>] 0 for every f ∈ C_c).
- Chapter02.WeightedArea.integral_area_formula_of_injective_derivative is the Bochner area formula, valid for every integrand. Its olean is prebuilt, and accepted nodes already import it.
- Chapter02.Area gives areaJacobianAt = √det(Df*∘Df) (areaJacobianAt_eq_sqrt_det_adjoint_comp).
- After import GMT.Ch07.Submission alone, normDet, areaJacobianAt and continuous_normDet are unknown. ContinuousLinearMap.adjoint, ContinuousLinearMap.det and ContinuousLinearMap.continuous_det are available. So child types state the Jacobian as Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det).
- The snapshot Mathlib has every analytic tool the proofs use, located by rg: dominated convergence (Integral/DominatedConvergence.lean:67), HasFDerivAt.lim (FDeriv/Basic.lean:333), ContinuousLinearMap.fderiv (FDeriv/Linear.lean:79), setIntegral_eq_of_subset_of_forall_sdiff_eq_zero and setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:466, 486), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:187), ContinuousLinearMap.continuous_det (Normed/Module/FiniteDimension.lean:175), LinearMap.finrank_range_of_inj (Dimension/Finrank.lean:127), LinearMap.coe_range (Submodule/Range.lean:60), Continuous.bounded_above_of_compact_support (Normed/Group/Bounded.lean:153), tendsto_inv_nhdsGT_zero (Algebra/Order/Field.lean:61).

DAG.
- The selected node is at depth 5 with max_depth 6, so a split is allowed and children are leaves.
- It has no children.
- The four new names have 0 matches anywhere.
- Related nodes (pit_*, ptd_piece_image_approxTangent_ae, codim1_lur_piece_image_approxTangent_ae) are unaccepted and have different types, so nothing is reused.

Lean evidence.
- All four child types elaborate in the exact comparator scope and pass validate_lean_statement.
- The parent is proved from them, and comparator-style `exact Submission.X` targets check.
- Complete draft proofs of all four children compile together with the parent assembly (Combined.lean). #print axioms for the parent and its target: [propext, Classical.choice, Quot.sound].
