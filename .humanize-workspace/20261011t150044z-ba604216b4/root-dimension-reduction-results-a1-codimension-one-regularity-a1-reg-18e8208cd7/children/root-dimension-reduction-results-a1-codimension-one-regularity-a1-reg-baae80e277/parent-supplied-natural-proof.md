# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1.c1_piece_tangent-a1.rescaled_integral_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 4–6 and the first half of step 7 of the parent proof. The continuous Jacobian J_g is replaced by an arbitrary continuous weight h. (The parent applies this with h = J_g, continuous by its step 2, and B = B_r(c).) The hypothesis m|v| ≤ |Dg(z)v| is the conclusion of parent step 1 at z; here it is assumed.
Notation: L := Dg(z) = fderiv ℝ g z. For s > 0:
- B_s := {b : z + sb ∈ B};
- φ_s(b) := s^{-1}(g(z + sb) − g(z));
- F_s(b) := h(z + sb)·f(φ_s(b));
- I(s) := ∫_{B_s} F_s dL^n.

1. (Radius R for f.) The support of f is compact, hence bounded: tsupport f ⊆ closedBall(0, R₀) for some R₀ ∈ ℝ. Put R := max(R₀, 1) > 0. If |y| > R then f(y) = 0: otherwise y ∈ tsupport f, so |y| ≤ R₀ ≤ R, a contradiction.

2. (Radius ρ₀.) B is open and z ∈ B, so there is ε > 0 with the open ball B_ε(z) ⊆ B. Put ρ₀ := ε/2 > 0. Then closedBall(z, ρ₀) ⊆ B_ε(z) ⊆ B.

3. (The compact set K.) Put K := closedBall(0, R/m) ⊆ ℝ^n and s₀ := mρ₀/R > 0.
(a) Let 0 < s ≤ s₀ and b ∈ K. Then |(z + sb) − z| = s|b| ≤ s₀·(R/m) = ρ₀, so z + sb ∈ closedBall(z, ρ₀) ⊆ B. In particular K ⊆ B_s.
(b) Let s > 0 and b ∈ B_s ∖ K. Then |b| > R/m, so m|b| > R (as m > 0). Since a := z + sb ∈ B, the hypothesis gives m·s|b| = m|a − z| ≤ |g(z + sb) − g(z)|. Hence |φ_s(b)| = s^{-1}|g(z + sb) − g(z)| ≥ m|b| > R. By step 1, f(φ_s(b)) = 0, so F_s(b) = 0.

4. (Localisation.) The condition 0 < s < s₀ holds eventually along 𝓝[>] 0. For such s:
- B_s is open, being the preimage of the open set B under the continuous map b ↦ z + sb; hence it is measurable;
- K ⊆ B_s by 3(a);
- F_s = 0 on B_s ∖ K by 3(b).
Therefore ∫_{B_s} F_s dL^n = ∫_K F_s dL^n (Mathlib setIntegral_eq_of_subset_of_forall_sdiff_eq_zero). So I(s) = ∫_K F_s dL^n eventually along 𝓝[>] 0.

5. (Uniform bound.)
- h is continuous on the compact set closedBall(z, ρ₀), so |h(a)| ≤ Λ for some Λ and all a ∈ closedBall(z, ρ₀).
- f is continuous with compact support, so |f(y)| ≤ C for some C and all y.
- For 0 < s < s₀ and b ∈ K, step 3(a) gives z + sb ∈ closedBall(z, ρ₀), hence |F_s(b)| ≤ ΛC.
- The constant ΛC is integrable on K because L^n(K) < ∞ (closed balls have finite Lebesgue measure).

6. (Measurability.) For each s, b ↦ F_s(b) is continuous. It is built from the continuous maps g, h and f, the affine map b ↦ z + sb, subtraction of the constant g(z), multiplication by s^{-1}, and a product of real functions. Hence it is a.e.-strongly measurable for L^n restricted to K.

7. (Pointwise limit.) Fix b ∈ ℝ^n.
- g is differentiable at z, so φ_s(b) = s^{-1}(g(z + sb) − g(z)) → Lb as s ↓ 0: this is the difference quotient in the direction b. In Mathlib use HasFDerivAt.lim with c(s) = s^{-1}, since |s^{-1}| → ∞ along 𝓝[>] 0.
- z + sb → z as s → 0, so h(z + sb) → h(z) by continuity of h.
- f(φ_s(b)) → f(Lb) by continuity of f.
Hence F_s(b) → h(z)·f(Lb).

8. (Dominated convergence.)
- The filter 𝓝[>] 0 on ℝ is countably generated.
- Steps 5–7 verify the hypotheses of dominated convergence along a filter (Mathlib tendsto_integral_filter_of_dominated_convergence) for L^n restricted to K, with bound ΛC.
- Hence ∫_K F_s dL^n → ∫_K h(z) f(Lb) dL^n(b) as s ↓ 0.
- By step 4, s ↦ I(s) and s ↦ ∫_K F_s agree eventually along 𝓝[>] 0. So I(s) → ∫_K h(z) f(Lb) dL^n(b).

9. (Identification of the limit.)
- If b ∉ K then |b| > R/m, so R < m|b| ≤ |Lb| by the hypothesis on L, and f(Lb) = 0 by step 1.
- Hence ∫_K h(z) f(Lb) db = ∫_{ℝ^n} h(z) f(Lb) db (Mathlib setIntegral_eq_integral_of_forall_compl_eq_zero) = h(z)·∫_{ℝ^n} f(Lb) db (integral_const_mul).
- Therefore I(s) → h(z)·∫_{ℝ^n} f(Dg(z)b) dL^n(b) as s ↓ 0. ∎

Implementation note (not part of the mathematics). Mathlib alone suffices. Useful names:
- Radius R: HasCompactSupport.isCompact, Bornology.IsBounded.subset_closedBall, subset_tsupport.
- Radius ρ₀: Metric.isOpen_iff, closedBall_subset_ball.
- Localisation: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, with IsOpen.preimage and IsOpen.measurableSet for B_s.
- Bounds: IsCompact.exists_bound_of_continuousOn, Continuous.bounded_above_of_compact_support.
- Dominated convergence: tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C), integrableOn_const with measure_closedBall_lt_top, ae_restrict_mem measurableSet_closedBall, Continuous.aestronglyMeasurable.
- Pointwise limit: HasFDerivAt.lim with tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero and simpa only [inv_inv]; Tendsto.mono_left nhdsWithin_le_nhds.
- Identification and conclusion: setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul, Tendsto.congr'.

## Key steps

1. Choose R > 0 with f = 0 off closedBall(0, R) and ρ₀ > 0 with closedBall(z, ρ₀) ⊆ B. Set K = closedBall(0, R/m) and s₀ = mρ₀/R.
2. For 0 < s ≤ s₀, K ⊆ B_s, and the integrand vanishes on B_s ∖ K because |φ_s(b)| ≥ m|b| > R. So I(s) = ∫_K F_s.
3. On K, F_s is continuous and |F_s| ≤ Λ·sup|f|, where Λ = max of |h| on closedBall(z, ρ₀). Pointwise F_s(b) → h(z) f(Dg(z)b), so dominated convergence along 𝓝[>] 0 gives ∫_K F_s → ∫_K h(z) f(Dg(z)b).
4. Off K, f(Dg(z)b) = 0 since |Dg(z)b| ≥ m|b| > R. So the limit equals h(z)·∫_{ℝ^n} f(Dg(z)b) db.

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
