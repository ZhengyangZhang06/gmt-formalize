# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.radius-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3 and 5 of the supplied proof (Simon Ch. 6, 8.2 (2)–(3): radii where (F^{1/n})' is controlled, and F' = nF^{(n−1)/n}(F^{1/n})').

1. For r ∈ ℝ let F(r) := μ(B_r(x₁)), a finite real number (B_r(x₁) ⊆ B̄_r(x₁), which is compact). F is nondecreasing and F(r) = 0 for r ≤ 0 (the ball is empty). Let G(r) := F(r)^{1/n} (real power of a nonnegative number); G is nondecreasing, G(r) = 0 for r ≤ 0, and G(r)^n = F(r) for every r (Real.rpow_inv_natCast_pow, n ≥ 1).

2. From μ(B_s(x₁)) < (as)^n we get F(s) < (as)^n and hence G(s) < as, because u ↦ u^{1/n} is strictly increasing on [0, ∞) and as > 0.

3. Let G' := deriv G (equal to 0 where G is not differentiable); G' ≥ 0 everywhere (Monotone.deriv_nonneg). Since G is monotone on [0, s], Mathlib MonotoneOn.intervalIntegrable_deriv and MonotoneOn.intervalIntegral_deriv_mem_uIcc show that G' is integrable on [0, s] and ∫_0^s G' ≤ G(s) − G(0) = G(s) < as.

4. Let E := {r ∈ (0, s) : G'(r) ≤ 2a}; it is measurable (deriv G is measurable, measurable_deriv). E has positive Lebesgue measure: otherwise G'(r) > 2a for a.e. r ∈ (0, s), and then ∫_0^s G' ≥ ∫_0^s 2a = 2as > as, contradicting step 3.

5. The following sets are Lebesgue-null: N (by hypothesis); D := {r : G is not differentiable at r} (Lebesgue's theorem for monotone functions, Mathlib Monotone.ae_differentiableAt); and Q := {r : μ(∂B_r(x₁)) > 0}, which is countable because the spheres ∂B_r(x₁), r ∈ ℝ, are pairwise disjoint closed (measurable) sets and μ is σ-finite (ℝ^P is a countable union of compact balls of finite μ-measure; Mathlib Measure.countable_meas_pos_of_disjoint_iUnion, whose SFinite instance is obtained by registering IsFiniteMeasureOnCompacts μ from the hypothesis). Since E has positive measure, E ⊄ N ∪ D ∪ Q; choose ρ ∈ E ∖ (N ∪ D ∪ Q). Then 0 < ρ < s, ρ ∉ N, μ(∂B_ρ(x₁)) = 0, G is differentiable at ρ and G'(ρ) ≤ 2a.

6. Since F = G^n, F is differentiable at ρ with F'(ρ) = n·G(ρ)^{n−1}·G'(ρ) ≤ 2na·G(ρ)^{n−1} = 2na·F(ρ)^{(n−1)/n}, because G(ρ) ≥ 0 and G(ρ)^{n−1} = (F(ρ)^{1/n})^{n−1} = F(ρ)^{(n−1)/n}.

7. For 0 < h < ρ every x with ρ − h < |x − x₁| < ρ lies in B_ρ(x₁) ∖ B_{ρ−h}(x₁), so, the measures being finite and B_{ρ−h}(x₁) ⊆ B_ρ(x₁), μ({ρ − h < |x − x₁| < ρ}) ≤ F(ρ) − F(ρ − h) and h⁻¹·μ({ρ − h < |x − x₁| < ρ}) ≤ h⁻¹(F(ρ) − F(ρ − h)). As h ↓ 0, h⁻¹(F(ρ) − F(ρ − h)) = (F(ρ + (−h)) − F(ρ))/(−h) → F'(ρ), by differentiability of F at ρ (hasDerivAt_iff_tendsto_slope_zero restricted to negative increments). Passing to [0, ∞] with ENNReal.ofReal (continuous and monotone), the liminf along h ↓ 0 of the left side is at most the limit of the right side: liminf_{h↓0} h⁻¹·μ({ρ − h < |x − x₁| < ρ}) ≤ F'(ρ) ≤ 2na·F(ρ)^{(n−1)/n} by step 6. ∎

## Key steps

1. F(r) = μ(B_r(x₁)) and G = F^{1/n} are nondecreasing, vanish for r ≤ 0, and G(s) < as.
2. ∫_0^s G' ≤ G(s) < as (MonotoneOn.intervalIntegral_deriv_mem_uIcc) forces {r ∈ (0,s) : G'(r) ≤ 2a} to have positive measure.
3. Remove the null sets N, the non-differentiability points of G, and the countable set of radii with μ(∂B_r(x₁)) > 0.
4. At the chosen ρ, F' = nG^{n−1}G' ≤ 2naF^{(n−1)/n}.
5. h⁻¹μ{ρ−h < |x−x₁| < ρ} ≤ h⁻¹(F(ρ) − F(ρ−h)) → F'(ρ), so the liminf is ≤ 2naF(ρ)^{(n−1)/n}.

## Reference use

### local-project

Queries:
- `cat manifest.json of the local-project snapshot (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); sed of GMT/Ch07/Contract.lean (IMRep, IMRep.measure, IMRep.Represents, IsIntegerMultiplicity, Sub instance on GeometricCurrentOn, unitBallVolume, Euclid)`
- `python3 -I scan of dag.json: frozen lean_statement of lower_density-a1 (identical to the handoff) and of the sibling isoperimetric-a1 (cbr_isoperimetric_filling); sibling statements convergence_tools-a1, restrict_unique-a1, slice_limit-a1, cycle_im-a1; accepted nodes whose statements mention sphere, unitBallVolume, 𝓝[>] 0 or (S - T).support (lcmp_exists_good_slice_level, cmc_ml_massOn_eq_of_disjoint_sub_support, dtc_measure_ball_eq_of_null_sphere, cmc_massOn_le_of_le_near_support: different statements, not reusable verbatim); lean_name collision check of the 7 cbrld_ names against 732 DAG names (none) and grep -rl over GMT/ and .lake/packages/simongmt (none)`
- `sed/cat of SimonGMT Chapter06/{Forms,Currents,Mass,FormSupNorm,CurrentLocalEquality}.lean: GeometricCurrentOn, TestFormOn, exteriorDerivativeTestOn, boundary, boundary_boundary, massOn, massAdmissibleOn, le_massOn, mass, covectorEuclideanNorm(_neg,_nonneg), zeroRegion, VanishesOn, support, WeaklyConvergesOn.massOn_le_liminf`
- `grep -rn in the Mathlib snapshot for: exists_disjoint_closedBall_covering_ae, MonotoneOn.intervalIntegrable_deriv, MonotoneOn.intervalIntegral_deriv_mem_uIcc, Monotone.ae_differentiableAt, Monotone.deriv_nonneg, measurable_deriv, countable_meas_pos_of_disjoint_iUnion, euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton, def extDeriv, Filter.EventuallyEq.extDeriv_eq, extDeriv_apply, ContinuousAlternatingMap.curryLeft, alternatizeUncurryFin_curryLeft, alternatizeUncurryFin_smul, Nat.cast_smul_eq_nsmul, ContDiffBump, exists_contDiff_tsupport_subset, integral_iUnion, frequently_lt_of_liminf_lt, hasDerivAt_iff_tendsto_slope_zero, ContinuousAlternatingMap.le_opNorm, lipschitzWith_of_nnnorm_fderiv_le, norm_image_sub_le_of_norm_fderiv_le, LipschitzWith.dist_left, HasCompactSupport.fderiv, measure_iUnion_null, ae_iff, setIntegral_eq_integral_of_forall_compl_eq_zero, lintegral_singleton, withDensity_apply, thickening_mono, Real.rpow_inv_natCast_pow, Real.rpow_add', Real.mul_rpow, ContinuousLinearMap.aestronglyMeasurable_comp₂`
- `verifier/lean_contract.py validate_lean_statement on all 7 statements (pass) and verifier/gmt-compare.py contract_scope/child_modules (scope replay: open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt); noncomputable section; end)`
- `grep -n depends_on and sed -n 1850,1960p, 6520,6640p of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (child depends_on resolved only among sibling keys; _dependency_problem; _existing_lean_name_problem)`
- `lake env lean /tmp/cbrld-decomp-x9f3/Types.lean (7 child types elaborate), /tmp/cbrld-decomp-x9f3/Assembly.lean (#print axioms CbrldCheck.assembly: propext, Classical.choice, Quot.sound), /tmp/cbrld-decomp-x9f3/LocalWiring.lean and /tmp/cbrld-decomp-x9f3/NullWiring.lean (interface skeletons typecheck)`
- `sed -n 2280,2480p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt (Simon Ch. 6, 8.2 proof (1)–(6) and footnote 5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b16b774435/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/NatInt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cbrld-decomp-x9f3/Types.lean`
- `/tmp/cbrld-decomp-x9f3/Assembly.lean`
- `/tmp/cbrld-decomp-x9f3/LocalWiring.lean`
- `/tmp/cbrld-decomp-x9f3/NullWiring.lean`

Nothing in the snapshot (project, SimonGMT or Mathlib) or among the accepted DAG nodes gives, in a form that can be reused, any of: the cone inequality for small cycles, the sphere slices of ISP cycles, the degree-0 mass gap, good-radius selection, or the covering inequality. SimonGMT Chapter06 supplies only the current, mass, support and boundary definitions together with le_massOn and boundary_boundary. Mathlib supplies the generic tools cited in the child proofs; every cited name was found in the pinned snapshot. Children can depend only on siblings, so (VO), (MR), (SL) and the conclusion (ISO) of cbr_isoperimetric_filling are carried verbatim as hypotheses. All 7 child statements elaborate in the replayed contract scope and pass the verifier's lexical check. A Lean proof that uses only hypotheses derives the frozen parent type from local_filling, null_set and the frozen cbr_isoperimetric_filling type, with axioms propext, Classical.choice and Quot.sound. None of the 7 cbrld_ names collides with the 732 DAG names.
