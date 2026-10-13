# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the covering part of Step 7 and the measure bookkeeping of Step 9 of the supplied proof (Simon Ch. 6, 8.2: pairwise disjoint closed balls covering μ-almost all of the low-density set, with Σμ(B_i) ≤ μ(W)), stated for a fixed bounded density g (in the parent g = ξ(ω) for a fixed test form ω).

1. (σ-finiteness and integrability.) ℝ^P = ⋃_k B̄_k(0) and every closed ball is compact, so μ(B̄_k(0)) < ∞; hence μ is σ-finite, in particular s-finite. (In Lean, register IsFiniteMeasureOnCompacts μ from the hypothesis ∀ K compact, μ K < ∞; the instances IsLocallyFiniteMeasure, SigmaFinite and SFinite on Euclid P then follow, as required by Besicovitch.exists_disjoint_closedBall_covering_ae.) Since g is μ-a.e. strongly measurable and |g| ≤ 1 μ-a.e., g is integrable on every measurable set of finite μ-measure, in particular on W and on every closed ball.

2. (Admissible radii.) For x ∈ ℝ^P let f(x) := {ρ > 0 : B̄_ρ(x) ⊆ W and ∫_{B̄_ρ(x)} g dμ ≤ θ·μ(B̄_ρ(x))}. For every x ∈ E and δ > 0, f(x) ∩ (0, δ) ≠ ∅: since W is open and x ∈ E ⊆ W, there is r > 0 with B_r(x) ⊆ W; the hypothesis applied with min(δ, r) gives ρ ∈ (0, min(δ, r)) with the integral inequality, and B̄_ρ(x) ⊆ B_r(x) ⊆ W.

3. (Besicovitch covering.) ℝ^P is a finite-dimensional real normed space, hence second countable with the Besicovitch covering property, and μ is an s-finite Borel measure. By Mathlib Besicovitch.exists_disjoint_closedBall_covering_ae (applied to μ, f, the set E and R ≡ 1) there are a countable set t ⊆ E and r : ℝ^P → ℝ such that r(x) ∈ f(x) for every x ∈ t, the closed balls B_x := B̄_{r(x)}(x), x ∈ t, are pairwise disjoint, and μ(E ∖ V) = 0 for V := ⋃_{x∈t} B_x.

4. V is measurable (a countable union of closed sets) and V ⊆ W (each B_x ⊆ W because r(x) ∈ f(x)), so μ(V) ≤ μ(W) < ∞. Since E ⊆ V ∪ (E ∖ V), μ(E) ≤ μ(V) + μ(E ∖ V) = μ(V).

5. (Integral over V.) By countable additivity of μ and of the integral over the countable family of pairwise disjoint measurable sets B_x, x ∈ t (Mathlib measure_iUnion and MeasureTheory.integral_iUnion, using that g is integrable on V ⊆ W), μ(V) = Σ_{x∈t} μ(B_x), a convergent series of finite reals, and ∫_V g dμ = Σ_{x∈t} ∫_{B_x} g dμ, a series that converges absolutely because |∫_{B_x} g dμ| ≤ μ(B_x). Since r(x) ∈ f(x), every term satisfies ∫_{B_x} g dμ ≤ θ·μ(B_x); summing, ∫_V g dμ ≤ θ·Σ_{x∈t} μ(B_x) = θ·μ(V).

6. (Integral over W ∖ V.) Since g ≤ 1 μ-a.e., ∫_{W∖V} g dμ ≤ μ(W ∖ V) = μ(W) − μ(V) (finite measures, V ⊆ W).

7. (Conclusion.) ∫_W g dμ = ∫_{W∖V} g dμ + ∫_V g dμ ≤ μ(W) − μ(V) + θ·μ(V) = μ(W) − (1 − θ)·μ(V) ≤ μ(W) − (1 − θ)·μ(E), using 1 − θ ≥ 0 and μ(E) ≤ μ(V) from step 4 (all quantities are finite reals). ∎

## Key steps

1. μ is σ-finite and g is integrable on sets of finite measure.
2. Admissible radii f(x): closed balls inside W satisfying the integral inequality, available at arbitrarily small scales at every x ∈ E.
3. Besicovitch (exists_disjoint_closedBall_covering_ae): countable disjoint admissible balls B_x with μ(E ∖ ⋃B_x) = 0.
4. Countable additivity: ∫_V g ≤ θμ(V); and ∫_{W∖V} g ≤ μ(W) − μ(V).
5. Combine with μ(E) ≤ μ(V) and θ ≤ 1.

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
