# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.slice-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 4 of the supplied proof (Simon Ch. 6, 8.2 (1)–(2) and 4.9: for a cycle, ∂(T⌞B_r(x₁)) is integer multiplicity for a.e. r and its mass is bounded by the derivative of r ↦ μ(B_r(x₁))).

1. Let f(x) := dist(x, x₁) = |x − x₁|. f is 1-Lipschitz (LipschitzWith.dist_left), {x : f(x) < t} = B_t(x₁) and {x : t − h < f(x) < t} = {x : t − h < |x − x₁| < t}. Let μ' := 0 (the zero measure) and ξ' := 0 (the zero field of d-vectors). Then (μ', ξ') is an admissible representation of ∂C = 0: μ' is finite on compacts, ξ' is strongly measurable, |ξ'(x)(α)| = 0 ≤ |α|, and ∂C(η) = 0 = ∫ξ'(η)dμ' for every test form η.

2. Apply the ISP hypothesis of C to the representations (μ, ξ) of C and (μ', ξ') of ∂C, to f and to L = 1: for L¹-a.e. t, for all currents A ∈ 𝒟_{d+1}(ℝ^P) and B ∈ 𝒟_d(ℝ^P) with A(ω) = ∫_{f<t} ξ(ω)dμ and B(η) = ∫_{f<t} ξ'(η)dμ' for all test forms, ∂A − B is integer multiplicity. Let N be the set of t ∈ ℝ at which this property fails; by ae_iff, N is Lebesgue-null.

3. Apply (SL) with k := d, U := ℝ^P (open), T := C, the representations (μ, ξ) and (μ', ξ'), f and L := 1; all its hypotheses hold (finiteness on compacts, measurability, the pointwise bounds, the representations of C and of ∂C from step 1, f Lipschitz). This gives currents A_t ∈ 𝒟_{d+1}(ℝ^P), B_t ∈ 𝒟_d(ℝ^P), t ∈ ℝ, with A_t(ω) = ∫_{f<t} ξ(ω)dμ, B_t(η) = ∫_{f<t} ξ'(η)dμ' = 0 (an integral against the zero measure), ∂A_t(η) = B_t(η) whenever tsupport η ∩ {f = t} = ∅, and M_W(∂A_t − B_t) ≤ 1·liminf_{h↓0} h⁻¹μ(W ∩ {t − h < f < t}) for every open W.

4. Fix ρ > 0 with ρ ∉ N and put A := A_ρ. Then A(ω) = ∫_{B_ρ(x₁)} ξ(ω)dμ for every test form ω. All values of B_ρ vanish, so B_ρ = 0 and ∂A − B_ρ = ∂A (extensionality of currents).

5. (Integer multiplicity.) Since ρ ∉ N, the property of step 2 holds at t = ρ; applied to A_ρ and B_ρ, whose values are given by the formulas of step 3, it shows that ∂A − B_ρ = ∂A is integer multiplicity.

6. (Support.) Let y ∈ ℝ^P with y ∉ ∂B_ρ(x₁), let r := |dist(y, x₁) − ρ|/2 > 0 and W' := B_r(y), an open set whose closure B̄_r(y) is compact. For z ∈ W', |dist(z, x₁) − dist(y, x₁)| ≤ |z − y| < r < |dist(y, x₁) − ρ|, so dist(z, x₁) ≠ ρ; hence every test form η with tsupport η ⊆ W' satisfies tsupport η ∩ {f = ρ} = ∅ and therefore ∂A(η) = B_ρ(η) = 0 by step 3. Thus ∂A vanishes on W', so W' is contained in the zero region of ∂A and y ∉ spt ∂A. Hence spt ∂A ⊆ ∂B_ρ(x₁).

7. (Mass.) Step 3 with the open set W := ℝ^P gives M(∂A) = M_{ℝ^P}(∂A − B_ρ) ≤ 1·liminf_{h↓0} h⁻¹μ(ℝ^P ∩ {ρ − h < f < ρ}) = liminf_{h↓0} h⁻¹μ({x : ρ − h < |x − x₁| < ρ}) (the factor (1 : ℝ≥0) cast to [0, ∞] is 1, and ℝ^P ∩ X = X). ∎

## Key steps

1. Slice by the 1-Lipschitz f = |· − x₁|, representing ∂C = 0 by the zero measure and zero field.
2. ISP yields a Lebesgue-null set N outside of which ∂A_t − B_t is integer multiplicity.
3. (SL) gives A_t = C⌞{f < t}, B_t = 0, the vanishing of ∂A_t off {f = t} and the liminf mass bound.
4. For ρ ∉ N: ∂A_ρ is integer multiplicity, spt ∂A_ρ ⊆ ∂B_ρ(x₁), and M(∂A_ρ) ≤ liminf_h h⁻¹μ{ρ − h < |x − x₁| < ρ}.

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
