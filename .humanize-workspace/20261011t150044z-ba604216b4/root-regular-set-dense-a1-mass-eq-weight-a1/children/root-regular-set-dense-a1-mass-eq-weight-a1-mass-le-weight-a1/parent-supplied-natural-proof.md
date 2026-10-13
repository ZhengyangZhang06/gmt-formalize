# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1`
- Child DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.mass_le_weight-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2.

Notation. H := μHE[n]; M := R.carrier; θ := R.mult; ξ := R.orient; μ := R.measure = (H⌞M).withDensity θ, with θ viewed in [0, ∞]; N := covectorEuclideanNorm.

1. Apply the sibling theorem rsd_mw_unit_orientation_dual to P and n, and fix the resulting J. Only its conclusion (i) is used: whenever IsUnitOrientationOf ξ₀ Q, |ξ₀(α)| ≤ N(α) for every covector α.

2. By the field R.orients, for H⌞M-a.e. x there is Q with IsUnitOrientationOf (ξ x) Q. Let G be the set of x with |ξ(x)(α)| ≤ N(α) for all α. By step 1, H⌞M-a.e. x lies in G.

3. By definition, T.massOn W = sSup {ENNReal.ofReal (T ω) : ω ∈ massAdmissibleOn U n W}. Here ω ∈ massAdmissibleOn U n W means ω ∈ TestFormOn U n, tsupport ω ⊆ W, and N(ω(x)) ≤ 1 for all x. So it suffices to prove ENNReal.ofReal (T ω) ≤ μ(W) for every such ω.

4. Fix such an ω. S := tsupport ω is closed, hence measurable, and S ⊆ W. Let f(x) := θ(x)·ξ(x)(ω(x)). By R.Represents T, T ω = R.action ω = ∫ f d(H⌞M).

5. Let x ∈ G.
- If x ∈ S, then |f(x)| = θ(x)·|ξ(x)(ω(x))| ≤ θ(x)·N(ω(x)) ≤ θ(x).
- If x ∉ S, then x lies outside the closure of the support of ω, so ω(x) = 0 and f(x) = θ(x)·ξ(x)(0) = 0.
Hence ‖f(x)‖ₑ = ENNReal.ofReal |f(x)| ≤ θ(x)·1_S(x) for H⌞M-a.e. x.

6. For every real-valued f, integrable or not (a non-integrable f has Bochner integral 0): ENNReal.ofReal (∫ f d(H⌞M)) ≤ ‖∫ f d(H⌞M)‖ₑ ≤ ∫⁻ ‖f‖ₑ d(H⌞M).
- By step 5 and monotonicity of the lower integral (a.e. version), ∫⁻ ‖f‖ₑ d(H⌞M) ≤ ∫⁻ θ·1_S d(H⌞M) = ∫⁻_S θ d(H⌞M) = μ(S). The last equality is the definition of the measure with density θ, evaluated on the measurable set S.
- Finally μ(S) ≤ μ(W), because S ⊆ W.

7. Thus ENNReal.ofReal (T ω) ≤ μ(W) for every admissible ω. Taking the supremum gives T.massOn W ≤ R.measure W. The proof uses neither the openness of U or W nor the local integrability of θ.

Lean route, checked against the frozen type of the sibling: sSup_le; Real.enorm_eq_ofReal_abs; enorm_integral_le_lintegral_enorm; lintegral_mono_ae with filter_upwards [R.orients]; image_eq_zero_of_notMem_tsupport; lintegral_indicator with withDensity_apply on the closed set tsupport ω; measure_mono.

## Key steps

1. Fix J from rsd_mw_unit_orientation_dual. Then, H⌞M-a.e., |ξ(x)(α)| ≤ N(α) for all α.
2. Reduce to ofReal(T ω) ≤ μ(W) for each ω ∈ massAdmissibleOn U n W.
3. For f = θ·ξ(ω), H⌞M-a.e. ‖f‖ₑ ≤ θ·1_{tsupport ω}, since ω = 0 off its tsupport and |ξ(ω)| ≤ N(ω) ≤ 1.
4. ofReal(∫ f) ≤ ‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ ≤ ∫⁻_{tsupport ω} θ d(H⌞M) = μ(tsupport ω) ≤ μ(W).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `python3 -I scan of dag.json: node ids, lean_name, status; related nodes matching mass_eq_measure|imrep_mass_and_support|imrep_mass_formula|imrep_measure_unique|support_iff_weight`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp lake-manifest.json local-references/123e8435b4a2469b/project/lake-manifest.json`
- `grep -n '^def \|^theorem \|^structure \|^abbrev ' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean Chapter06/Mass.lean; cat Chapter06/{Mass,Forms,FormSupNorm,Representation}.lean`
- `grep -rln 'Cauchy-Binet\|Cauchy–Binet\|CauchyBinet\|cauchy_binet\|cauchyBinet' mathlib/Mathlib; grep -rn 'Binet' mathlib/Mathlib`
- `grep -rn 'theorem Integrable.exists_hasCompactSupport\|theorem MemLp.exists_hasCompactSupport' mathlib/Mathlib`
- `grep -n 'of_sigmaCompactSpace_of_isLocallyFiniteMeasure' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `grep -rn 'exists_contDiff_support_eq_eq_one_iff\|exists_contDiff_tsupport_subset\|exists_contMDiff_zero_iff_one_iff_of_isClosed' mathlib/Mathlib`
- `cat mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `grep -rn 'HasCompactSupport.contDiff_convolution_left\|dist_normed_convolution_le\|Convex.integral_mem' mathlib/Mathlib`
- `grep -rn 'integral_withDensity_eq_integral_smul\|setIntegral_eq_integral_of_forall_compl_eq_zero\|exists_open_between_and_isCompact_closure\|exists_compact_between' mathlib/Mathlib`
- `grep -rn 'enorm_integral_le_lintegral_enorm\|ofReal_integral_eq_lintegral_ofReal' mathlib/Mathlib/MeasureTheory/Integral/Bochner/*.lean; grep -rn 'withDensity_apply\|withDensity_absolutelyContinuous\|theorem le_of_forall_lt' mathlib/Mathlib`
- `grep -rn 'rsd_mw_\|rsd_unit_orientation\|rsd_massOn_le\|rsd_measure_le\|rsd_exists_testForm' .humanize GMT`
- `sed -n 225,285p book/chapter-06.txt; sed -n 755,770p book/chapter-06.txt`
- `sed -n 480,570p verifier/gmt-compare.py`
- `lake env lean /tmp/rsd-mw-split/Children.lean`
- `lake env lean /tmp/rsd-mw-split/Assembly.lean`
- `lake env lean /tmp/rsd-mw-split/Glue.lean`
- `lake env lean /tmp/rsd-mw-review/GlueFull.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-mass-eq-weight-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/rsd-mw-split/Children.lean`
- `/tmp/rsd-mw-split/Assembly.lean`
- `/tmp/rsd-mw-split/Glue.lean`
- `/tmp/rsd-mw-review/GlueFull.lean`

Snapshot integrity (project b4d606d, Mathlib 25730c7c): the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and lake-manifest.json matches.

No local declaration states mass = weight for IMRep, or the Euclidean-norm dual bound for unit simple n-vectors:
- simongmt Chapter06 provides covectorEuclideanNorm (with _nonneg, _zero and _neg), massAdmissibleOn, massOn, le_massOn and massOn_mono.
- Representation.lean leaves the mass bridge pending.
- Mathlib has no Cauchy–Binet formula (grep finds no match), so child 1 derives the needed identity from the expansion α(v) = Σ_I D_I(v)α(e_I).

Reusable Mathlib tools located:
- Integrable.exists_hasCompactSupport_integral_sub_le (ContinuousMapDense.lean:226);
- Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (Regular.lean:1183);
- UniformContinuous.exists_contDiff_dist_le (BumpFunction/SmoothApprox.lean);
- exists_contDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:789);
- exists_open_between_and_isCompact_closure (Separation/Regular.lean:364);
- integral_withDensity_eq_integral_smul (Bochner/ContinuousLinearMap.lean:251);
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486);
- enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333);
- withDensity_apply and withDensity_absolutelyContinuous (WithDensity.lean);
- le_of_forall_lt (Order/Basic.lean:352).
The ContinuousMapDense and SmoothApprox modules are outside the import closure of GMT.Ch07.Submission; this is noted in child 3.

Lean checks in the replayed contract scope:
- All four child types elaborate.
- The parent assembly from children 2 and 4 depends only on propext, Classical.choice and Quot.sound.
- The glue facts (withDensity conversion, restriction, localization) depend only on the same axioms.
- The reviewer's proofs of child 2 from child 1, and of child 4 and the parent from children 1 and 3, depend only on the same axioms.

Names: no rsd_mw_ name occurs in the run directory or GMT/. The parallel mass = measure nodes in other branches have no children yet, so no reserved names collide.
