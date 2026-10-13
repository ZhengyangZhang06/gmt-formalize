# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1`
- Child DAG node: `root.regular_set_dense-a1.mass_eq_weight-a1.weight_le_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 3–6.

Notation. H := μHE[n]; M := R.carrier; θ := R.mult; ξ := R.orient; μ := R.measure = (H⌞M).withDensity θ. F := Covector (Euclid P) n with operator norm ‖·‖. N := covectorEuclideanNorm.

1. Orientation facts. By the sibling theorem rsd_mw_unit_orientation_dual, fix a continuous linear J : MultiVector P n → F such that IsUnitOrientationOf ξ₀ Q implies (∀ α, |ξ₀(α)| ≤ N(α)), N(J(ξ₀)) = 1 and ξ₀(J(ξ₀)) = 1.
- Let G be the set of x for which IsUnitOrientationOf (ξ x) Q holds for some Q. By R.orients, H⌞M-a.e. x lies in G.
- μ = (H⌞M).withDensity θ is absolutely continuous with respect to H⌞M. So μ-a.e. x lies in G, and the same holds for every measure absolutely continuous with respect to μ.
- For x ∈ G: (a) |ξ(x)(α)| ≤ N(α) for all α; (b) N(J(ξ(x))) = 1 and ξ(x)(J(ξ(x))) = 1; (c) ‖ξ(x)‖ ≤ 1, because ξ(x)(α) = ±α(τ) for an orthonormal τ and |α(τ)| ≤ ‖α‖·∏_i ‖τ_i‖ = ‖α‖.

2. Reduction. It suffices to show c < T.massOn W for every c ∈ [0, ∞] with c < μ(W). Indeed, if T.massOn W < μ(W), taking c := T.massOn W would give T.massOn W < T.massOn W. Fix such a c. Then c < ∞; put c₀ := c.toReal ≥ 0, so c = ENNReal.ofReal c₀.

3. Choice of K and V. For j ≥ 1 let K_j := {y : ‖y‖ ≤ j and B(y, 1/j) ⊆ W}.
- K_j is closed (if y_k → y with B(y_k, 1/j) ⊆ W, then B(y, 1/j) ⊆ W) and bounded, hence compact. The K_j increase with j, and their union is W because W is open.
- By continuity of μ from below, μ(K_j) → μ(W) > c. Fix K := K_j with μ(K) > c.
- Alternative: (Measure.InnerRegularWRT.isCompact_isClosed μ).trans (Measure.InnerRegularWRT.of_pseudoMetrizableSpace μ) gives such a compact K ⊆ W directly, for any measure μ on ℝ^P.
- ℝ^P is locally compact Hausdorff and K ⊆ W with W open. So there is an open V with K ⊆ V, closure V compact and closure V ⊆ W.
- Then μ(V) ≥ μ(K) > c. Also μ(V) ≤ μ(closure V) = ∫⁻_{M ∩ closure V} θ dH < ∞ by R.locallyIntegrable_mult, since closure V is a compact subset of W ⊆ U. (For measurable A, μ(A) = ∫⁻_{M∩A} θ dH by the definitions of withDensity and restriction.)
- So c₀ < μ(V).toReal. Put ε := (μ(V).toReal − c₀)/2 > 0.

4. Data for the approximation theorem. Let ν := μ⌞V, the restriction of μ to V.
- ν(ℝ^P) = μ(V) < ∞, so ν is a finite measure.
- ν(ℝ^P ∖ V) = μ((ℝ^P ∖ V) ∩ V) = 0; the complement of the open set V is measurable.
- Let β(x) := J(ξ(x)). ξ is a.e.-strongly measurable for H⌞M (field R.aestronglyMeasurable_orient) and J is continuous, so β is a.e.-strongly measurable for H⌞M, hence for ν (ν ≪ μ ≪ H⌞M).
- J is continuous and linear, so it is bounded on the unit ball. Continuity at 0 gives δ > 0 with ‖J(w)‖ < 1 whenever ‖w‖ < δ; by homogeneity, ‖J(w)‖ ≤ C_J := 2/δ whenever ‖w‖ ≤ 1.
- For ν-a.e. x (x ∈ G), ‖β(x)‖ ≤ C_J by 1(c), and N(β(x)) = 1 ≤ 1 by 1(b).
- Lean note: do not use ‖J‖. The norm instance on MultiVector P n →L[ℝ] Covector (Euclid P) n is not synthesized in the pinned Mathlib. Obtain C_J from Metric.continuous_iff applied to J at 0, with J.continuous retyped to the metric topology (a definitional equality Lean accepts).
- A ν-a.e. bounded, a.e.-strongly measurable function on a finite measure space is integrable, so β ∈ L¹(ν; F).

5. Approximation. Apply the sibling theorem rsd_mw_exists_testForm_approx to P, n, ν, V, β and ε. This gives ω : DifferentialForm (Euclid P) n with IsTestForm ω, tsupport ω ⊆ V, N(ω(x)) ≤ 1 for all x, and ∫⁻ ENNReal.ofReal(N(ω(x) − β(x))) dν(x) < ENNReal.ofReal ε.

6. Admissibility. tsupport ω ⊆ V ⊆ W ⊆ U. So ω̃ := ⟨ω, ⟨IsTestForm ω, tsupport ω ⊆ U⟩⟩ ∈ TestFormOn U n, and ω̃ ∈ massAdmissibleOn U n W (tsupport ω ⊆ W and N(ω(x)) ≤ 1). Hence ENNReal.ofReal(T ω̃) ≤ T.massOn W (GeometricCurrentOn.le_massOn).

7. Computing T ω̃. Let h(x) := ξ(x)(ω(x)).
- By R.Represents T, T ω̃ = R.action ω = ∫ θ(x)·h(x) d(H⌞M)(x).
- μ is H⌞M with the measurable density θ, viewed as an ℝ≥0-valued function. So ∫ h dμ = ∫ θ·h d(H⌞M); this identity for integrals against a measure with density holds for every h, integrable or not.
- If x ∉ V, then x ∉ tsupport ω, so ω(x) = 0 and h(x) = ξ(x)(0) = 0. Therefore ∫ h dμ = ∫_V h dμ = ∫ h dν.
Thus T ω̃ = ∫ h dν.

8. Estimate.
- h is a.e.-strongly measurable for ν: ξ is, ω is continuous, and the evaluation map (L, a) ↦ L(a) is continuous. Also |h(x)| ≤ N(ω(x)) ≤ 1 for ν-a.e. x by 1(a). So h ∈ L¹(ν).
- Put d(x) := N(ω(x) − β(x)) ≥ 0. d is a.e.-strongly measurable (N is continuous), and ∫⁻ ENNReal.ofReal(d) dν < ENNReal.ofReal ε < ∞. So d ∈ L¹(ν) and ∫ d dν = (∫⁻ ENNReal.ofReal(d) dν).toReal < ε.
- For ν-a.e. x (x ∈ G), by linearity of ξ(x) and 1(a), 1(b): h(x) = ξ(x)(β(x)) + ξ(x)(ω(x) − β(x)) ≥ 1 − N(ω(x) − β(x)) = 1 − d(x).
- Integrating: T ω̃ = ∫ h dν ≥ ∫ (1 − d) dν = ν(ℝ^P).toReal − ∫ d dν > μ(V).toReal − ε = (μ(V).toReal + c₀)/2 > c₀.

9. Conclusion. Since T ω̃ > c₀ ≥ 0, c = ENNReal.ofReal c₀ < ENNReal.ofReal(T ω̃) ≤ T.massOn W. As c < μ(W) was arbitrary, R.measure W = μ(W) ≤ T.massOn W. The proof does not use the openness of U.

Lean route, checked against the frozen types of the two siblings:
- le_of_forall_lt;
- Measure.InnerRegularWRT for K;
- exists_open_between_and_isCompact_closure;
- withDensity_apply with Measure.restrict_restrict and R.locallyIntegrable_mult;
- isFiniteMeasure_restrict;
- withDensity_absolutelyContinuous with AEStronglyMeasurable.mono_ac;
- Integrable.mono' with integrable_const;
- integral_withDensity_eq_integral_smul with the density (R.mult x : ℝ≥0);
- setIntegral_eq_integral_of_forall_compl_eq_zero with image_eq_zero_of_notMem_tsupport;
- isBoundedBilinearMap_apply for measurability of h;
- hasFiniteIntegral_iff_ofReal and integral_eq_lintegral_of_nonneg_ae for d;
- integral_mono_ae;
- GeometricCurrentOn.le_massOn.

## Key steps

1. Fix J from rsd_mw_unit_orientation_dual. Then μ-a.e.: |ξ(α)| ≤ N(α), N(Jξ) = 1, ξ(Jξ) = 1 and ‖ξ‖ ≤ 1.
2. Given c < μ(W): compact K ⊆ W with μ(K) > c (exhaustion), then open V ⊇ K with compact closure in W, so c < μ(V) < ∞.
3. ν = μ⌞V is finite with ν(Vᶜ) = 0, and β = J∘ξ is ν-integrable with N(β) ≤ 1 ν-a.e.
4. rsd_mw_exists_testForm_approx gives a test form ω with tsupport ⊆ V, N(ω) ≤ 1 and ∫⁻ ofReal N(ω − β) dν < ε. It is admissible for M_W(T).
5. T ω = ∫ ξ(ω) dν (withDensity, ω = 0 off V) ≥ ν(ℝ^P) − ∫ N(ω − β) dν > μ(V) − ε > c, so c < M_W(T).

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
