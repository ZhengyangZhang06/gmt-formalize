# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.sheet_first_variation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 6(b) and the first equality of step 9 (the varifold v(M, θ) of Simon Ch. 4, 2.2–2.3). The parent asserts in 6(b) that the carrier and the regular surface agree H^n-a.e. near p, that θ is constant there, and that the approximate tangent planes of the carrier are the tangent planes of the surface; this child proves exactly these facts, using the density hypothesis and accepted lemmas in place of the sketched graph argument, and then evaluates the first variation. Conventions: B := B_ρ(p), H^n := μHE[n], ω_n := unitBallVolume n, μ := R.measure = θ·H^n⌞S, and T_xM := span(tangentSpace M x) with orthogonal projection P_x; tangentialDivergence n S X x = tr(P_{approxTangentPlane n S x} ∘ DX(x)) and R.firstVariation X = ∫_S θ(x)·tangentialDivergence n S X x dH^n(x) (contract definitions).
1. (Measure facts.) θ ≥ 1 on S, so μ(Sᶜ) = 0, and for every Borel A: H^n(A ∩ S) ≤ μ(A); thus a Borel μ-null set meets S in an H^n-null set, and a Borel set A with H^n(A ∩ S) = 0 is μ-null. For compact K ⊆ U, μ(K) = ∫_{S∩K} θ dH^n < ∞ (field locallyIntegrable_mult), hence H^n(S ∩ K) < ∞.
2. ((S ∩ B) ∖ M is H^n-null.) If x ∈ (S ∩ B) ∖ M then x ∉ spt T, since otherwise x ∈ spt T ∩ B = M ∩ B. So (S ∩ B) ∖ M ⊆ S ∖ spt T, which is H^n-null by the accepted lemma `Submission.imrep_carrier_sdiff_support_null` (U open, R represents T).
3. (θ = k H^n-a.e. on S ∩ B.) By the accepted lemma `Submission.rsd_ae_hasMassDensity_mult`, HasMassDensity T x θ(x) for μ-a.e. x. As H^n(S ∖ spt T) = 0 and spt T = U ∖ zeroRegion T is Borel, step 1 gives μ((spt T)ᶜ) = 0. For μ-a.e. x ∈ B therefore x ∈ spt T ∩ B, so HasMassDensity T x k by hypothesis and θ(x) = k by uniqueness of densities (accepted `Submission.dimred_cs_mi_hasMassDensity_unique`). The Borel set {x ∈ B : θ(x) ≠ k} is μ-null, hence (step 1) H^n-null within S.
4. ((M ∩ B) ∖ S is H^n-null.) Apply the accepted lemma `Submission.regcomp_atl_local_density_zero` to U (open) and S (Borel, H^n(S ∩ K) < ∞ for compact K ⊆ U by step 1): there is an H^n-null set Z such that H^n(S ∩ closedBall(x, r))/rⁿ → 0 as r ↓ 0 for every x ∈ U ∖ (S ∪ Z). Let x ∈ (M ∩ B) ∖ (S ∪ Z). Then x ∈ spt T ∩ B, so HasMassDensity T x k, i.e. M_{B_r(x)}(T)/(ω_n rⁿ) → k as r ↓ 0. For 0 < r < ρ − |x − p| we have B_r(x) ⊆ B ⊆ U, and by the accepted lemma `Submission.rsd_massOn_eq_measure` and step 3, M_{B_r(x)}(T) = μ(B_r(x)) = ∫_{S ∩ B_r(x)} θ dH^n = k·H^n(S ∩ B_r(x)) ≤ k·H^n(S ∩ closedBall(x, r)). Hence M_{B_r(x)}(T)/(ω_n rⁿ) ≤ (k/ω_n)·H^n(S ∩ closedBall(x, r))/rⁿ → 0 (0 < ω_n < ∞), so k = 0, contradicting k ≥ 1. Thus (M ∩ B) ∖ S ⊆ Z is H^n-null. Together with step 2, S ∩ B and M ∩ B coincide up to an H^n-null set.
5. (Approximate tangent planes.) By the field orients of R, for H^n-a.e. x ∈ S there is a subspace Q_x with HasApproximateTangentSpaceAt n S x Q_x and ξ(x) a unit orientation of Q_x; then finrank Q_x = n, and approxTangentPlane n S x = Q_x by the definition of approxTangentPlane and uniqueness (`HasApproximateTangentSpaceAt.unique`, SimonGMT Chapter03/Rectifiable.lean). Fix such an x with x ∈ S ∩ B and x ∈ M (H^n-a.e. point of S ∩ B, by step 2). The accepted lemma `Submission.dtc_approxTangent_of_null_diff` (with S ∩ B ⊆ S, V := B, and (S ∖ (S ∩ B)) ∩ B = ∅) gives HasApproximateTangentSpaceAt n (S ∩ B) x Q_x. The accepted lemma `Submission.approxTangent_le_submanifold_tangentSpace` (N := M, an embedded C¹ n-submanifold, x ∈ M, H^n((S ∩ B) ∖ M) = 0 by step 2) gives Q_x ⊆ tangentSpace M x. Taking a chart ψ of M at x with ψ(v) = x, the accepted lemma `Submission.chart_tangentSpace_eq_range_fderiv` (r = 1) gives tangentSpace M x = range Dψ(v), the carrier of an n-dimensional subspace (Dψ(v) is injective on ℝⁿ); hence span(tangentSpace M x) = range Dψ(v) has dimension n and contains Q_x, so approxTangentPlane n S x = Q_x = span(tangentSpace M x) = T_xM.
6. (Vanishing off tsupport X.) If x ∉ tsupport X, then X = 0 on the open neighbourhood (tsupport X)ᶜ of x, so DX(x) = 0; hence tangentialDivergence n S X x = 0 and tr(P_x ∘ DX(x)) = 0.
7. (Evaluation.) By definition R.firstVariation X = ∫_S θ·tangentialDivergence n S X dH^n. By step 6 the integrand vanishes on S ∖ B (tsupport X ⊆ B), so the integral equals ∫_{S∩B} θ·tangentialDivergence n S X dH^n (S Borel). By steps 3 and 5, θ(x)·tangentialDivergence n S X x = k·tr(P_x ∘ DX(x)) for H^n-a.e. x ∈ S ∩ B. Hence R.firstVariation X = ∫_{S∩B} k·tr(P_x ∘ DX(x)) dH^n = k·∫_{S∩B} tr(P_x ∘ DX(x)) dH^n, and, since S ∩ B and M ∩ B coincide up to an H^n-null set (steps 2 and 4), the last integral equals ∫_{M∩B} tr(P_x ∘ DX(x)) dH^n. (These identities of Bochner integrals need no integrability: they are the indicator identity for a Borel set, a.e.-congruence of integrands, pulling out a constant factor, and a.e.-equality of the domains of integration.) ∎

## Key steps

1. Carrier points of B outside M lie outside spt T, hence form an H^n-null set (imrep_carrier_sdiff_support_null).
2. θ = k H^n-a.e. on S ∩ B: μ-a.e. x is in spt T and has density θ(x) (rsd_ae_hasMassDensity_mult), which equals k by hypothesis.
3. Points of M ∩ B outside S would have density 0 for H^n-a.e. such point (regcomp_atl_local_density_zero with θ = k), contradicting density k ≥ 1; so S ∩ B and M ∩ B agree H^n-a.e.
4. At H^n-a.e. x ∈ S ∩ B the approximate tangent plane Q_x of S lies in tangentSpace M x (approxTangent_le_submanifold_tangentSpace after localizing), and equal dimensions give Q_x = span(tangentSpace M x).
5. Since DX = 0 off tsupport X ⊆ B, the first-variation integral reduces to k·∫_{M∩B} tr(P_{T_xM} DX) dH^n.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `python3 -I scans of dag.json (lean_name, lean_statement, status): lemmas mentioning regularSet; IsConeCurrent together with support; IsStationaryAlong or firstVariation together with IsMinimizingIn; HasApproximateTangentSpaceAt together with IsEmbeddedSubmanifold or ContDiff; names matching support_null|density_zero|vanish|null_off; restrictDomain together with boundary; subspace ball measure; statuses of the 29 cited lemma names`
- `grep -n 'def restrictDomain|def VanishesOn|def zeroRegion|def support|def IsTestForm|def testFormOnSubmodule|def GeometricCurrentOn.boundary|def WeaklyConvergesOn|abbrev Covector' simongmt Chapter06/{CurrentLocalEquality,Currents,Forms}.lean`
- `grep -n 'def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique|def CountablyRectifiable' simongmt Chapter03/Rectifiable.lean`
- `grep -n 'theorem integral_area_formula_of_injective_derivative|def areaJacobianAt|areaJacobianAt_eq_sqrt_det_gram|theorem ae_eq_const_of_weak_coordinate_derivatives_zero' simongmt Chapter02/{WeightedArea,Area,AreaParametrization}.lean Chapter08/DistributionalConstancy.lean`
- `grep -rn 'euclideanHausdorffMeasure' mathlib Geometry/Euclidean/Volume/Measure.lean (zero_or_top, eq_volume, Isometry.euclideanHausdorffMeasure_image); grep -n 'addHaar_ball_of_pos|addHaar_ball ' mathlib MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `grep -c idtp_ccd dag.json; grep -rl idtp_ccd run nodes/*.json|*.md and .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match); grep -n 'Whi82' book/chapter-07.txt, book/simon-gmt.txt; sed -n 490,515p book/chapter-07.txt`
- `lake env lean /tmp/ccdp_check/Children.lean (7 child types elaborate); lake env lean /tmp/ccdp_check/Assembly.lean (#print axioms assembly_check: propext, Classical.choice, Quot.sound); lake env lean /tmp/ccdp_check/FromJson.lean (frozen child types as Submission.* stubs plus accepted-lemma stubs prove the parent type, exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/ccdp_check/Children.lean`
- `/tmp/ccdp_check/Assembly.lean`
- `/tmp/ccdp_check/FromJson.lean`

Pins match the manifest. The snapshot project commit equals workspace HEAD, b4d606d. Mathlib is 25730c7c and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Accepted DAG lemmas used by the children, all with status `accepted`: rsd_constant_multiplicity_reduction, rsd_ae_hasMassDensity_mult, rsd_mem_support_iff_measure_ball_pos, rsd_massOn_eq_measure, rsd_cmr_support_eq_inter, imrep_carrier_sdiff_support_null, regcomp_atl_local_density_zero, approxTangent_le_submanifold_tangentSpace, dtc_approxTangent_of_null_diff, chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity, dimred_rpd_submanifold_density_one, imsupp_unit_orientation_ne_zero_norm_le_one, cone_current_imrep_measure_smul_image, dtc_restrictDomain_isIntegerMultiplicity, dtc_massOn_eq_of_agreeOn, dimred_cs_mi_hasMassDensity_unique, dimred_regular_point_density.

Non-accepted results used, all ancestor or parent prerequisites as in the supplied proof:
- density_one_implies_regular (speculative-ready)
- minimizing_implies_stationary (speculative-ready)
- idtp_planar_cycle_eq_const_mul (planar_constancy, this node's prerequisite)

No accepted lemma already states any child. In particular:
- No accepted lemma states cone-support dilation invariance or the regular-point support identity.
- No accepted lemma gives existence of approximate tangent planes for C¹ submanifolds. This is why sheet_first_variation uses the density argument plus approxTangent_le_submanifold_tangentSpace.
- The decomposing node codim1_density_one_regular_local_rep covers only density 1 and is not accepted.

SimonGMT supplies the area formula integral_area_formula_of_injective_derivative (areaJacobianAt = normDet; areaJacobianAt_eq_sqrt_det_gram is in AreaParametrization.lean) and ae_eq_const_of_weak_coordinate_derivatives_zero, which takes C¹ test functions. These modules are outside the base import closure, so only proofs, never the frozen statements, use them; other worktrees already add these imports. The SimonGMT definitions of support, zeroRegion and test forms (ContDiff ∞ with compact support) match the arguments in the proofs.

Mathlib supplies euclideanHausdorffMeasure_zero_or_top, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image and addHaar_ball_of_pos.

The proposed names idtp_ccd_* are unreserved: there is no match in dag.json, the run nodes, or any worktree Submission.

Lean check: all 7 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07. The hypothesis-only assembly proves the frozen parent type with axioms propext, Classical.choice and Quot.sound.
