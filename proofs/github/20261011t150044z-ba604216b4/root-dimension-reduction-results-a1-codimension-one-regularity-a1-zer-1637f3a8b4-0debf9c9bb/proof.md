# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.flat_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 7(b)–(c), 8, 9 and 10 of the supplied proof of the parent node (projected test forms, uniform perimeter bound, BV compactness, identification of the limit), with the rescaled region boundaries entering only through (H1)–(H4). Simon 7.5.3 (chapter-07.txt lines 790–860: "by virtue of (1) and 5.2 we deduce from the BV Compactness 2.6 of Ch. 2 that some subsequence … converges in L¹_loc") and 7.5.5 (lines 862–901). Departures from the supplied proof: (1) test forms are lifted from divergence fields with a cut-off in the normal direction, and only a uniform comass bound K is used (the supplied step 8 used |ζπ_A^#α̃| ≤ 1 via Cauchy–Binet; a uniform constant suffices for the compactness); (2) the representation (H3) is assumed for every test form supported in a ball, so the splitting ω = ζω + (1 − ζ)ω of the supplied step 10 is unnecessary. Sibling child used: bv_compactness (Submission.codim1_zsl_perimeter_compactness).

Notation. P := n + 1 + k; ℝ^d = Euclid d; α(Le) := α(Le_0, …, Le_n) for an (n+1)-covector α and a linear L : ℝ^{n+1} → ℝ^P. ι*, ι'* are the adjoints: ι*ι = id, ι'*ι' = id, ι*ι' = 0, ι'*ι = 0, and (orthogonality and spanning) y = ιι*y + ι'ι'*y and |y|² = |ι*y|² + |ι'*y|² for every y. B_R := ball(0, R) ⊆ ℝ^{n+1}; H^{n+1} := μHE[n+1]; L^{n+1} := volume on ℝ^{n+1}; div φ := trace Dφ; G(w) := ιw + ι'b. |α| := covectorEuclideanNorm α, and a form ω is admissible if |ω(y)| ≤ 1 for all y.

Part A (lifting divergence fields to test forms).
A1. Let Ω be the standard volume form of ℝ^{n+1}, Ω(z_0, …, z_n) := det[z_0 | … | z_n]: the determinant Module.Basis.det of the standard basis, made a continuous alternating map with AlternatingMap.mkContinuous and the Leibniz bound |det[z_0 | … | z_n]| ≤ (n+1)!·∏_j|z_j|. Ω(e_0, …, e_n) = 1, and Ω(z, e_0, …, ê_j, …, e_n) = (−1)^j·z_j for z ∈ ℝ^{n+1} and j ≤ n (moving z to position j takes j transpositions).
A2. For a C^∞ compactly supported vector field φ on ℝ^{n+1} let α̃(v) := Ω(φ(v), ·, …, ·) (ContinuousAlternatingMap.curryLeft), an n-form on ℝ^{n+1}. α̃ is C^∞ (a continuous linear function of φ(v)), tsupport α̃ ⊆ tsupport φ, and by the coordinate formula for d (SimonGMT exteriorDerivative_apply: dβ(v)(e_0, …, e_n) = Σ_j (−1)^j·D[β(·)(e_0, …, ê_j, …, e_n)](v)e_j) together with A1,
 dα̃(v)(e_0, …, e_n) = Σ_j (−1)^j·∂_j((−1)^jφ_j)(v) = Σ_j ∂_jφ_j(v) = div φ(v).
A3. Fix h > 0 and let χ(t) := smoothTransition((4h² − t)/(3h²)) for t ∈ ℝ: χ is C^∞, 0 ≤ χ ≤ 1, χ(t) = 1 for t ≤ h² and χ(t) = 0 for t ≥ 4h². Put ζ(y) := χ(|ι'*y|²), a C^∞ function on ℝ^P.
A4. Define ω_φ(y) := ζ(y)·(α̃(ι*y)∘ι*), i.e. ζ times the pull-back affinePullbackForm ι* 0 α̃. ω_φ is C^∞. If ω_φ(y) ≠ 0 then ι*y ∈ tsupport φ and |ι'*y| < 2h; the set {y : ι*y ∈ tsupport φ, |ι'*y| ≤ 2h} is closed and bounded (|y|² = |ι*y|² + |ι'*y|²), hence compact. So ω_φ ∈ 𝒟^n(ℝ^P) and tsupport ω_φ ⊆ {ιv + ι'w : v ∈ tsupport φ, |w| ≤ 2h}.
A5. (Uniform comass bound.) z ↦ Ω(z, ·)∘ι* is a linear map from ℝ^{n+1} to n-covectors on ℝ^P, and |·| is continuous and absolutely homogeneous; so K := max(1, sup_{|z|≤1}|Ω(z, ·)∘ι*|) is finite (compact unit ball) and depends only on n, k and ι. If |φ| ≤ 1 everywhere, then |ω_φ(y)| = ζ(y)·|Ω(φ(ι*y), ·)∘ι*| ≤ K for all y.
A6. (Key identity.) Let v ∈ ℝ^{n+1}, w ∈ ℝ^k with |w| < h, y₀ := ιv + ι'w, and let L : ℝ^{n+1} → ℝ^P be linear with ι*L = id. Then dω_φ(y₀)(Le) = div φ(v). Indeed |ι'*y|² < h² for y near y₀, so ζ = 1 near y₀ and ω_φ coincides near y₀ with π^#α̃ := affinePullbackForm ι* 0 α̃. The exterior derivative at a point depends only on the germ (Filter.EventuallyEq.fderiv_eq), so dω_φ(y₀) = d(π^#α̃)(y₀) = dα̃(ι*y₀)∘ι* (SimonGMT exteriorDerivative_affinePullbackForm) = dα̃(v)∘ι*. Hence dω_φ(y₀)(Le_0, …, Le_n) = dα̃(v)(ι*Le_0, …, ι*Le_n) = dα̃(v)(e_0, …, e_n) = div φ(v) by A2.

Part B (uniform perimeter bounds).
B1. Fix R > 0 and put h := |b| + 1, R₂ := R + 2h. Let c₂ be the constant of (H4) for R₂. By (H1), (H2) with ε = 1, (H3) and (H4), all for R₂, there is i₀ such that for i ≥ i₀: g_i is differentiable on B_{R₂}; |g_i(w) − b| < 1, hence |g_i(w)| < h, on B_{R₂}; the representation (H3) holds for every ω supported in ball(0, R₂); and currentEval(S_i)(ω) ≤ c₂ for every admissible ω supported in ball(0, R₂).
B2. Let i ≥ i₀ and let φ be C^∞ with compact support, tsupport φ ⊆ B_R and |φ| ≤ 1; let ω := ω_φ with h from B1. For v ∈ tsupport φ and |w| ≤ 2h, |ιv + ι'w| ≤ |v| + |w| < R + 2h, so tsupport ω ⊆ ball(0, R₂). For w ∈ B_{R₂}: G_i(w) = ιw + ι'g_i(w) with |g_i(w)| < h, g_i is differentiable at w, DG_i(w) = ι + ι'Dg_i(w) and ι*DG_i(w) = id; so by A6, dω(G_i(w))(DG_i(w)e) = div φ(w). Hence by (H3), currentEval(S_i)(ω) = ∫_{F_i∩B_{R₂}} div φ = ∫_{F_i} div φ, because div φ vanishes outside tsupport φ ⊆ B_{R₂} (φ vanishes near such points) and F_i is measurable.
B3. ω/K is admissible (A5) and has the same support as ω, and currentEval(S_i) is linear in the form (tsupport(ω/K) = tsupport ω, so the same branch of currentEval applies, and S_i is linear). By B1, ∫_{F_i} div φ = K·currentEval(S_i)(ω/K) ≤ K·c₂. Thus for every R > 0 there are c(R) := K·c₂ and i₀ such that ∫_{F_i} div φ ≤ c(R) for every i ≥ i₀ and every admissible φ with tsupport φ ⊆ B_R: this is the hypothesis of bv_compactness for the measurable sets F_i ⊆ ℝ^{n+1}.

Part C (compactness).
C1. bv_compactness (with m := n + 1) gives a strictly increasing σ and a measurable F' ⊆ ℝ^{n+1} with L^{n+1}((F_{σ(i)} Δ F') ∩ B_R) → 0 for every R.

Part D (identification of S).
D1. Fix ω ∈ 𝒟^n(ℝ^P). tsupport ω is compact, so tsupport ω ⊆ ball(0, R) for some R > 0. Put h_i(w) := dω(G_i(w))(DG_i(w)e) and h(w) := dω(G(w))(ιe). dω is continuous with compact support, hence bounded, say by M, and uniformly continuous.
D2. By (H1)–(H2) (and |ι'u| = |u|), for every ε > 0 and all large i, |G_i(w) − G(w)| = |g_i(w) − b| < ε and ‖DG_i(w) − ι‖ = ‖Dg_i(w)‖ < ε for all w ∈ B_R. The map (y, L) ↦ dω(y)(Le) is uniformly continuous on ℝ^P × {L : ‖L‖ ≤ 2}, because dω is uniformly continuous and bounded and α is multilinear: |α(z) − α'(z')| ≤ ‖α − α'‖·∏_j|z_j| + ‖α'‖·Σ_j|z_j − z'_j|·∏_{l≠j}max(|z_l|, |z'_l|). Hence sup_{B_R}|h_i − h| → 0, and |h_i| ≤ M' := 2^{n+1}M on B_R for all large i.
D3. For large i, h_i is measurable on B_R: G_i is continuous on B_R and w ↦ DG_i(w) = ι + ι'Dg_i(w) is measurable (measurable_fderiv); h is continuous.
D4. By (H3), for all large i, currentEval(S_{σ(i)})(ω) = ∫_{F_{σ(i)}∩B_R} h_{σ(i)}, and
 |∫_{F_{σ(i)}∩B_R} h_{σ(i)} − ∫_{F'∩B_R} h| ≤ ∫_{B_R}|1_{F_{σ(i)}} − 1_{F'}|·|h_{σ(i)}| + ∫_{F'∩B_R}|h_{σ(i)} − h| ≤ M'·L^{n+1}((F_{σ(i)} Δ F') ∩ B_R) + L^{n+1}(B_R)·sup_{B_R}|h_{σ(i)} − h|,
which tends to 0 by C1 and D2.
D5. S_i ⇀ S gives currentEval(S_{σ(i)})(ω) → S(ω). Hence S(ω) = ∫_{F'∩B_R} h = ∫_{F'} h, because for |w| ≥ R, |G(w)|² = |w|² + |b|² ≥ R², so G(w) ∉ ball(0, R) ⊇ tsupport ω ⊇ tsupport dω and h(w) = 0.

Part E (transfer to the plane).
E1. G is an isometry of ℝ^{n+1} onto A_b := {ιw + ι'b : w ∈ ℝ^{n+1}} (|G(w) − G(w')| = |w − w'|), hence a closed embedding and a measurable embedding (Topology.IsClosedEmbedding.measurableEmbedding). F := G(F') is measurable and F ⊆ A_b = {y : ∃ w, y = ιw + ι'b}.
E2. Hausdorff measure is invariant under isometries: G_#(μHE[n+1] on ℝ^{n+1}) = H^{n+1}⌞range G (Isometry.map_euclideanHausdorffMeasure), and μHE[n+1] = L^{n+1} on ℝ^{n+1} (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). As G is injective, H^{n+1}⌞F = G_#(L^{n+1}⌞F') and ∫_F f dH^{n+1} = ∫_{F'} f(G(w)) dw for every f : ℝ^P → ℝ (MeasurableEmbedding.integral_map).
E3. With f(y) := ξ_A(dω(y)) and ξ_A(α) = α(ιe): ∫_F ξ_A(dω(y)) dH^{n+1}(y) = ∫_{F'} dω(G(w))(ιe) dw = ∫_{F'} h = S(ω) by D5. As ω was arbitrary, IsBoundaryOfRegion S F (y ↦ ξ_A), with F measurable and F ⊆ {y : ∃ w, y = ιw + ι'b}. ∎

## Key steps

1. Divergence fields φ on ℝ^{n+1} lift to test forms ω_φ = ζ·(Ω(φ∘ι*, ·)∘ι*) on ℝ^P with |ω_φ| ≤ K, supported in a slab |ι'*y| ≤ 2h, and dω_φ(ιv + ι'w)(Le) = div φ(v) whenever |w| < h and ι*L = id.
2. By (H2) the graphs G_i = ι + ι'g_i lie in that slab and ι*DG_i = id, so (H3) gives currentEval(S_i)(ω_φ) = ∫_{F_i} div φ, which (H4) bounds by K·c₂: uniform local perimeter bounds.
3. bv_compactness yields F' with 1_{F_σ(i)} → 1_{F'} in L¹_loc; (H1)–(H2) give uniform convergence of the integrands, so S(ω) = ∫_{F'} dω(ιw + ι'b)(ιe) dw.
4. The isometry G(w) = ιw + ι'b carries this to S(ω) = ∫_{G(F')} ξ_A(dω) dH^{n+1}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; grep -n simongmt -A6 local-references/123e8435b4a2469b/project/lake-manifest.json`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `cat decomposition-audit-v1.json decomposition-review-receipt-v1.json; python3 dump of decomposition-v1.json (12 subproblems: statements, lean_statements, natural proofs, key steps, dependencies)`
- `python3 scan of dag.json: lean_name lookup of the 8 codim1_zsl_* names, the 4 reused names (status, candidate commit, lean_statement byte equality with decomposition-v1.json), dtc_hausdorff_dilation, dor_ims_unitOrientation_dual and codim1_zero_scale_limit_offset_plane; raw count of 'codim1_zsl'; keyword scan 'area formula|BV|perimeter|bvVariation|indicator' over statements and titles`
- `for r in $(git for-each-ref --format='%(objectname)' | sort -u): git grep -q -e codim1_zsl $r -- 'GMT/*.lean' (1277 commits); positive control: the same loop with dgcr_graph_orientation_jacobian; grep -rl codim1_zsl .lake/packages/simongmt/Poincare GMT`
- `grep -n 'def IsTestForm|def exteriorDerivative|theorem exteriorDerivative_apply|def covectorEuclideanNorm|def massOn|def zeroRegion|def support|def affinePullbackForm|theorem exteriorDerivative_affinePullbackForm|theorem tsupport_exteriorDerivative_subset' simongmt/Poincare/SimonGMT/Chapter06/*.lean, then sed of Forms.lean 25-135, Mass.lean 25-80, CurrentLocalEquality.lean 95-125, AffineCurrentPushforward.lean 30-50 and 145-160, Currents.lean 120-190`
- `rg -n 'theorem tsupport_eq|theorem support_eq|protected theorem neg|symmetric :' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n 'integral_comp_inv_smul_of_nonneg|support_convolution_subset|exists_isCompact_sdiff_lt|exists_isOpen_sdiff_lt|integral_pos_iff_support_of_nonneg|theorem lintegral_tsum' mathlib/Mathlib; rg -n 'namespace Module.Basis|def det' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `lean -DautoImplicit=false /tmp/zsl-v2/Lib.lean and /tmp/zsl-v2/Lib2.lean (#check of about 70 Mathlib/SimonGMT lemmas cited by the children)`
- `lean -DautoImplicit=false /tmp/zsl-v2/Bump.lean (ρ := (∫b)⁻¹·b for b : ContDiffBump (0 : Euclid m) with radii 1/2, 1: ContDiff ℝ ⊤, ρ ≥ 0, ρ(−z) = ρ(z), tsupport ρ = closedBall 0 1, ∫ρ = 1)`
- `lean -DautoImplicit=false /tmp/zsl-v2/TypesV2.lean (12 child types generated from the v2 JSON plus the assembly of the selected type); lean -DautoImplicit=false /tmp/zsl-v2/AssemblyV2.lean (children as axioms, #print axioms)`
- `grep -n 'def check_source_delta' -A40 /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-0b42d13aab/decomposition-review-receipt-v1.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/tmp/zsl-v2/Lib.lean`
- `/tmp/zsl-v2/Lib2.lean`
- `/tmp/zsl-v2/Bump.lean`
- `/tmp/zsl-v2/TypesV2.lean`
- `/tmp/zsl-v2/AssemblyV2.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot lake-manifest pins simongmt 2b366308, equal to .lake/packages/simongmt. The snapshot Contract.lean and the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
DAG.
- The selected node is 'decomposing' with the handoff's exact frozen type.
- The 4 reused declarations are accepted with types byte-identical to v1: dtc_blowUp_testForm_corr (5e184fbc), setIntegral_blowUpMap_image_eq_inv_pow_mul (713eebc5), rsdic_unitOrientation_eq_or_eq_neg (fe95347b) and dgcr_graph_orientation_jacobian (62aa1f11).
- The 8 codim1_zsl_* names have 0 occurrences in dag.json, SimonGMT, GMT/ and the 1277 commits reachable from refs. The positive control dgcr_graph_orientation_jacobian was found on 6 of those commits.
- No accepted node gives an exact graph area formula or BV compactness. The only area-formula nodes are unaccepted (dpf_area_formula_bilipschitz_rectifiable, idtp_carrier_area_formula) and have other types.
Library.
- The SimonGMT definitions match the children's proofs: exteriorDerivative = extDeriv with the alternating-sum formula, IsTestForm = ContDiff ℝ ∞ ∧ HasCompactSupport, covectorEuclideanNorm, massOn/massAdmissibleOn, zeroRegion/support and affinePullbackForm.
- In the snapshot Mathlib, ContDiffBump.tsupport_eq (BumpFunction/Basic.lean:157) gives closedBall c rOut. This confirms the v1 defect, so step 1 of bv_compactness now claims only tsupport ρ = closedBall(0, 1). ContDiffBump.neg (:132) gives evenness, and support_eq (:151) gives the open-ball support.
- Every lemma cited by the corrected proofs exists in the import closure. Examples: integral_comp_inv_smul_of_nonneg (Haar/NormedSpace.lean:129), support_convolution_subset (Convolution.lean:670), MeasurableSet.exists_isCompact_sdiff_lt/exists_isOpen_sdiff_lt (Regular.lean:843/385), exists_continuous_one_zero_of_isCompact and Module.Basis.det (Determinant.lean:591; the old name Basis.det is fixed).
Lean.
- Bump.lean compiles the corrected mollifier.
- TypesV2.lean elaborates all 12 frozen types taken verbatim from the v2 JSON and proves the selected type; lean exits 0. Its axioms are propext, sorryAx, Classical.choice and Quot.sound.
- With the children as axioms, AssemblyV2.lean depends only on propext, Classical.choice, Quot.sound and the 4 direct children.
- leaf_verification.check_source_delta forbids new declarations and imports in leaf proofs, so the deep lemmas must stay separate children.
