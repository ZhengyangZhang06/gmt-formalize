# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 5, Theorem 7.1 and its proof (chapter-05.txt lines 1306–1366), last part: if θ is a positive integer, N is a C^{q+3} submanifold and V is stationary in U ∩ N, then near a point of density one spt V is the graph of a C^{q+2,α} function. This is how step 2 of the supplied proof of the parent obtains smoothness ("for every y ∈ M and every q there are σ > 0 and a rigid motion after which M ∩ B_σ(y) is the graph of a C^{q+2,α} function"). Supporting book results: Ch. 4, 2.6 and 3.14 (stationary varifolds have generalized mean curvature 0); Ch. 3, 1.4–1.8 (approximate tangent spaces and densities). Sibling lemmas: chart_tangent_space (Submission.chart_tangentSpace_eq_range_fderiv: tangentSpace M x = range Dψ(v), the m-dimensional classical tangent plane), density_one (Submission.dimred_rpd_submanifold_density_one), locally_closed (Submission.dimred_rpd_embedded_locally_closed).

Notation. H^m := μHE[m]; B_s(x) := ball x s; ω_m := unitBallVolume m; T_xM := tangentSpace M x.

1. (Orders r ≤ 1.) A C¹ chart is a C^r chart for r ≤ 1 (ContDiffOn ℝ 1 implies ContDiffOn ℝ r), so IsEmbeddedSubmanifold r m M holds for r ≤ 1. Fix r ≥ 2 and y ∈ M. We construct a C^r chart of M at y.

2. (Local closedness.) By locally_closed, part (b), there is ε > 0 with M ∩ closedBall(y, ε) compact. Choose ρ > 0 with 2ρ < ε and closedBall(y, 2ρ) ⊆ U, and put B := B_{2ρ}(y). For every compact K ⊆ B, M ∩ K = (M ∩ closedBall(y, ε)) ∩ K is compact. In particular M ∩ B is relatively closed in B.

3. (The varifold and its first variation.) Let V₀ := v(M ∩ B, 1), the rectifiable m-varifold in B with multiplicity θ ≡ 1 on M ∩ B. M ∩ B is an embedded C¹ submanifold (restrict the charts of M to the open set B), hence Borel and countably m-rectifiable, and μ_{V₀} = H^m⌞(M ∩ B) is a Radon measure on B, since H^m(M ∩ K) < ∞ for compact K ⊆ B ⊆ U. At every x ∈ M ∩ B the approximate tangent space of V₀ is T_xM = tangentSpace M x = range Dψ(v) for any chart ψ with ψ(v) = x (chart_tangent_space): near x, M is the graph over T_xM of a C¹ function with zero derivative at x (inverse function theorem applied to the orthogonal projection onto T_xM of a chart, Simon Ch. 2, 4.4), so the blow-ups λ^{-1}(M − x) converge locally to T_xM as C¹ graphs with gradients tending to 0, and η_{x,λ#}(H^m⌞M) → H^m⌞T_xM (Simon Ch. 3, 1.4 and 1.7). Hence, for X ∈ C¹_c(B; ℝ^P), the first variation of V₀ is δV₀(X) = ∫_{M∩B} div_M X dH^m (Simon Ch. 4, 2.2, with div_M computed on T_xM). For such X, tsupport X ⊆ B ⊆ U and div_M X = 0 on M ∖ B (DX = 0 outside tsupport X), so δV₀(X) = ∫_M div_M X dH^m = 0 by the stationarity hypothesis. Thus V₀ is stationary in B (Simon Ch. 4, 2.6, with N = ℝ^P); equivalently it has generalized mean curvature H = 0 in B (Ch. 4, 3.14), and in particular H ∈ L^p_loc(μ_{V₀}) for every p > m.

4. (Density.) By density_one, Θ^m(V₀, x) = lim_{s↓0} H^m(M ∩ B_s(x))/(ω_m s^m) = 1 for every x ∈ M ∩ B. Thus θ ≡ 1 ≥ 1 and Θ^m(V₀, y) = 1. Moreover spt μ_{V₀} ∩ B = M ∩ B: every point of M ∩ B has positive density, hence lies in the support, and M ∩ B is closed in B (step 2).

5. (Allard–Schauder.) The hypotheses of Simon Ch. 5, Theorem 7.1 hold in the open set B at the point ξ := y: V₀ = v(M ∩ B, θ) has generalized mean curvature H = 0, which is locally in L^p for some p > m; θ ≥ 1 and θ is positive integer-valued; Θ^m(V₀, y) = 1; and V₀ is stationary in B ∩ N with N := ℝ^P, a C^∞ (in particular C^{q+3}) submanifold of dimension P (step 3). Apply the last part of Theorem 7.1 with q := r. Together with formula (1) of its proof (graph u = spt V ∩ B_σ(0), after translating by −y and applying an orthogonal transformation), it gives σ ∈ (0, ρ), an orthogonal transformation Q of ℝ^P, an open set Ω ⊆ ℝ^m with 0 ∈ Ω and u ∈ C^{r+2,α}(Ω; ℝ^{P−m}) ⊆ C^r(Ω; ℝ^{P−m}) with u(0) = 0 and Du(0) = 0, such that
 Q(spt μ_{V₀} − y) ∩ B_σ(0) = {(a, u(a)) : a ∈ Ω}.
 Since σ < 2ρ, spt μ_{V₀} ∩ B_σ(y) = M ∩ B_σ(y) by step 4. Hence M ∩ B_σ(y) = {y + Q^{-1}(a, u(a)) : a ∈ Ω}.

6. (A C^r chart at y.) Define linear isometries ι : ℝ^m → ℝ^P, ι(a) := Q^{-1}(a, 0), and ι' : ℝ^{P−m} → ℝ^P, ι'(b) := Q^{-1}(0, b), with orthogonal ranges, and put π := ι* (so π∘ι = id and π∘ι' = 0). Let G(a) := y + ι(a) + ι'(u(a)) for a ∈ Ω and G(a) := y + ι(a) for a ∉ Ω. Take V₁ := Ω, W₁ := B_σ(y) and ψ := G. Then:
 (i) V₁ and W₁ are open, and y = G(0) ∈ W₁;
 (ii) G is C^r on V₁, because u ∈ C^r(Ω);
 (iii) G is injective on V₁, because π(G(a) − y) = a;
 (iv) G(V₁) = M ∩ B_σ(y) = W₁ ∩ M, by step 5;
 (v) for every compact K ⊆ W₁, V₁ ∩ G^{-1}(K) = π((M ∩ K) − y): if a ∈ V₁ and G(a) ∈ K, then G(a) ∈ M ∩ K and a = π(G(a) − y); conversely each z ∈ M ∩ K ⊆ M ∩ B_σ(y) is z = G(a) with a ∈ V₁, and π(z − y) = a. M ∩ K is compact by step 2 (K ⊆ B), so V₁ ∩ G^{-1}(K) is compact;
 (vi) DG(a) = ι + ι'∘Du(a) satisfies π∘DG(a) = id, so DG(a) is injective for a ∈ V₁.
 The values of G outside the open set V₁ affect neither ContDiffOn on V₁ nor fderiv at points of V₁. Hence (V₁, W₁, G) is a C^r chart of M at y in the sense of IsEmbeddedSubmanifold r m M. As y ∈ M was arbitrary, IsEmbeddedSubmanifold r m M holds, for every r ∈ ℕ. ∎

## Key steps

1. For r ≤ 1 the C¹ charts suffice; for r ≥ 2 fix y ∈ M and a ball B = B_{2ρ}(y) ⊆ U in which M is relatively closed (locally_closed).
2. v(M ∩ B, 1) is stationary in B, its first variation being ∫_M div_M X dH^m, and has density 1 at every point of M ∩ B (density_one); its support in B is M ∩ B.
3. Simon Ch. 5, Theorem 7.1, last part (N = ℝ^P, q = r) and formula (1) of its proof: after a rigid motion, M ∩ B_σ(y) is the graph of a C^{r+2,α} function u.
4. G(a) = y + ι(a) + ι'(u(a)) is a C^r chart at y: injective, proper, with injective derivative and image W ∩ M.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 1,457p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, MultiVector, tangentialDivergence, unitBallVolume)`
- `python3 scans of dag.json: selected node, parent simons_regular_cone and its decomposition-v1.json; nodes whose types mention IsEmbeddedSubmanifold or tangentSpace with statuses and candidate commits; keyword scan Allard|Schauder|second fundamental|Simons|stability|first variation|area formula`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/AppendixB/{SimonsInequalities,ConeDefect,LagrangeIdentity}.lean and Chapter02/{SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldCalculus,AreaFormula,Area}.lean`
- `grep -rn 'measurable_fderiv|LipschitzWith.ae_differentiableAt|ae_differentiableWithinAt_of_mem|hausdorffMeasure_image_le|image_of_continuousOn_injOn|hasDerivAt_integral_of_dominated_loc_of_deriv_le|exists_isSubordinate|contDiffOn_infty|HasFDerivWithinAt.unique_on|normDet' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `runtime.py of flow gmt-claude-252c8df06c56: _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _accepted_checkpoint; store.py ensure`
- `git for-each-ref (1709 distinct objects) | xargs git grep -l codim1_hcp -- 'GMT/*.lean' (no match); grep -c codim1_hcp dag.json (0); grep -rn codim1_hcp simongmt (no match)`
- `lean -DautoImplicit=false /tmp/hcp-split/check/{Types,TypesAll,Assembly,Inst}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `book: chapter-B.txt 1-282; chapter-02.txt 854-1410; chapter-05.txt 1280-1397; chapter-03.txt 290-330; grep 'B.2 Theorem|B.8 Lemma|B.11 Lemma|Proof of B.2' sources/chapter-07-source.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-locally-closed-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/LagrangeIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/hcp-split/check/TypesAll.lean`
- `/tmp/hcp-split/check/Assembly.lean`
- `/tmp/hcp-split/check/Inst.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib (simongmt 2b366308). The snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library. SimonGMT supplies injective_area_formula_of_injective_derivative (Chapter02/AreaFormula.lean:145), the Appendix B algebra simonsDefect_eq_sum_skew (LagrangeIdentity.lean:122), four_mul_radialSkewSum_le, radial_derivative_of_codazzi, cone_simonsDefect_lower_bound (ConeDefect.lean:136–228) and exists_final_exponent (witness 1/10). It has no submanifold curvature calculus, Simons identity or Allard theorem; these remain book citations inside unit_normal, stability, simons_cone and smooth_regularity. The snapshot Mathlib has measurable_fderiv (FDeriv/Measurable.lean:378), LipschitzWith.ae_differentiableAt and LipschitzOnWith.ae_differentiableWithinAt_of_mem (Calculus/Rademacher.lean), LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733), MeasurableSet.image_of_continuousOn_injOn, hasDerivAt_integral_of_dominated_loc_of_deriv_le, SmoothPartitionOfUnity.exists_isSubordinate, contDiffOn_infty and HasFDerivWithinAt.unique_on. LinearMap.normDet exists (InnerProductSpace/NormDet.lean) but is outside Submission's import closure, so Jacobians are stated as √det(L*∘L).
DAG. chart_tangentSpace_eq_range_fderiv, dimred_rpd_submanifold_density_one and dimred_rpd_embedded_locally_closed are accepted with candidate commits (d626082a69a0, e8842d90b78f, 6da66b1edf6f) and are reused with byte-identical types; the runtime reuses accepted nodes by identical name and type and leaves their handoffs untouched. The Allard nodes dor_allard_bounded_curvature_graph and codim1_ldr_allard_bounded_curvature_graph are unaccepted and cannot be reused. The stationarity integrand has the same form as idtp_ccd_sheet_first_variation. The 9 new codim1_hcp_ names are free in dag.json, GMT/, SimonGMT and all ref trees.
Lean. All 12 child types elaborate after import GMT.Ch07.Submission in the contract namespace and opens (TypesAll.lean, exit 0). The selected frozen type is kernel-checked from the child types as axioms (Assembly.lean, exit 0; axioms: propext, Classical.choice, Quot.sound and six children). Inline instances verified by rfl (Inst.lean): the inner product on span(tangentSpace M x) is Submodule.innerProductSpace and starProjection = subtypeL ∘ orthogonalProjection; ContDiff ℝ (⊤ : ℕ∞) elaborates to ↑⊤ (C^∞, not analytic).
