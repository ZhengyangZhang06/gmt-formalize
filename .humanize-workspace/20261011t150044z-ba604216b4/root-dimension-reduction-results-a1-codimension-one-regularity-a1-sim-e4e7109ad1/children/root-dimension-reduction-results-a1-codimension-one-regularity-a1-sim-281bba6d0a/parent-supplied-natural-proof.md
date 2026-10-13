# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.linear_bootstrap-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the interior Schauder theory for linear systems in divergence form with Hölder coefficients (Giaquinta–Martinazzi 2012, §5.4.3–5.4.4, Theorem on C^{k,α}-regularity: coefficients and data in C^{k,α} give Du ∈ C^{k,α}), proved by Campanato's estimate (c1alpha_estimate) for k = 0, by difference quotients (difference_quotient) for k = 1, and by differentiating the equation for k ≥ 2; the Hölder-class calculus is holder_algebra. H_n denotes C^{n,α}_loc(Ω).

0. (Constants and conventions.) Let ε_D be the ε₁ of c1alpha_estimate for (m, k, α) and put ε₁ := min(ε_D, (ε_D/3)^{1/2}); so ε₁ ≤ ε_D and 3ε₁² ≤ ε_D. ω := |B_1(0)|. Write W[w; B, g; O] for the weak equation on an open set O. Two facts are used repeatedly: (a) W[w; B, g; Ω] implies W[w; B, g; O] for every open O ⊆ Ω (test maps supported in O are admissible, and integrands vanish off their supports); (b) membership in H_n is local: it suffices that every point of Ω has a ball in Ω on which f is C^n with an α-Hölder bound for D^n f near the point. For C¹ functions, D¹f(y) corresponds isometrically to Df(y) (Mathlib continuousMultilinearCurryFin1), so f ∈ H_1 iff f is C¹ and Df is locally α-Hölder.
We prove by induction on l the statement S(l): for all open Ω, w, B, g as in the statement with B, g ∈ H_l, w ∈ H_{l+1}.

1. (Translated equations.) Let closedBall(x, r + |t|) ⊆ Ω, v a unit vector, t ≠ 0, and w_t(y) := t⁻¹(w(y + tv) − w(y)). Then w_t is C¹ on B_r(x), Dw_t(y) = t⁻¹(Dw(y + tv) − Dw(y)), and W[w_t; B, g_t; B_r(x)] holds with g_t(y) := t⁻¹(B(y + tv) − B(y))[Dw(y + tv)] + t⁻¹(g(y + tv) − g(y)). Proof: for ζ admissible in B_r(x), ζ(· − tv) is admissible in Ω; apply W[w; B, g; Ω] to it, substitute y ↦ y + tv (translation invariance of Lebesgue measure), subtract W for ζ, divide by t, and use B(y + tv)[Dw(y + tv)] − B(y)[Dw(y)] = B(y)[Dw(y + tv) − Dw(y)] + (B(y + tv) − B(y))[Dw(y + tv)].

2. (S(0).) Let B, g ∈ H_0 and x ∈ Ω. Choose R > 0 with closedBall(x, R) ⊆ Ω such that B and g are α-Hölder on B_R(x) with constants C_B, C_g, and let K₀ bound ‖w‖ and ‖g‖ on closedBall(x, R) (continuity). F := B[Dw] + g is continuous on B_R(x) and ‖F‖ ≤ ε₁‖Dw‖ + K₀ ≤ ε_D‖Dw‖ + K₀. For closedBall(z, ρ) ⊆ B_R(x) put c := B(z)[(Dw)_{z,ρ}] + g(z); for y ∈ B_ρ(z), F(y) − c = (B(y) − B(z))[Dw(y)] + B(z)[Dw(y) − (Dw)_{z,ρ}] + (g(y) − g(z)), so ∫_{B_ρ(z)} ‖F − c‖² ≤ 3ε₁²∫‖Dw − (Dw)_{z,ρ}‖² + 3C_B²ρ^{2α}∫‖Dw‖² + 3C_g²ωρ^{m+2α}. With K := max(K₀, 3C_B², 3C_g²ω) all hypotheses of c1alpha_estimate hold on B_R(x) (3ε₁² ≤ ε_D; the weak equation by fact (a)). Hence Dw is bounded and α-Hölder on B_{R/4}(x). By fact (b), w ∈ H_1.

3. (S(1).) Let B, g ∈ H_1. By holder_algebra (5)/(6) they are C¹ with locally α-Hölder derivatives, and by S(0) (H_1 ⊆ H_0 by holder_algebra (5)) w ∈ H_1. Fix x ∈ Ω and R > 0 with closedBall(x, 2R) ⊆ Ω such that on B_{2R}(x) the maps B, DB, g, Dg, Dw are bounded by K₁ and α-Hölder with constant K₁ (local Hölder bounds and continuity; shrink R). Let v be a unit vector and 0 < |t| < R/2. By step 1, w_t solves W[w_t; B, g_t; B_R(x)]. Uniformly in t and v: ‖w_t‖ ≤ K₁ (mean value inequality); t⁻¹(B(y + tv) − B(y)) = ∫_0^1 DB(y + σtv)v dσ has norm ≤ K₁ and is α-Hölder in y with constant K₁; the same holds for t⁻¹(g(y + tv) − g(y)); y ↦ Dw(y + tv) is bounded by K₁ and α-Hölder with constant K₁ on B_R(x). Hence ‖g_t‖ ≤ K₁² + K₁ and g_t is α-Hölder on B_R(x) with constant K₂ := 2K₁² + K₁. As in step 2 (with F_t := B[Dw_t] + g_t and c := B(z)[(Dw_t)_{z,ρ}] + g_t(z)), c1alpha_estimate applies on B_R(x) with K := max(K₁, K₁² + K₁, 3K₁², 3K₂²ω), independent of t and v, and gives C with ‖Dw_t‖ ≤ C and ‖Dw_t(y) − Dw_t(y')‖ ≤ C‖y − y'‖^α on B_{R/4}(x). Since Dw_t(y) = t⁻¹(Dw(y + tv) − Dw(y)), difference_quotient (f := Dw, ball B_{R/4}(x), h₀ := R/2) shows that Dw is C¹ on B_{R/4}(x) with α-Hölder derivative. By fact (b), Dw ∈ H_1, so w ∈ H_2 by holder_algebra (6).

4. (S(l − 1) ⇒ S(l) for l ≥ 2.) Let B, g ∈ H_l. By holder_algebra (5), B, g ∈ H_{l−1}, so S(l − 1) gives w ∈ H_l; in particular w is C^l, hence C², on Ω. For s ∈ {1, …, m} put v_s(y) := Dw(y)e_s, B'_s(y) := DB(y)e_s, g'_s(y) := Dg(y)e_s.
(a) (Differentiated equation.) W[v_s; B, B'_s[Dw] + g'_s; Ω] holds. Indeed, let ζ be admissible and let d > 0 be the distance from the compact set tsupport ζ to ℝ^m \ Ω (d = ∞ if Ω = ℝ^m). For 0 < |t| < d/2 the map ζ(· − te_s) is admissible in Ω, and the computation of step 1 (with v = e_s) gives ∫⟨Dw_t, Dζ⟩ = ∫⟨B[Dw_t] + g_t, Dζ⟩, where w_t, g_t are defined and continuous (w_t C¹) on the d/2-neighbourhood of tsupport ζ and the integrands vanish off tsupport ζ. As t → 0, uniformly on the compact set tsupport ζ: Dw_t(y)e_j = t⁻¹(Dw(y + te_s) − Dw(y))e_j → D²w(y)(e_s, e_j) = D²w(y)(e_j, e_s) = Dv_s(y)e_j (symmetry of second derivatives, uniform continuity of D²w on a compact neighbourhood), and g_t → B'_s[Dw] + g'_s (B, g C¹). The integrands are uniformly bounded and supported in tsupport ζ, so the identity passes to the limit.
(b) (Data.) v_s is C¹ on Ω. By holder_algebra: DB ∈ H_{l−1} (6), so B'_s = β₀(DB, e_s) ∈ H_{l−1} with β₀ the evaluation bilinear map and e_s a constant (1), (3); Dw ∈ H_{l−1} (6); B'_s[Dw] ∈ H_{l−1} (3, evaluation bilinear map); g'_s ∈ H_{l−1} likewise; the sum is in H_{l−1} (2). Also B ∈ H_{l−1} and ‖B‖ ≤ ε₁.
(c) S(l − 1) applied to (v_s, B, B'_s[Dw] + g'_s) gives v_s ∈ H_l.
(d) Dw(y) = Σ_s λ_s(v_s(y)), where λ_s : ℝ^k → L(ℝ^m, ℝ^k), λ_s(b)(a) := ⟨a, e_s⟩b, is continuous linear (hence C^∞). By holder_algebra (4) and (2), Dw ∈ H_l, and by (6), w ∈ H_{l+1}.

5. By induction, S(l) holds for every l. ∎

## Key steps

1. Choose ε₁ ≤ min(ε_D, (ε_D/3)^{1/2}) so that B[Dw] + g satisfies the hypotheses of c1alpha_estimate on small balls.
2. l = 0: c1alpha_estimate on small balls gives Dw locally α-Hölder.
3. l = 1: difference quotients w_t solve the same kind of equation with data bounded and Hölder uniformly in t; c1alpha_estimate plus difference_quotient give Dw ∈ C^{1,α}.
4. l ≥ 2: v_s = ∂_s w solves Δv_s = div(B[Dv_s] + (∂_s B)[Dw] + ∂_s g) with data in C^{l−1,α} (holder_algebra); induction gives v_s ∈ C^{l,α}, hence w ∈ C^{l+1,α}.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sed -n 1,457p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace, approxTangentPlane, tangentialDivergence)`
- `python3 scans of dag.json: selected node, parent hypercone_plane and its 12 children with statuses; regex Allard|Schauder|elliptic|harmonic|Campanato|Caccioppoli|Weyl|difference quotient|Hölder|Sobolev|mollif|Poincar|inverse function|graph over; accepted nodes whose types mention IsEmbeddedSubmanifold`
- `name checks: lean_name scan of dag.json (1531 nodes); grep -rln codim1_hcp_sr GMT/ simongmt/Poincare local-references/.../project (no match); git for-each-ref | xargs git grep -l codim1_hcp_sr -- 'GMT/*.lean' (no match)`
- `runtime.py: _decompose (node.depth >= max_depth), _existing_lean_name_problem, _solve_children, _accepted_checkpoint`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: iteratedFDeriv_succ_eq_comp_right, contDiffOn_succ_iff_fderiv_of_isOpen, ContDiffOn.fderiv_of_isOpen, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, ae_eq_zero_of_integral_contDiff_smul_eq_zero, MeasurableSet.image_of_continuousOn_injOn, exists_contDiff_tsupport_subset, exists_contMDiff_zero_iff_one_iff_of_isClosed, contDiffAt_ringInverse, Submodule.topologicalClosure, trace_comp_comm, LipschitzOnWith.extend_real, norm_integral_le_integral_norm, HolderOnWith; ls Analysis/InnerProductSpace/{Harmonic,Laplacian.lean,LaxMilgram.lean}, Analysis/Distribution/Sobolev.lean`
- `sed -n 100,220p simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean (injective_area_formula_of_injective_derivative); grep euclideanHausdorffMeasure mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `book: chapter-05.txt lines 50-131 (§1, system 1.1-1.3) and 1270-1397 (Theorem 7.1 and its proof); accepted proofs of dorag_ha_weyl_lemma and dorag_ha_interior_estimates (parent-supplied-natural-proof.md)`
- `lean -DautoImplicit=false /tmp/sr-split-ch07/check/{Types,TypesFinal,Assembly,AssemblyFinal,Inst}.lean (LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean)`
- `WebSearch (standard): Giaquinta Martinazzi Regularity Theory for Elliptic Systems Campanato iteration lemma Schauder estimates divergence form chapter 5`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e4e7109ad1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e4e7109ad1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-ea25690300/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-f15d71c3ef/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-252c8df06c56/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/Sobolev.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/sr-split-ch07/check/TypesFinal.lean`
- `/tmp/sr-split-ch07/check/AssemblyFinal.lean`
- `/tmp/sr-split-ch07/check/Inst.lean`

Pins: manifest records project b4d606db and Mathlib 25730c7c, matching the workspace.
Library gaps: Mathlib has no interior elliptic or Schauder regularity, Campanato theory, or Dirichlet solver; it has only the Laplacian, HarmonicAt, Fourier-side Sobolev spaces and Lax–Milgram.
Library support used by the leaf proofs:
- Mathlib: the inverse function theorem, integration by parts, the fundamental lemma of distributions, Lusin–Souslin, smooth bumps, smoothness of ring inversion, iteratedFDeriv currying and contDiffOn_succ_iff_fderiv_of_isOpen;
- SimonGMT: injective_area_formula_of_injective_derivative.
DAG: dorag_ha_weyl_lemma and dorag_ha_interior_estimates are accepted with candidate commits and are reused with byte-identical types. dor_allard_bounded_curvature_graph is accepted but only gives C¹. The ten new codim1_hcp_sr_* names are unused everywhere.
Lean: all 12 child types elaborate. The selected frozen type is kernel-checked from graph_chart, stationary_mss and quasilinear_smooth as axioms (axioms: propext, Classical.choice, Quot.sound and the three children).
