# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.difference_quotient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the difference-quotient characterization of differentiability used in the Schauder bootstrap (Gilbarg–Trudinger, Elliptic PDE of Second Order, §7.11 for the L^p version; here the elementary Hölder version).
0. Since m ≥ 1 a unit vector v exists, and ‖q_t(x)‖ ≥ 0, so C ≥ 0. Write q^v_t for the quotient in direction v. Fix x ∈ B and d_x := R − ‖x − x₀‖ > 0; let τ₀ := min(h₀, d_x)/3.
1. (Averaging identity.) Let v be a unit vector and τ, t real with 0 < |τ|, |t| < τ₀. Then every point x + σv with |σ| ≤ |τ| + |t| lies in B, f is continuous on that segment, and with σ ranging over the interval between 0 and τ: (1/τ)∫_0^τ q^v_t(x + σv) dσ = (1/τ)[(1/t)∫_τ^{τ+t} f(x + σv) dσ − (1/t)∫_0^t f(x + σv) dσ]. As t → 0, the right-hand side tends to (1/τ)(f(x + τv) − f(x)) = q^v_τ(x), by continuity of σ ↦ f(x + σv) (fundamental theorem of calculus for continuous integrands).
2. (Rate.) Since x + σv ∈ B for σ between 0 and τ, the Hölder hypothesis gives ‖(1/τ)∫_0^τ q^v_t(x + σv) dσ − q^v_t(x)‖ ≤ (1/|τ|)|∫_0^τ C|σ|^α dσ| ≤ C|τ|^α. Letting t → 0 in step 1: limsup_{t→0} ‖q^v_t(x) − q^v_τ(x)‖ ≤ C|τ|^α.
3. (Directional derivatives.) For t, t' → 0, ‖q^v_t(x) − q^v_{t'}(x)‖ ≤ ‖q^v_t(x) − q^v_τ(x)‖ + ‖q^v_τ(x) − q^v_{t'}(x)‖ has limsup ≤ 2C|τ|^α for every 0 < |τ| < τ₀, hence 0. So (q^v_t(x)) is Cauchy as t → 0 in the complete space L(ℝ^m, ℝ^k) and converges to some ∂_vf(x), and ‖∂_vf(x) − q^v_τ(x)‖ ≤ C|τ|^α for 0 < |τ| < τ₀.
4. (Bounds.) Passing to the limit in the hypotheses: ‖∂_vf(x)‖ ≤ C and ‖∂_vf(x) − ∂_vf(y)‖ ≤ C‖x − y‖^α for all x, y ∈ B and unit v.
5. (Fréchet differentiability.) Define the linear map L_x(w) := Σ_i w_i ∂_{e_i}f(x). For w ∈ ℝ^m with ‖w‖ < τ₀ put p_0 := x and p_i := p_{i−1} + w_i e_i; all p_i lie in B_{‖w‖}(x) ⊆ B. Then f(x + w) − f(x) = Σ_i [f(p_{i−1} + w_ie_i) − f(p_{i−1})], and for w_i ≠ 0, f(p_{i−1} + w_ie_i) − f(p_{i−1}) = w_i q^{e_i}_{w_i}(p_{i−1}). By step 3 at p_{i−1} (whose own τ₀ is at least (d_x − ‖w‖)/3 > 0 for ‖w‖ small), ‖q^{e_i}_{w_i}(p_{i−1}) − ∂_{e_i}f(p_{i−1})‖ ≤ C|w_i|^α, and by step 4 ‖∂_{e_i}f(p_{i−1}) − ∂_{e_i}f(x)‖ ≤ C‖w‖^α. Hence ‖f(x + w) − f(x) − L_x(w)‖ ≤ 2mC‖w‖^{1+α} for small w, so f is differentiable at x with Df(x) = L_x.
6. (Conclusion.) Differentiability gives Df(x)v = ∂_vf(x) for every unit v, so by step 4 ‖Df(x)‖ = sup_{‖v‖=1} ‖∂_vf(x)‖ ≤ C and ‖Df(x) − Df(y)‖ = sup_{‖v‖=1} ‖∂_vf(x) − ∂_vf(y)‖ ≤ C‖x − y‖^α. In particular Df is continuous on the open set B, so f is C¹ on B. ∎

## Key steps

1. Average the quotients q_t along the segment: (1/τ)∫_0^τ q_t(x + σv)dσ → q_τ(x) as t → 0.
2. The uniform Hölder bound gives limsup_{t→0}‖q_t(x) − q_τ(x)‖ ≤ C|τ|^α, so q_t(x) is Cauchy and the directional derivative exists with rate C|τ|^α.
3. Directional derivatives inherit the bound C and the α-Hölder bound.
4. Summing coordinate increments gives f(x + w) − f(x) − L_x w = O(‖w‖^{1+α}), so f is differentiable with Df(x)v = ∂_v f(x); hence C¹ with the stated bounds.

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
