# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.harmonic_replacement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the harmonic comparison step of Campanato's approach to Schauder estimates (Giaquinta–Martinazzi, An Introduction to the Regularity Theory for Elliptic Systems, Harmonic Maps and Minimal Graphs, 2nd ed. 2012, Ch. 5, §5.4.1: compare with the solution of the frozen problem), done here without a Dirichlet solver: the harmonic part is obtained from the orthogonal projection onto the closure of gradients of test functions, and its smoothness from Weyl's lemma (sibling weyl_lemma = Submission.dorag_ha_weyl_lemma).

0. (Notation.) B := B_R(x₀). For ξ ∈ L(ℝ^m, ℝ^k) and κ ∈ {1, …, k} let ξ^κ ∈ ℝ^m be the vector with components ⟨ξe_j, e_κ⟩; then |ξ|² = Σ_κ ‖ξ^κ‖². Let w^κ := ⟨w, e_κ⟩, so (Dw)^κ = ∇w^κ. Since closedBall(x₀, R) ⊆ B_{R'}(x₀) is compact, Dw and F are continuous and bounded on it, so ∇w^κ and F^κ belong to H := L²(B; ℝ^m), a Hilbert space with ⟨f, g⟩_H = ∫_B f·g. Constant vector fields belong to H (B has finite measure).

1. (Scalar weak equations.) Let C¹_c(B) be the real C¹ functions on ℝ^m with compact support and tsupport ⊆ B. For φ ∈ C¹_c(B), ζ := φ·e_κ is admissible and Dζ(x)e_j = ∂_jφ(x)e_κ, so the hypothesis reads ∫_B ∇w^κ·∇φ = ∫_B F^κ·∇φ. Also ∫_B c·∇φ = 0 for every constant c ∈ ℝ^m (∫ ∂_jφ = 0 for compactly supported C¹ φ).

2. (Poincaré inequality.) For φ ∈ C¹_c(B), the C¹ compactly supported vector field φ²(x − x₀) has divergence mφ² + 2φ∇φ·(x − x₀) and integral of its divergence 0 (Mathlib integration by parts, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, coordinatewise). Hence m∫_B φ² = −2∫_B φ∇φ·(x − x₀) ≤ 2R‖φ‖_{L²(B)}‖∇φ‖_{L²(B)}, i.e. ‖φ‖_{L²(B)} ≤ (2R/m)‖∇φ‖_{L²(B)}.

3. (Projection.) S := {∇φ : φ ∈ C¹_c(B)} ⊆ H is a linear subspace; let S̄ be its closure (a closed, hence complete, subspace) and Π the orthogonal projection onto S̄. By step 1, ∇w^κ − F^κ ⊥ S, hence ⊥ S̄, so Π∇w^κ = ΠF^κ; and every constant c ⊥ S̄, so ΠF^κ = Π(F^κ − c). Put z^κ := Π∇w^κ. Then ‖z^κ‖_H = ‖Π(F^κ − c^κ)‖_H ≤ ‖F^κ − c^κ‖_H for every c ∈ L(ℝ^m, ℝ^k).

4. (A potential for z^κ.) Choose φ_j ∈ C¹_c(B) with ∇φ_j → z^κ in H. By step 2, (φ_j) is Cauchy in L²(B), so φ_j → ψ^κ in L²(B). For η ∈ C¹_c(B) and l ∈ {1, …, m}: ∫_B ψ^κ ∂_lη = lim ∫_B φ_j ∂_lη = −lim ∫_B ∂_lφ_j η = −∫_B z^κ_l η (integration by parts for the compactly supported C¹ functions φ_jη; L² convergence on the finite-measure ball).

5. (Weak harmonicity.) Let v^κ := w^κ − ψ^κ ∈ L²(B) ⊆ L¹(B). For η ∈ C²(ℝ^m) with compact support and tsupport η ⊆ B: ∫_B w^κ Δη = −∫_B ∇w^κ·∇η (w is C¹ near tsupport η), and ∫_B ψ^κ Δη = −∫_B z^κ·∇η (step 4 applied to ∂_lη ∈ C¹_c(B), summed over l). Hence ∫_B v^κ Δη = −⟨∇w^κ − z^κ, ∇η⟩_H = 0, because ∇w^κ − z^κ = (I − Π)∇w^κ ⊥ S̄ and ∇η ∈ S.

6. (Weyl.) Apply weyl_lemma to W(y) := v^κ(x₀ + y) on B_R(0) (translation preserves integrability and the identity of step 5, test functions being translated). It gives h^κ, C^j on B for all j, harmonic on B, with h^κ = v^κ a.e. on B.

7. (Gradients.) For η ∈ C^∞ with compact support in B and each l: ∫_B ∂_lh^κ η = −∫_B h^κ ∂_lη = −∫_B v^κ ∂_lη = −∫_B w^κ ∂_lη + ∫_B ψ^κ ∂_lη = ∫_B ∂_lw^κ η − ∫_B z^κ_l η. The function ∂_lh^κ − ∂_lw^κ + z^κ_l is locally integrable on B and integrates to zero against every such η, so it vanishes a.e. on B (Mathlib ae_eq_zero_of_integral_contDiff_smul_eq_zero). Thus ∇w^κ − ∇h^κ = z^κ a.e. on B.

8. (Conclusion.) h := Σ_κ h^κ e_κ is C^j on B for every j and Σ_i D²h(e_i, e_i) = Σ_κ (Δh^κ)e_κ = 0 on B. Since (Dw − Dh)^κ = ∇w^κ − ∇h^κ = z^κ a.e., |Dw − Dh|² = Σ_κ ‖z^κ‖² a.e. on B is integrable and ∫_B |Dw − Dh|² = Σ_κ ‖z^κ‖²_H ≤ Σ_κ ‖F^κ − c^κ‖²_H = ∫_B |F − c|² for every constant c. ∎

## Key steps

1. Componentwise scalar weak equations ∫∇w^κ·∇φ = ∫F^κ·∇φ, and constants are orthogonal to gradients of test functions.
2. Poincaré inequality ‖φ‖_{L²} ≤ (2R/m)‖∇φ‖_{L²} for compactly supported C¹ φ via the radial field.
3. z^κ := Π∇w^κ (projection onto the closure of test gradients) equals Π(F^κ − c), so ‖z^κ‖ ≤ ‖F^κ − c‖.
4. z^κ is the weak gradient of an L² limit ψ^κ; w^κ − ψ^κ is weakly harmonic, hence a.e. a smooth harmonic h^κ by Weyl's lemma.
5. ∇w^κ − ∇h^κ = z^κ a.e.; summing over κ gives the energy bound.

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
