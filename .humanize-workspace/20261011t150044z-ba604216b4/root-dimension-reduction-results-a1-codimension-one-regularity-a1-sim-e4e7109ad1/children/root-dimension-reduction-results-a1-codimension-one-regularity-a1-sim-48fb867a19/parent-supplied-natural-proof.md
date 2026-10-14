# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.harmonic_decay-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the constant-coefficient decay estimates of Campanato's method (Giaquinta–Martinazzi 2012, Ch. 5, §5.4.1, for the Laplacian), derived from the interior estimates for harmonic functions (sibling interior_estimates = Submission.dorag_ha_interior_estimates; Simon Ch. 5, 3.2–3.4).
Notation: ω := |B_1(0)|, so |B_ρ(x)| = ωρ^m; for f with |f|² integrable on a ball, f is integrable there (finite measure), and its average f̄ minimizes c ↦ ∫|f − c|² because ∫⟨f − f̄, f̄ − c⟩ = 0 for the Hilbert–Schmidt inner product ⟨A, B⟩ = Σ_j ⟨Ae_j, Be_j⟩ (evaluation at e_j commutes with averages). Φ(ρ) := ∫_{B_ρ(x₀)} |Dh − (Dh)_{x₀,ρ}|², Ψ(ρ) := ∫_{B_ρ(x₀)} |Dh|². Let C_H be the constant of interior_estimates for n = m. For a component κ write h^κ := ⟨h, e_κ⟩ and ∇h^κ for its gradient, so |Dh|² = Σ_κ ‖∇h^κ‖².

1. (Large r.) If R/4 < r ≤ R: Φ(r) ≤ ∫_{B_r} |Dh − (Dh)_{x₀,R}|² ≤ Φ(R) ≤ 4^{m+2}(r/R)^{m+2}Φ(R), and Ψ(r) ≤ Ψ(R) ≤ 4^m (r/R)^m Ψ(R).

2. (Normalized interior estimates.) Fix κ, a vector c ∈ ℝ^m and x ∈ B_{R/4}(x₀); then closedBall(x, R/2) ⊆ B_R(x₀). Let g(z) := h^κ(z) − c·z and f(v) := g(x + v) − g(x); f is C^∞ and harmonic on B_{R/2}(0), bounded there (continuity on the compact closedBall(x, R/2)), so f² is integrable on B_{R/2}(0), and ‖Df‖² = ‖∇h^κ(x + ·) − c‖² is integrable there. Let λ² := (R/2)^{−m}∫_{B_{R/2}(0)} ‖Df‖². If λ = 0 then ∇g ≡ 0 on B_{R/2}(x) (continuity), so g is constant on B_{R/2}(x). If λ > 0, apply interior_estimates to f/λ with radius R/2 (its gradient energy equals (R/2)^m). In both cases: (a) ‖∇g(x)‖ ≤ C_H λ, and (b) |g(x + v) − g(x) − ∇g(x)·v| ≤ 2C_H λ ‖v‖²/R for ‖v‖ ≤ R/8. Moreover λ² ≤ (R/2)^{−m}∫_{B_R(x₀)} ‖∇h^κ − c‖².

3. (Proof of (ii) for r ≤ R/4.) Take c = 0 in step 2(a): for x ∈ B_r(x₀) ⊆ B_{R/4}(x₀), ‖∇h^κ(x)‖² ≤ C_H² 2^m R^{−m} ∫_{B_R(x₀)} ‖∇h^κ‖². Summing over κ: |Dh(x)|² ≤ C_H² 2^m R^{−m} Ψ(R). Integrating over B_r(x₀): Ψ(r) ≤ ω 2^m C_H² (r/R)^m Ψ(R).

4. (Lipschitz bound for ∇h^κ on B_{R/4}(x₀).) Take c := ((Dh)_{x₀,R})^κ (the κ-th row of the average), so ‖∇h^κ − c‖² ≤ |Dh − (Dh)_{x₀,R}|² and every λ in step 2 satisfies λ ≤ λ* := ((R/2)^{−m}Φ(R))^{1/2}. Let x, x' ∈ B_{R/4}(x₀) with d := ‖x − x'‖ ≤ R/16, d > 0, and e a unit vector. By step 2(b) at the centers x and x' (all displacements below have length ≤ 2d ≤ R/8):
 g(x + de) − g(x) = d∇g(x)·e + E₁,
 g(x + de) − g(x') = ∇g(x')·(x − x' + de) + E₃,
 g(x) − g(x') = ∇g(x')·(x − x') + E₄,
with |E_i| ≤ 8C_Hλ*d²/R. Subtracting the third identity from the second and comparing with the first: d(∇g(x) − ∇g(x'))·e = E₃ − E₄ − E₁, so |(∇h^κ(x) − ∇h^κ(x'))·e| = |(∇g(x) − ∇g(x'))·e| ≤ 24C_Hλ*d/R. Taking the supremum over e: ‖∇h^κ(x) − ∇h^κ(x')‖ ≤ 24C_Hλ*‖x − x'‖/R whenever ‖x − x'‖ ≤ R/16. For arbitrary x, x' ∈ B_{R/4}(x₀) divide the segment [x, x'] (contained in the convex ball) into 8 equal pieces of length ≤ R/16 and add: the same bound holds.

5. (Proof of (i) for r ≤ R/4.) For x ∈ B_r(x₀), step 4 with x' = x₀ gives |Dh(x) − Dh(x₀)|² = Σ_κ ‖∇h^κ(x) − ∇h^κ(x₀)‖² ≤ k(24C_H)²λ*² r²/R². By minimality of the average, Φ(r) ≤ ∫_{B_r(x₀)} |Dh − Dh(x₀)|² ≤ ωr^m·k(24C_H)²(R/2)^{−m}Φ(R)r²/R² = ω2^m k(24C_H)² (r/R)^{m+2} Φ(R).

6. (Constant.) C := max(4^{m+2}, ω2^m C_H², ω2^m k(24C_H)², 1) works for all 0 < r ≤ R by steps 1, 3 and 5; it depends only on m and k. ∎

## Key steps

1. For r > R/4 both estimates are trivial with constants 4^{m+2} and 4^m (the average minimizes the L² deviation).
2. Normalize each component on B_{R/2}(x), x ∈ B_{R/4}(x₀), and apply the accepted interior estimates: gradient bound and quadratic Taylor remainder with factor λ ≤ ((R/2)^{−m}∫_{B_R}|Dh − c|²)^{1/2}.
3. Gradient bound at every point of B_r(x₀) gives the Morrey decay (ii).
4. Taylor bounds at two nearby centers give a Lipschitz bound 24C_Hλ*/R for ∇h^κ on B_{R/4}(x₀), hence the Campanato decay (i).

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
