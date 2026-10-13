# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.quasilinear_smooth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 5, proof of Theorem 7.1, last part (chapter-05.txt lines 1340–1366): once spt V is a C^{1,α} graph of u with small Du, u satisfies the system 1.3 and 'standard elliptic theory implies u ∈ C^{q+2,α}'. Here the graph is only known to be C¹, so the first step is the C^{1,α} estimate (the conclusion that Allard's theorem 5.2 would otherwise provide); the Schauder theory is supplied by c1alpha_estimate, difference_quotient, holder_algebra and linear_bootstrap (Giaquinta–Martinazzi 2012, Ch. 5). Weak equations are written W[·], H_n := C^{n,α}_loc(Ω) as in holder_algebra.

0. (Constants.) Fix α := 1/2. Let ε_D be the ε₁ of c1alpha_estimate and ε_L the ε₁ of linear_bootstrap for (m, k, α). L(ℝ^m, ℝ^k) is finite-dimensional, so closed balls in it are compact. DG is continuous with DG(0) = 0, so there is ε₀ ∈ (0, 1] with Λ := sup_{‖p‖≤ε₀} ‖DG(p)‖ satisfying Λ ≤ ε_D, 2Λ² ≤ ε_D and Λ ≤ ε_L; let Λ₂ := sup_{‖p‖≤ε₀} ‖D²G(p)‖ < ∞. On the convex set {‖p‖ ≤ ε₀}: ‖G(p) − G(q)‖ ≤ Λ‖p − q‖, ‖G(p)‖ ≤ Λ‖p‖ (G(0) = 0) and ‖DG(p) − DG(q)‖ ≤ Λ₂‖p − q‖. Fix Ω and u as in the statement. Note ‖⨍ Du‖ ≤ ⨍‖Du‖ ≤ ε₀ for averages over balls in Ω.

1. (C^{1,α}.) Fix x ∈ Ω and R > 0 with closedBall(x, R) ⊆ Ω. w := u − u(x) is C¹ on B_R(x) with Dw = Du and ‖w‖ ≤ ε₀R =: K₀ (mean value inequality). F := G∘Du is continuous and ‖F‖ ≤ Λ‖Du‖ ≤ ε_D‖Dw‖ + K₀. For closedBall(z, ρ) ⊆ B_R(x) take c := G((Du)_{z,ρ}); then ‖F(y) − c‖ ≤ Λ‖Du(y) − (Du)_{z,ρ}‖, so ∫_{B_ρ(z)} ‖F − c‖² ≤ Λ²∫‖Du − (Du)_{z,ρ}‖² ≤ ε_D∫‖Dw − (Dw)_{z,ρ}‖². The weak equation on B_R(x) follows from the one on Ω (test maps supported in B_R(x) are admissible; integrands vanish off their supports). c1alpha_estimate (K := K₀) shows that Du is α-Hölder on B_{R/4}(x), with some constant C₁.

2. (C^{2,α}.) Keep x, R, C₁ from step 1; on B₁ := B_{R/4}(x), Du is C₁-Hölder and ‖Du‖ ≤ ε₀. Let v be a unit vector, 0 < |t| < R/16, and w_t(y) := t⁻¹(u(y + tv) − u(y)) for y ∈ B_{R/8}(x) (then y, y + tv ∈ B₁).
(a) w_t is C¹ on B_{R/8}(x), Dw_t(y) = t⁻¹(Du(y + tv) − Du(y)), and ‖w_t‖ ≤ ε₀.
(b) W[Δw_t = div F_t] on B_{R/8}(x) with F_t(y) := t⁻¹(G(Du(y + tv)) − G(Du(y))): apply the equation of u to ζ(· − tv) (admissible: its support lies in B_{R/8+R/16}(x) ⊆ Ω), substitute y ↦ y + tv, subtract the equation for ζ and divide by t.
(c) F_t(y) = B_t(y)[Dw_t(y)] with B_t(y) := ∫_0^1 DG(Du(y) + σ(Du(y + tv) − Du(y))) dσ (fundamental theorem of calculus along a segment in the ε₀-ball). ‖B_t‖ ≤ Λ, and ‖B_t(y) − B_t(y')‖ ≤ Λ₂(‖Du(y) − Du(y')‖ + ‖Du(y + tv) − Du(y' + tv)‖) ≤ 2Λ₂C₁‖y − y'‖^α.
(d) Hence ‖F_t‖ ≤ Λ‖Dw_t‖ ≤ ε_D‖Dw_t‖, and for closedBall(z, ρ) ⊆ B_{R/8}(x), with c := B_t(z)[(Dw_t)_{z,ρ}] and F_t(y) − c = (B_t(y) − B_t(z))[Dw_t(y)] + B_t(z)[Dw_t(y) − (Dw_t)_{z,ρ}]: ∫‖F_t − c‖² ≤ 8Λ₂²C₁²ρ^{2α}∫‖Dw_t‖² + 2Λ²∫‖Dw_t − (Dw_t)_{z,ρ}‖² ≤ ε_D∫‖Dw_t − (Dw_t)_{z,ρ}‖² + Kρ^{2α}∫‖Dw_t‖², with K := max(ε₀, 8Λ₂²C₁²) independent of t, v.
(e) c1alpha_estimate on B_{R/8}(x) yields C₂, independent of t and v, with ‖Dw_t‖ ≤ C₂ and ‖Dw_t(y) − Dw_t(y')‖ ≤ C₂‖y − y'‖^α on B_{R/32}(x).
(f) Since Dw_t(y) = t⁻¹(Du(y + tv) − Du(y)), difference_quotient applied to f := Du on B_{R/64}(x) with h₀ := R/64 (for y ∈ B_{R/64}(x) and |t| < R/64 both y and y + tv lie in B_{R/32}(x)) shows that Du is C¹ on B_{R/64}(x) with α-Hölder derivative.
As x ∈ Ω is arbitrary, Du is C¹ on Ω and D(Du) is locally α-Hölder, i.e. Du ∈ H_1 (holder_algebra (6) with l = 0), and u ∈ H_2 (holder_algebra (6) with l = 1).

3. (Bootstrap.) We show u ∈ H_{l+1} for all l ≥ 1 by induction; l = 1 is step 2. Let l ≥ 1 and u ∈ H_{l+1}, so u is C² on Ω. For s ∈ {1, …, m} let v_s(y) := Du(y)e_s, which is C¹ on Ω.
(a) (Differentiated equation.) ∫_Ω Σ_j ⟨Dv_s e_j, Dζ e_j⟩ = ∫_Ω Σ_j ⟨(DG(Du)[Dv_s] + 0)e_j, Dζ e_j⟩ for admissible ζ. Indeed, with d > 0 the distance from tsupport ζ to ℝ^m \ Ω and 0 < |t| < d/2, the computation of step 2(b) with v = e_s gives ∫⟨Dw_t, Dζ⟩ = ∫⟨t⁻¹(G(Du(· + te_s)) − G(Du)), Dζ⟩, where w_t := t⁻¹(u(· + te_s) − u). As t → 0, uniformly on tsupport ζ, Dw_t(y)e_j → D²u(y)(e_s, e_j) = D²u(y)(e_j, e_s) = Dv_s(y)e_j and t⁻¹(G(Du(y + te_s)) − G(Du(y))) → DG(Du(y))[D²u(y)(e_s, ·)] = DG(Du(y))[Dv_s(y)] (u is C², symmetry of second derivatives, uniform continuity on a compact neighbourhood); the integrands are uniformly bounded with support in tsupport ζ, so the identity passes to the limit.
(b) (Coefficients.) B := DG∘Du. By holder_algebra (6), Du ∈ H_l; DG is C^∞; so B ∈ H_l by holder_algebra (4). ‖B‖ ≤ Λ ≤ ε_L on Ω. The zero map is in H_l (holder_algebra (1)).
(c) linear_bootstrap (with w := v_s, this B and g := 0) gives v_s ∈ H_{l+1}.
(d) Du(y) = Σ_s λ_s(v_s(y)) with λ_s : ℝ^k → L(ℝ^m, ℝ^k), λ_s(b)(a) := ⟨a, e_s⟩b, continuous linear; by holder_algebra (4), (2), Du ∈ H_{l+1}, hence u ∈ H_{l+2} by holder_algebra (6).

4. (Conclusion.) For every l, u ∈ H_{l+1}; in particular u is C^{l+1} on Ω. Hence u is C^r on Ω for every r ∈ ℕ. ∎

## Key steps

1. Choose ε₀ so that Λ = sup_{‖p‖≤ε₀}‖DG(p)‖ is below the thresholds of c1alpha_estimate and linear_bootstrap.
2. C^{1,α}: F = G(Du) satisfies ‖G(Du) − G(avg)‖ ≤ Λ‖Du − avg‖, so c1alpha_estimate makes Du locally α-Hölder.
3. C^{2,α}: the difference quotients w_t solve Δw_t = div(B_t[Dw_t]) with ‖B_t‖ ≤ Λ and B_t uniformly α-Hölder; c1alpha_estimate gives uniform C^{1,α} bounds and difference_quotient gives Du ∈ C^{1,α}.
4. Bootstrap: v_s = ∂_s u solves Δv_s = div(DG(Du)[Dv_s]) with DG(Du) ∈ C^{l,α}_loc (holder_algebra), so linear_bootstrap gives v_s ∈ C^{l+1,α}_loc and u ∈ C^{l+2,α}_loc for every l.

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
