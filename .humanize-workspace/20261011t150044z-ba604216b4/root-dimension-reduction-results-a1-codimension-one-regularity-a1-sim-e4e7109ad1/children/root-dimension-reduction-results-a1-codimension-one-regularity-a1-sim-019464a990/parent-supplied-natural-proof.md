# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.stationary_mss-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 5, §1 (chapter-05.txt lines 50–131: for M = graph u near a point, stationarity is the system 1.3, the Euler–Lagrange system of the area integrand), Ch. 4, 2.2–2.6 (first variation δV(X) = ∫ div_M X), and the area formula (Simon Ch. 2, §3; SimonGMT Chapter02.injective_area_formula_of_injective_derivative). This is the step of Simon's proof of Theorem 5.7.1 asserting that the graph u satisfies (2)/(3) with h = 0 (N = ℝ^P).
Notation: L := L(ℝ^m, ℝ^k); for A, B ∈ L, ⟨A, B⟩ := Σ_j ⟨Ae_j, Be_j⟩; λ := Lebesgue measure on ℝ^m, which equals H^m on ℝ^m.

1. (Definition of G.) For p ∈ L let g(p) := I + p*p : ℝ^m → ℝ^m, so ⟨g(p)e_i, e_j⟩ = δ_ij + ⟨pe_i, pe_j⟩. g(p) is self-adjoint and ⟨g(p)v, v⟩ = ‖v‖² + ‖pv‖² ≥ ‖v‖², so g(p) is invertible and det g(p) ≥ 1. Put J(p) := √(det g(p)), A(p) := J(p)·(p ∘ g(p)⁻¹) and G(p) := p − A(p). G depends only on m, k.

2. (G is C^∞.) p ↦ g(p) is a continuous polynomial map (p ↦ p*p is continuous bilinear-quadratic); det is polynomial; √ is C^∞ on (0, ∞) and det g ≥ 1; inversion is C^∞ on the open set of invertible operators (Mathlib contDiffAt_ringInverse); products and compositions of C^∞ maps are C^∞.

3. (G(0) = 0, DG(0) = 0.) A(0) = 1·(0 ∘ I) = 0, so G(0) = 0. For q ∈ L and τ ∈ ℝ, g(τq) = I + τ²q*q, so J(τq) = 1 + O(τ²) and g(τq)⁻¹ = I + O(τ²); hence A(τq) = τq + O(τ³), DA(0)q = q, i.e. DA(0) = id and DG(0) = id − DA(0) = 0.

4. (Linear algebra at a graph point.) Fix a ∈ B_s(0), p := Du(a), τ_i := DF(a)e_i = ιe_i + ι'(pe_i). By orthogonality of the ranges, ⟨τ_i, τ_j⟩ = δ_ij + ⟨pe_i, pe_j⟩ = g(p)_ij; T := range DF(a) = span{τ_1, …, τ_m} has dimension m and DF(a)*DF(a) = g(p). The orthogonal projection onto T is P_T z = Σ_{i,j} (g(p)⁻¹)_ij ⟨τ_j, z⟩ τ_i, and for every linear map L of ℝ^P, trace(P_T ∘ L) = trace(L ∘ P_T) = Σ_{i,j} (g(p)⁻¹)_ij ⟨τ_j, Lτ_i⟩ (trace of a rank-one map z ↦ ⟨α, z⟩β is ⟨α, β⟩). The Jacobian of F at a is √det(DF(a)*DF(a)) = J(p).

5. (Test vector field.) Let ζ be as in the conclusion and S₀ := tsupport ζ, a compact subset of B_s(0). C₀ := F(S₀) is compact (F is continuous on B_s(0)) and C₀ ⊆ Z because ‖u‖ < t on B_s(0). Choose θ : ℝ^P → [0, 1], C^∞ with compact support, θ = 1 on C₀ and tsupport θ ⊆ Z (smooth Urysohn lemma for the compact set C₀ in the open set Z, e.g. Mathlib exists_contMDiff_zero_iff_one_iff_of_isClosed applied to C₀ and the complement of an open neighbourhood of C₀ with compact closure in Z). Put π := ι* and X(z) := θ(z)·ι'(ζ(π(z − y))). X is C¹ with compact support and tsupport X ⊆ tsupport θ ⊆ Z ⊆ U, so X is admissible in the stationarity hypothesis.

6. (X ∘ F = ι' ∘ ζ on B_s(0).) π(F(a) − y) = a, so X(F(a)) = θ(F(a))·ι'ζ(a). If a ∈ S₀ then θ(F(a)) = 1; otherwise ζ(a) = 0. Hence X(F(a)) = ι'ζ(a) on the open set B_s(0), and by the chain rule DX(F(a))τ_i = ∂_i(X∘F)(a) = ι'(Dζ(a)e_i).

7. (The integrand.) Let f(x) := trace(P_x ∘ DX(x)). If x ∉ tsupport X then X vanishes on a neighbourhood of x, so DX(x) = 0 and f(x) = 0; in particular f = 0 off Z. For a ∈ B_s(0) and x = F(a), tangentSpace M x = range DF(a) = T is a subspace, so P_x = P_T, and by steps 4 and 6, with p = Du(a): f(F(a)) = Σ_{i,j} (g(p)⁻¹)_ij ⟨τ_j, ι'(Dζ(a)e_i)⟩ = Σ_{i,j} (g(p)⁻¹)_ij ⟨pe_j, Dζ(a)e_i⟩. Since A(p)e_i = J(p) Σ_j (g(p)⁻¹)_ji pe_j and g(p)⁻¹ is symmetric, J(p)·f(F(a)) = Σ_i ⟨A(p)e_i, Dζ(a)e_i⟩ = ⟨A(Du(a)), Dζ(a)⟩.

8. (Reduction to F(B_s(0)) and integrability.) Let μ := H^m. Since Z is open, μ⌞M = (μ⌞M)⌞Z + (μ⌞M)⌞Zᶜ and (μ⌞M)⌞Z = μ⌞(M ∩ Z) = μ⌞F(B_s(0)). f = 0 on Zᶜ, so f is integrable for (μ⌞M)⌞Zᶜ with integral 0. On F(B_s(0)) (a Borel set: the continuous injective image of an open set, Mathlib MeasurableSet.image_of_continuousOn_injOn), f(x) equals the step-7 expression evaluated at a = π(x − y), a continuous function of x on the open set {x : π(x − y) ∈ B_s(0)}; so f is a.e.-strongly measurable for μ⌞F(B_s(0)). Moreover |f| ≤ m·sup‖DX‖ (trace of P∘L with P of rank m) and f vanishes outside tsupport X, while μ(F(B_s(0)) ∩ tsupport X) ≤ μ(M ∩ tsupport X) < ∞ by hypothesis (tsupport X is compact and ⊆ U). Hence f is integrable for μ⌞M and ∫_M f dμ = ∫_{F(B_s(0))} f dμ.

9. (Area formula.) F is C¹ and injective on B_s(0) with injective derivative (π∘DF(a) = id). By SimonGMT injective_area_formula_of_injective_derivative (normDet DF(a) = √det(DF(a)*DF(a)) = J(Du(a)) by step 4), μ(F(E)) = ∫_E J(Du) dλ for every Borel E ⊆ B_s(0). For Borel A ⊆ ℝ^P, injectivity gives F(B_s(0)) ∩ A = F(B_s(0) ∩ F⁻¹(A)), so μ⌞F(B_s(0)) is the push-forward of J(Du)·λ⌞B_s(0) under F, and ∫_{F(B_s(0))} f dμ = ∫_{B_s(0)} f(F(a)) J(Du(a)) da.

10. (Conclusion.) By stationarity and steps 7–9, 0 = ∫_M f dμ = ∫_{B_s(0)} ⟨A(Du(a)), Dζ(a)⟩ da. Since A = id − G, and both a ↦ ⟨Du(a), Dζ(a)⟩ and a ↦ ⟨G(Du(a)), Dζ(a)⟩ are continuous on B_s(0) and vanish off the compact set S₀ ⊆ B_s(0) (hence integrable), ∫_{B_s(0)} ⟨Du, Dζ⟩ = ∫_{B_s(0)} ⟨G(Du), Dζ⟩. ∎

## Key steps

1. Define g(p) = I + p*p, J = √det g, A(p) = J·p∘g⁻¹ and G = id − A; G is C^∞ with G(0) = 0 and DG(0) = 0.
2. At a graph point the tangent plane is spanned by τ_i = DF(a)e_i with Gram matrix g(Du(a)), so trace(P_T∘L) = Σ g^{ij}⟨τ_j, Lτ_i⟩ and the Jacobian is J(Du).
3. Build X = θ·ι'(ζ∘ι*(· − y)) with θ = 1 on F(tsupport ζ) and tsupport θ ⊆ Z ⊆ U, so X∘F = ι'∘ζ and the trace integrand becomes ⟨A(Du), Dζ⟩/J(Du).
4. The integrand vanishes off Z, is bounded, measurable and supported in finite measure, so ∫_M equals ∫ over F(B_s(0)).
5. Area formula transfers the integral to ∫_{B_s} ⟨A(Du), Dζ⟩ = 0, i.e. ∫⟨Du, Dζ⟩ = ∫⟨G(Du), Dζ⟩.

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
