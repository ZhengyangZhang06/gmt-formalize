# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.c1alpha_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Campanato's proof of the Schauder estimates for systems in divergence form (Giaquinta–Martinazzi 2012, Ch. 5, §§5.1–5.4; Giaquinta 1983, Ch. III), which is the 'Schauder theory' invoked without proof in Simon's proof of Theorem 5.7.1. Dependencies: harmonic_replacement, harmonic_decay, campanato_lemmas.

0. (Notation and choice of ε₁.) |A|² := Σ_j ‖Ae_j‖² (Hilbert–Schmidt), so ‖A‖ ≤ |A| ≤ √m‖A‖. ω := |B_1(0)|. For closedBall(x, ρ) ⊆ B_R(x₀) put Ψ(x, ρ) := ∫_{B_ρ(x)} |Dw|² and Φ(x, ρ) := ∫_{B_ρ(x)} |Dw − (Dw)_{x,ρ}|², (Dw)_{x,ρ} := ⨍_{B_ρ(x)} Dw; these are finite (Dw is continuous on the compact closed ball), Ψ(x, ·) and Φ(x, ·) are nondecreasing and nonnegative (Φ(x, r) = min_c ∫_{B_r(x)} |Dw − c|², the average minimizing in the Hilbert–Schmidt norm), and Φ ≤ Ψ. Let C_C be the constant of harmonic_decay for (m, k) and A₁ := (4C_C + 2)m. By campanato_lemmas (I) let (ε_a, c_a), (ε_b, c_b), (ε_c, c_c) be the constants for (A, a, b) = (A₁, m, m − α), (A₁, m + 2, m + α), (A₁, m + 2, m + 2α) (all with 0 < b < a since 0 < α < 1). Let C₀', C₀'' be the constants of campanato_lemmas (II) for exponents α/2 and α. Set ε₁ := min(1/(4√m), (ε_a/2)^{1/2}, ε_b, ε_c) > 0; it depends only on m, k, α. Fix K ≥ 0 and R > 0, and put R₁ := R/8. All constants C₃, …, C₈ below depend only on m, k, α, K, R.

1. (Comparison inequalities.) Let closedBall(x, ρ) ⊆ B_R(x₀) and 0 < r ≤ ρ. Choose ρ' > ρ with B_{ρ'}(x) ⊆ B_R(x₀). The weak equation holds in B_ρ(x) (test maps supported in B_ρ(x) are admissible in B_R(x₀) and the integrands vanish outside their supports). harmonic_replacement (with R := ρ, R' := ρ') gives a smooth harmonic h on B_ρ(x) with |Dw − Dh|² integrable and ∫_{B_ρ(x)} |Dw − Dh|² ≤ ∫_{B_ρ(x)} |F − c|² for every constant c. |Dh|² ≤ 2|Dw|² + 2|Dw − Dh|² is integrable, so harmonic_decay applies to h on B_ρ(x). With Φ_h, Ψ_h the analogous quantities for h: Φ(x, r) ≤ ∫_{B_r(x)} |Dw − (Dh)_{x,r}|² ≤ 2Φ_h(r) + 2∫_{B_ρ(x)} |Dw − Dh|² ≤ 2C_C(r/ρ)^{m+2}Φ_h(ρ) + 2∫_{B_ρ(x)}|Dw − Dh|² and Φ_h(ρ) ≤ ∫_{B_ρ(x)} |Dh − (Dw)_{x,ρ}|² ≤ 2Φ(x, ρ) + 2∫_{B_ρ(x)} |Dw − Dh|². Hence, for every constant c:
(C1) Φ(x, r) ≤ 4C_C(r/ρ)^{m+2}Φ(x, ρ) + (4C_C + 2)∫_{B_ρ(x)} |F − c|²;
(C2) Ψ(x, r) ≤ 4C_C(r/ρ)^mΨ(x, ρ) + (4C_C + 2)∫_{B_ρ(x)} |F|² (same argument with c = 0).
Using |F − c|² ≤ m‖F − c‖², (H_F), ∫‖Dw − (Dw)_{x,ρ}‖² ≤ Φ(x, ρ) and ∫‖Dw‖² ≤ Ψ(x, ρ) in (C1), and ‖F‖² ≤ (ε₁‖Dw‖ + K)² ≤ 2ε₁²|Dw|² + 2K² in (C2):
(C1') Φ(x, r) ≤ A₁[(r/ρ)^{m+2} + ε₁]Φ(x, ρ) + A₁K(ρ^{2α}Ψ(x, ρ) + ρ^{m+2α});
(C2') Ψ(x, r) ≤ A₁[(r/ρ)^m + 2ε₁²]Ψ(x, ρ) + 2A₁K²ωρ^m.

2. (Caccioppoli.) Let closedBall(x, ρ) ⊆ B_R(x₀). Take η ∈ C^∞ with compact support in B_ρ(x), 0 ≤ η ≤ 1, η = 1 on B_{ρ/2}(x), ‖∇η‖ ≤ 4/ρ. ζ := η²w is C¹ on ℝ^m (C¹ on B_R(x₀), and zero on a neighbourhood of every point outside tsupport η) with compact support in B_ρ(x), and Dζ = η²Dw + 2η w⊗∇η. The weak equation gives ∫η²|Dw|² = ∫η²⟨F, Dw⟩ + 2∫η⟨F − Dw, w⊗∇η⟩ (Hilbert–Schmidt pairings). Now |⟨F, Dw⟩| ≤ |F||Dw| ≤ √m(ε₁‖Dw‖ + K)|Dw| ≤ (1/4)|Dw|² + √mK|Dw| and |F| ≤ (1/4)|Dw| + √mK (as √mε₁ ≤ 1/4), ‖w‖ ≤ K, ‖∇η‖ ≤ 4/ρ. Hence ∫η²|Dw|² ≤ (1/4)∫η²|Dw|² + √mK∫η²|Dw| + (8K/ρ)∫η((5/4)|Dw| + √mK) over B_ρ(x); estimating √mK η²|Dw| ≤ (1/8)η²|Dw|² + 2mK², (10K/ρ)η|Dw| ≤ (1/8)η²|Dw|² + 2(10K/ρ)² and (8√mK²/ρ)∫_{B_ρ(x)} η ≤ 8√mωK²ρ^{m−1} ≤ 4√mωK²(ρ^{m−2} + ρ^m), and absorbing the (1/4 + 1/8 + 1/8)∫η²|Dw|² terms into the left side, ∫η²|Dw|² ≤ C_m K²(ρ^{m−2} + ρ^m) with C_m depending only on m. So Ψ(x, ρ/2) ≤ C_mK²(ρ^{m−2} + ρ^m).

3. (Morrey decay.) Let x ∈ B_{R/2}(x₀). For 0 < r ≤ ρ ≤ R₁, closedBall(x, ρ) ⊆ B_{5R/8}(x₀) ⊆ B_R(x₀), and (C2') gives Ψ(x, r) ≤ A₁[(r/ρ)^m + 2ε₁²]Ψ(x, ρ) + 2A₁K²ωR₁^αρ^{m−α}. Since 2ε₁² ≤ ε_a, campanato_lemmas (I) with φ = Ψ(x, ·), R₀ = R₁, B = 2A₁K²ωR₁^α yields Ψ(x, r) ≤ c_a((r/R₁)^{m−α}Ψ(x, R₁) + Br^{m−α}). Step 2 with ρ = R/4 (closedBall(x, R/4) ⊆ B_{3R/4}(x₀)) bounds Ψ(x, R₁). Hence Ψ(x, r) ≤ C₃r^{m−α} for x ∈ B_{R/2}(x₀), 0 < r ≤ R₁.

4. (First Campanato pass.) For x ∈ B_{R/2}(x₀) and 0 < r ≤ ρ ≤ R₁, (C1') and step 3 give Φ(x, r) ≤ A₁[(r/ρ)^{m+2} + ε₁]Φ(x, ρ) + A₁K(C₃ + R₁^α)ρ^{m+α}. As ε₁ ≤ ε_b, campanato_lemmas (I) gives Φ(x, r) ≤ c_b((r/R₁)^{m+α}Φ(x, R₁) + A₁K(C₃ + R₁^α)r^{m+α}) ≤ C₅r^{m+α}, using Φ(x, R₁) ≤ Ψ(x, R₁) ≤ C₃R₁^{m−α}.

5. (Hölder continuity with exponent α/2 and a sup bound.) Dw is continuous on closedBall(x₀, R/2 + R₁) ⊆ B_R(x₀), and ∫_{B_ρ(x)} ‖Dw − (Dw)_{x,ρ}‖² ≤ Φ(x, ρ) ≤ C₅ρ^{m+2(α/2)} for x ∈ B_{R/2}(x₀), 0 < ρ ≤ R₁. campanato_lemmas (II) (exponent α/2, radius R/2, ρ₁ = R₁) gives ‖Dw(x) − Dw(y)‖ ≤ C₀'√C₅‖x − y‖^{α/2} for x, y ∈ B_{R/2}(x₀) with ‖x − y‖ ≤ R/16. For x ∈ B_{3R/8}(x₀), B_{R/16}(x) ⊆ B_{R/2}(x₀), so ‖Dw(x)‖ ≤ ⨍_{B_{R/16}(x)} ‖Dw(x) − Dw(z)‖dz + ⨍_{B_{R/16}(x)} ‖Dw‖ ≤ C₀'√C₅(R/16)^{α/2} + (Ψ(x, R/16)/(ω(R/16)^m))^{1/2} ≤ C₆ by step 3.

6. (Second Campanato pass.) For x ∈ B_{R/4}(x₀) and 0 < ρ ≤ R₁, B_ρ(x) ⊆ B_{3R/8}(x₀), so Ψ(x, ρ) ≤ mC₆²ωρ^m. Then (C1') gives, for 0 < r ≤ ρ ≤ R₁, Φ(x, r) ≤ A₁[(r/ρ)^{m+2} + ε₁]Φ(x, ρ) + A₁K(mC₆²ω + 1)ρ^{m+2α}, and since ε₁ ≤ ε_c and m + 2α < m + 2, campanato_lemmas (I) gives Φ(x, r) ≤ c_c((r/R₁)^{m+2α}mC₆²ωR₁^m + A₁K(mC₆²ω + 1)r^{m+2α}) ≤ C₈r^{m+2α}.

7. (Conclusion.) Dw is continuous on closedBall(x₀, R/4 + R₁) ⊆ B_R(x₀); by step 6 and campanato_lemmas (II) (exponent α, radius R/4, ρ₁ = R₁), ‖Dw(x) − Dw(y)‖ ≤ C₀''√C₈‖x − y‖^α for x, y ∈ B_{R/4}(x₀) with ‖x − y‖ ≤ R/16. If ‖x − y‖ > R/16, then by step 5 ‖Dw(x) − Dw(y)‖ ≤ 2C₆ ≤ 2C₆(16/R)^α‖x − y‖^α. Also ‖Dw‖ ≤ C₆ on B_{R/4}(x₀). Hence C := max(C₆, C₀''√C₈, 2C₆(16/R)^α) works; it depends only on m, k, α, K, R, while ε₁ depends only on m, k, α. ∎

## Key steps

1. Harmonic replacement plus harmonic decay give the comparison inequalities Φ(r) ≤ A₁[(r/ρ)^{m+2} + ε₁]Φ(ρ) + A₁K(ρ^{2α}Ψ(ρ) + ρ^{m+2α}) and Ψ(r) ≤ A₁[(r/ρ)^m + 2ε₁²]Ψ(ρ) + 2A₁K²ωρ^m.
2. Caccioppoli with test map η²w bounds Ψ(x, ρ/2) by C K²(ρ^{m−2} + ρ^m).
3. Iteration lemma: Morrey decay Ψ ≤ C r^{m−α}, then Campanato decay Φ ≤ C r^{m+α}, giving α/2-Hölder continuity and a sup bound for Dw.
4. With Dw bounded, a second Campanato iteration gives Φ ≤ C r^{m+2α}; Campanato's criterion yields the α-Hölder bound on B_{R/4}(x₀).

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
