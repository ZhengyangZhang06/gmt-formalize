# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.layers-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of 3.14: its first paragraph and (1) (chapter-06.txt lines 1030–1048), (3)–(7) (lines 1048–1105), Remark 3.15 (lines 953–1029) and Remark 2.35 (lines 606–639); the mollification Lemma Ch. 2, 2.5. These are steps 5–7 of the parent proof, for U = ℝ^{n+1}. Part A is the first step of 3.14 (R is given by an integer density); Part B is the layer decomposition and Simon's smoothing estimates (5)–(7).
Siblings used: vanish_off_support (dtc_vanish_off_support), in step A5; mollify_variation (codim1_rdo_dg_sp_mollify_variation), in step B6.
Notation: e = (e_0, …, e_n) is the standard basis (e_i = EuclideanSpace.single i 1), L = L^{n+1} = volume, H^{n+1} = μHE[n+1] and div φ = trace Dφ. For an n-covector α write α_î := α(e_{i.succAbove 0}, …, e_{i.succAbove(n−1)}), i.e. e with e_i omitted.
Hodge correspondence (Simon 3.15, 2.35). For a vector field φ let ⋆φ be the n-form (⋆φ)(x)(v_0, …, v_{n−1}) := det[φ(x), v_0, …, v_{n−1}]. For an n-form η let φ_η be the vector field with components φ_η^i := (−1)^iη(·)_î. Then:
 (S1) (⋆φ)(x)_î = (−1)^iφ^i(x) (Laplace expansion along the first column). So φ_{⋆φ} = φ and ⋆φ_η = η, since an n-covector on ℝ^{n+1} is determined by its n + 1 values α_î.
 (S2) |(⋆φ)(x)| = |φ(x)|, because the Euclidean coefficient norm of α is (Σ_iα_î²)^{1/2}.
 (S3) For a C¹ n-form η, dη(x)(e) = Σ_i(−1)^i∂_i(η(·)_î)(x) = div φ_η(x) (Mathlib extDeriv_apply).
 (S4) η is a test form iff φ_η is C^∞ with compact support.
 (S5) ∫div φ dL = 0 for C¹ compactly supported φ (fundamental theorem of calculus in each coordinate).
Part A (the density θ; Simon 3.14, first paragraph and (1); 2.35).
A1. (Representation.) R is IM, so it has an IMRep (V, θ₀, ξ):
 - V ⊆ ℝ^{n+1} is Borel;
 - θ₀ : ℝ^{n+1} → ℕ is measurable, θ₀ ≥ 1 on V, and ∫_{V∩K}θ₀ dH^{n+1} < ∞ for every compact K;
 - ξ is a.e. strongly measurable for H^{n+1}⌞V;
 - for H^{n+1}-a.e. x ∈ V there is a subspace Q with IsUnitOrientationOf (ξ(x)) Q;
 - R(ω) = ∫_Vθ₀(x)ξ(x)(ω(x)) dH^{n+1}(x) for every ω ∈ 𝒟^{n+1}(ℝ^{n+1}).
A2. (Hausdorff = Lebesgue.) H^{n+1} = L^{n+1} on ℝ^{n+1} (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume).
A3. (Orientations are ±e_0∧⋯∧e_n.) Let D be the determinant (n+1)-covector of the standard basis, D(v) := det[⟨e_i, v_j⟩]; then D(e) = 1. Every (n+1)-covector α equals α(e)·D (Mathlib AlternatingMap.eq_smul_basis_det, applied to the underlying alternating map). If IsUnitOrientationOf (ξ(x)) Q, there is an orthonormal τ : Fin (n+1) → ℝ^{n+1} with ξ(x)(α) = ±α(τ) for all α. Then τ is an orthonormal basis of ℝ^{n+1}, so D(τ) is the determinant of an orthogonal matrix, i.e. ±1 (Mathlib OrthonormalBasis.det_to_matrix_orthonormalBasis_real). Hence ξ(x)(α) = ±D(τ)α(e) = s(x)·α(e) with s(x) := ξ(x)(D) ∈ {−1, 1}, for H^{n+1}-a.e. x ∈ V.
A4. (The density θ₁; Simon's θ̃.) x ↦ ξ(x)(D) is a.e. strongly measurable for H^{n+1}⌞V (evaluation at D is continuous and linear). So there is a Borel s̃ equal to it H^{n+1}⌞V-a.e. Define
 - θ₁(x) := θ₀(x) if x ∈ V and s̃(x) > 0;
 - θ₁(x) := −θ₀(x) if x ∈ V and s̃(x) ≤ 0;
 - θ₁(x) := 0 if x ∉ V.
 θ₁ is Borel and integer valued with |θ₁| = θ₀1_V. For a.e. x ∈ V, θ₀(x)ξ(x)(ω(x)) = θ₁(x)ω(x)(e). By steps A1–A3, R(ω) = ∫θ₁(x)ω(x)(e) dL^{n+1}(x) for every ω (Simon's (1)), and ∫_K|θ₁| dL^{n+1} = ∫_{V∩K}θ₀ dH^{n+1} < ∞ for compact K.
A5. (θ₁ = 0 a.e. off spt R.) Z := ℝ^{n+1} ∖ spt R is the zero region, which is open (SimonGMT isOpen_zeroRegion; spt R = univ ∖ zeroRegion). Let a ∈ C_c^∞(ℝ^{n+1}) with tsupport a ⊆ Z, and ω_a := a·D. This is a test form with tsupport ω_a ⊆ tsupport a, which is disjoint from spt R. So R(ω_a) = 0 by vanish_off_support. On the other hand R(ω_a) = ∫θ₁a dL^{n+1} by step A4, since ω_a(x)(e) = a(x). θ₁ is locally integrable on Z, so by the fundamental lemma of the calculus of variations (Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero), θ₁ = 0 L^{n+1}-a.e. on Z.
A6. (Output.) Put θ := θ₁·1_{spt R}. spt R is closed, hence Borel, so θ is Borel and integer valued, and θ(x) = 0 for x ∉ spt R. |θ| ≤ |θ₁| gives local integrability. θ = θ₁ a.e. by step A5, so R(ω) = ∫θ(x)ω(x)(e) dL^{n+1}(x) for every ω ∈ 𝒟^{n+1}(ℝ^{n+1}).
Part B (layers and truncation bounds; Simon 3.14 (3)–(7), 3.15).
B1. (Density.) Part A gives a Borel θ : ℝ^{n+1} → ℤ, locally integrable, with θ = 0 off spt R and R(ω) = ∫θω(e) dL for every ω. As spt R is compact, θ is integrable and has compact support.
B2. (Layers.) U_j := {θ ≥ j} (j ∈ ℤ) is Borel with U_{j+1} ⊆ U_j; let V_j := ℝ^{n+1} ∖ U_j. For an integer t, #{j ≥ 1 : t ≥ j} = t⁺ and #{j ≤ 0 : t < j} = t⁻. So Σ_{j≥1}1_{U_j} = θ⁺ and Σ_{j≤0}1_{V_j} = θ⁻ pointwise, and θ = Σ_{j≥1}1_{U_j} − Σ_{j≤0}1_{V_j} (Simon, before (3)).
B3. (Currents X_j = [[U_j]].) X_j(ω) := ∫_{U_j}ω(x)(e) dL is linear in ω. It is sequentially continuous on 𝒟^{n+1}(ℝ^{n+1}): a sequence converging to 0 in 𝒟 has supports in one compact K and converges uniformly, and |X_j(ω)| ≤ L(K)·sup|ω(·)(e)|. So X_j ∈ 𝒟_{n+1}(ℝ^{n+1}).
B4. (Series; Simon (3)–(4).) Fix η ∈ 𝒟^n and let g := dη(·)(e) = div φ_η (S3), continuous with compact support.
 (a) ∂X_j(η) = X_j(dη) = ∫_{U_j}g. For j ≤ 0, ∫_{U_j}g = ∫g − ∫_{V_j}g = −∫_{V_j}g by (S5).
 (b) Hence Σ_j|∂X_j(η)| ≤ Σ_{j≥1}∫1_{U_j}|g| + Σ_{j≤0}∫1_{V_j}|g| = ∫|θ||g| < ∞, by monotone convergence and step B2.
 (c) By dominated convergence for series (Mathlib integral_tsum, with dominating function |θ||g|), the sum is ∫(Σ_{j≥1}1_{U_j} − Σ_{j≤0}1_{V_j})g = ∫θg = R(dη) = ∂R(η). In ℝ, absolute summability gives HasSum. This is (i).
B5. (Variation bound; 3.15/2.35.) Let Λ := M(∂R). If Λ = ∞, (ii) and (iii) are trivial, so assume Λ < ∞.
 (a) Smooth fields. For a C^∞ compactly supported φ with |φ| ≤ 1, ⋆φ is a test form with |⋆φ(x)| ≤ 1 (S2, S4), and ∂R(⋆φ) = R(d⋆φ) = ∫θ div φ (S1, S3). So ∫θ div φ ≤ Λ, and with −φ, |∫θ div φ| ≤ Λ.
 (b) C¹ fields. Let g be C¹ and compactly supported with |g| ≤ 1. The mollifications g_δ := ρ_δ*g (ρ_δ as in step B6) are C^∞, supported in a fixed compact set, satisfy |g_δ| ≤ 1, and div g_δ = ρ_δ*div g → div g uniformly. As θ is integrable, |∫θ div g| = lim_δ|∫θ div g_δ| ≤ Λ.
B6. (Mollification; Ch. 2, 2.5.) Fix ρ ∈ C_c^∞(ℝ^{n+1}) with ρ ≥ 0, ρ(−x) = ρ(x) and ∫ρ = 1, and put ρ_σ(x) := σ^{−(n+1)}ρ(x/σ) (σ > 0). Each ρ_σ is C¹, compactly supported, nonnegative, even and has integral 1. θ_σ := ρ_σ*θ is C^∞ with compact support, and θ_σ → θ in L¹ as σ ↓ 0. By mollify_variation (u := θ, M := Λ, η := ρ_σ; its hypotheses hold by steps B1 and B5), ∫|Dθ_σ| dL ≤ Λ for every σ > 0.
B7. (Smoothed layers; Simon (5)–(6).)
 (a) The function Ψ. Let ε ∈ (0, 1/8] and integers a ≤ b. Choose ψ ∈ C^∞(ℝ), nondecreasing, with ψ = 0 on (−∞, −1 + ε], ψ = 1 on [−ε, ∞) and 0 ≤ ψ' ≤ 1 + 3ε. To build it, integrate a C^∞ function β ≥ 0 supported in [−1 + ε, −ε] with ∫β = 1 and max β ≤ 1 + 3ε; this is possible since the interval has length 1 − 2ε and (1 − 2ε)(1 + 3ε) > 1. Put Ψ(t) := Σ_{j=a}^{b}ψ(t − j).
 (b) Properties. For integer t, ψ(t − j) = 1 if t ≥ j and 0 if t ≤ j − 1, so Ψ∘θ = Σ_{j=a}^{b}1_{U_j}. The supports of ψ'(· − j) lie in the pairwise disjoint intervals [j − 1 + ε, j − ε], so 0 ≤ Ψ' ≤ 1 + 3ε and Ψ is (1 + 3ε)-Lipschitz.
 (c) Integration by parts. Let φ be C^∞ with compact support and |φ| ≤ 1. Since θ_σ has compact support, u_σ := Ψ(θ_σ) − Ψ(0) is C^∞ with compact support. By (S5) and div(u_σφ) = Du_σ(φ) + u_σ div φ, ∫Ψ(θ_σ)div φ = ∫u_σ div φ = −∫Ψ'(θ_σ)Dθ_σ(φ) ≤ (1 + 3ε)∫|Dθ_σ| ≤ (1 + 3ε)Λ.
 (d) Limit. |Ψ(θ_σ) − Ψ(θ)| ≤ (1 + 3ε)|θ_σ − θ| → 0 in L¹, and div φ is bounded. So ∫(Σ_{j=a}^{b}1_{U_j})div φ = ∫Ψ(θ)div φ = lim_σ∫Ψ(θ_σ)div φ ≤ (1 + 3ε)Λ. Letting ε ↓ 0, ∫(Σ_{j=a}^{b}1_{U_j})div φ ≤ Λ.
B8. (Masses; Simon (7).) Let a ≤ b be integers and Y ∈ 𝒟_n(ℝ^{n+1}) with Y(η) = Σ_{j=a}^{b}∂X_j(η) for all η. Let η be admissible (|η(x)| ≤ 1 for all x). By step B4(a), Y(η) = Σ_{j=a}^{b}∫_{U_j}div φ_η = ∫(Σ_{j=a}^{b}1_{U_j})div φ_η. This is ≤ Λ by step B7, because φ_η is C^∞, compactly supported and |φ_η| = |η| ≤ 1 (S2, S4). Hence M(Y) = sup ofReal(Y(η)) ≤ Λ. Taking a = b = j and Y = ∂X_j gives (ii); taking a = −N, b = N gives (iii). ∎

## Key steps

1. An IMRep (V, θ₀, ξ) of R has ξ(x) = ±(orthonormal basis of ℝ^{n+1}), hence ξ(x)(α) = s(x)α(e₀,…,e_n) with s = ±1, because top-degree covectors are multiples of det.
2. With H^{n+1} = L^{n+1}, θ₁ := s·θ₀·1_V is Borel, integer valued and locally integrable, and R(ω) = ∫θ₁ω(e).
3. Off spt R, R kills a·det for a ∈ C_c^∞ (vanish_off_support), so θ = 0 a.e. there and θ := θ₁·1_{spt R} is an integrable integer density with compact support representing R.
4. U_j := {θ ≥ j} are nested Borel sets and θ = Σ_{j≥1}1_{U_j} − Σ_{j≤0}1_{V_j}.
5. ∂X_j(η) = ∫_{U_j} div φ_η (Hodge correspondence), and Σ_j |∂X_j(η)| ≤ ∫|θ||div φ_η|, so the series converges to ∫θ div φ_η = ∂R(η).
6. M(∂R) bounds |∫θ div g| for C¹ fields |g| ≤ 1, and mollify_variation gives ∫|D(ρ_σ*θ)| ≤ M(∂R).
7. Simon's ψ_j smoothing: Ψ = Σ_{j=a}^b ψ(· − j) is (1+3ε)-Lipschitz with Ψ∘θ = Σ_{j=a}^b 1_{U_j}, so ∫(Σ 1_{U_j}) div φ ≤ (1+3ε)M(∂R).
8. Hence every partial sum Σ_{j=a}^b ∂X_j, and in particular each ∂X_j, has mass ≤ M(∂R).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); sha256sum snapshot project/GMT/Ch07/Contract.lean vs workspace GMT/Ch07/Contract.lean (both e4148e7f…)`
- `rg -n 'BoundaryRectifiability|FedererFleming|CompactnessTheorem|DeGiorgi|IsoperimetricTheorem|RectifiabilityTheorem' project/GMT -g '*.lean' (only sorry-based contract definitions in GMT/Ch06 and GMT/Ch08, namespaces GMT.Ch06/GMT.Ch08, not importable from GMT.Ch07); rg -n 'closure|De Giorgi|reduced boundary|slice' project/GMT/Ch07 (only topological closure in definitions; no closure, slicing or De Giorgi theorem)`
- `sed -n 321,345p project/GMT/Ch06/Contract.lean (BoundaryRectifiability, FlatConvergenceIffWeakConvergence, RectifiabilityTheorem: formulation reference only)`
- `rg in snapshot mathlib: 'theorem ae_tendsto_average ' (Covering/Differentiation.lean:855), 'theorem ae_tendsto_rnDeriv' (Differentiation.lean:657), 'lintegral_pow_le_pow_lintegral_fderiv' (FunctionalSpaces/SobolevInequality.lean:371), 'ae_eq_zero_of_integral_contDiff_smul_eq_zero' (Distribution/AEEqOfIntegralContDiff.lean:186), 'euclideanHausdorffMeasure_eq_volume' (Geometry/Euclidean/Volume/Measure.lean:187), 'theorem integral_tsum' (Integral/DominatedConvergence.lean:88), 'exists_disjoint_subfamily_covering_enlargement_closedBall' (Covering/Vitali.lean:158), 'theorem exists_dense_seq' (Topology/Bases.lean:364), 'tendsto_inv_nat_nhds_zero' (Topology/Instances/ENNReal/Lemmas.lean:486)`
- `grep declarations in .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,FormSupNorm,Forms}.lean and Chapter03/Rectifiable.lean: GeometricCurrentOn, TestFormOn, boundary_apply, boundary_boundary, exteriorDerivative_sq, massAdmissibleOn, massOn, mass, le_massOn, massOn_le_liminf, covectorEuclideanNorm (no smul/bound lemma), testFormEuclideanSupNorm, HasApproximateTangentSpaceAt (blow-up integral definition); no closure, slicing, isoperimetric, De Giorgi or boundary-rectifiability theorem`
- `python3 -I scans of dag.json (1615 nodes): accepted codim1_rdo_dg_* De Giorgi helpers (measure_eq_hausdorff, rectifiable_of_flat_tangent, flat_tangent_density_cone, normal_average_ae, cutoff_estimates, gauss_green_measure, ...) and codim1_rdo_rectifiable_ae_density_one; non-accepted codim1_rdo_de_giorgi_gauss_green, tangent_measure_ae, blowup_halfspace, volume_density_lower, cmc_closure_and_boundary_rectifiability with cbr_* children, dtc_bc_tc_closure, cmc_deformation_theorem; accepted cbr_isoperimetric_filling (conditional on cmc_deformation_theorem); statement of the deformation sibling dtc_bc_lc_fd_deformation; collision check of dtc_bc_lc_fd_bim_* (only in this node's decomposition-v1.json)`
- `cat nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json} (rejected v1 and its required changes)`
- `python3 -I /tmp/bim_v2_scripts/reuse_check.py: git show <commit>:GMT/Ch07/Submission.lean for 3632b24, be5e512, 44ef61f, cfaa429, 8380287, 2af75d6, d1641e8, 3450f10 (whitespace-normalised types identical to dag.json; only sorry = main_theorem; no axiom/opaque); git show <commit>:GMT/Ch07/Contract.lean | sha256sum (all e4148e7f…); comparator-v1.log and isolated-comparator-result.json of the two new reuses ('Your solution is okay!', passed)`
- `git show 3632b24 / be5e512 :GMT/Ch07/Submission.lean | grep helpers cited by the reused proofs (codim1_rdo_dg_flat_tangent_density_cone, codim1_rdo_dg_rectifiable_of_flat_tangent; regcomp_atl_upper_density_zero, rsd_tendsto_closedBall_density_of_approxTangent, rsd_tendsto_ball_density_of_closedBall): all present and accepted; git log --all -S 'dtc_bc_lc_fd_bim_' (no hit)`
- `lake env lean /tmp/bim_v2_check/Challenges.lean (12 targets in comparator challenge form after the gmt-compare.py contract_scope replay: exit 0, 12 sorry warnings only)`
- `lake env lean /tmp/bim_v2_check/AllChecks.lean (stubs; sorry-free bim_* helper lemmas; node_assembly; de_giorgi_from_children; closure_cycles_from_general; #print axioms)`
- `sed book/chapter-06.txt lines 440-660 (2.23-2.37), 725-960 (3.1-3.15), 1150-1420 (4.1-4.11), 1425-1500 (5.1-5.4), 1925-2160 (6.1-8.1), 2160-2296 (8.1 proof), 2290-2473 (8.2-8.3); chapter-01.txt 596-612, 800-830, 1745-1800 (3.3, 3.12, 4.16); chapter-03.txt 551-746 (4.1-4.3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-8e4c089bcc/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4abe9c6216/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-4abe9c6216/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96d3c5f21c/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/bim_v2_check/Challenges.lean`
- `/tmp/bim_v2_check/AllChecks.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) matches the workspace, and the snapshot and workspace GMT/Ch07/Contract.lean are byte-identical (sha256 e4148e7f…). The pinned project proves no closure, slicing, isoperimetric, De Giorgi or boundary-rectifiability theorem usable from GMT.Ch07. GMT/Ch06 and GMT/Ch08 only state them as sorry-based contract definitions in other namespaces; they served as formulation references. SimonGMT provides currents, boundary, massOn/mass (Euclidean coefficient norm), le_massOn, massOn_le_liminf, support and HasApproximateTangentSpaceAt, but no bound for covectorEuclideanNorm; the needed homogeneity and operator-norm bounds were proved in the scratch check. Snapshot Mathlib supplies the measure-theory tools cited in the child proofs (Besicovitch/Vitali differentiation, GNS inequality, fundamental lemma, μHE = volume, integral_tsum, separability). In the DAG, the De Giorgi parent codim1_rdo_de_giorgi_gauss_green and the closure theorems are not accepted. The accepted codim1_rdo_dg_measure_eq_hausdorff and codim1_rdo_rectifiable_ae_density_one close the rejected de_giorgi step 6: types identical in commits 3632b24 and be5e512, comparators passed, helpers contained. They are reused together with the six v1 reuses. All eight reused types are identical in their accepted commits, those commits' contracts are byte-identical, and they contain no extra sorry or axioms. The four new names are unreserved and the dependencies are acyclic. Lean: all 12 child types elaborate in challenge form. The parent's frozen type is proved from the 12 child stubs plus the deformation sibling, with the inline weak-limit step proved sorry-free (propext, Classical.choice, Quot.sound). de_giorgi's type is assembled from the three reused De Giorgi lemmas, and closure_cycles follows from the cousin dtc_bc_tc_closure's type.
