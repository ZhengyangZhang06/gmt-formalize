# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.nested_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of 3.14, (8)–(9) and its final paragraph (chapter-06.txt lines 1105–1132). Also Remark 3.15 (∂[[A]] = τ(∂*A, 1, ⋆ν_A); lines 1000–1029) and Ch. 3, 4.3(‡) for the normals of nested sets: 'By virtue of the fact that U_{j+1} ⊂ U_j we see from 4.3(‡) of Ch. 3 that ν_j ≡ ν_k on ∂*U_j ∩ ∂*U_k'. These are steps 8–9 of the parent proof.
Siblings used: de_giorgi; normal_orientation (codim1_lur_normal_covector_orientation); im_calculus (cmc_imRep_locality_restrict_sub, parts (a) and (d)); oriented_mass_lower (codim1_oriented_rep_lintegral_le_massOn).
Notation:
- The Hodge correspondence (S1)–(S5) is as in the sibling layers: α_î := α(e_{i.succAbove 0}, …, e_{i.succAbove(n−1)}), (⋆φ)(x)(v) := det[φ(x), v], φ_η^i := (−1)^iη(·)_î, (⋆φ)_î = (−1)^iφ^i, |⋆φ| = |φ|, dη(·)(e) = div φ_η, and ∫div φ = 0.
- For an n-covector α let φ_α := Σ_i(−1)^iα_îe_i, so that φ_η(x) = φ_{η(x)}.
- For v ∈ ℝ^{n+1} let ξ_v be the n-vector ξ_v(α) := −⟨φ_α, v⟩ = −Σ_i(−1)^iα_î⟨e_i, v⟩. It is continuous and linear in α, and linear in v.
- L = volume, H^n = μHE[n], ‖η‖ := sup_x|η(x)|.
1. (Finite perimeter.) Fix j. For a C^∞ compactly supported φ with |φ| ≤ 1, ⋆φ is a test form with |⋆φ(x)| ≤ 1. So ∂X_j(⋆φ) ≤ M(∂X_j) =: C_j < ∞, and ∂X_j(⋆φ) = X_j(d⋆φ) = ∫_{U_j}div φ dL by (S1), (S3). Hence ∫_{U_j}div φ ≤ C_j.
2. (De Giorgi.) de_giorgi (n ≥ 1, E := U_j Borel, C := C_j) gives B_j and ν_j:
 - B_j is Borel and countably n-rectifiable with H^n(B_j) < ∞;
 - ν_j is Borel with |ν_j| = 1 on B_j;
 - B_j has approximate tangent space (span{ν_j(y)})^⊥ at H^n-a.e. y ∈ B_j;
 - ∫_{U_j}div φ = −∫_{B_j}⟨φ, ν_j⟩dH^n for C¹ compactly supported φ;
 - (‡): for H^n-a.e. y ∈ B_j and every ρ, L(((U_j)_{y,r} Δ {⟨w, ν_j(y)⟩ > 0}) ∩ B_ρ(0)) → 0 as r ↓ 0.
3. (∂X_j as a rectifiable current; 3.15.) For η ∈ 𝒟^n, ∂X_j(η) = X_j(dη) = ∫_{U_j}div φ_η = −∫_{B_j}⟨φ_η, ν_j⟩dH^n = ∫_{B_j}ξ_{ν_j(x)}(η(x)) dH^n(x). For |v| = 1, normal_orientation gives an orthonormal family σ_v with span (span{v})^⊥ and α(σ_v) = −⟨φ_α, v⟩ = ξ_v(α) for every α. So IsUnitOrientationOf ξ_v (span{v})^⊥, with the + sign.
4. (Compatibility of normals; 3.14 with 4.3(‡).) Let j < k, so U_k ⊆ U_j. Let y ∈ B_j ∩ B_k be a point where (‡) holds for both (U_j, ν_j) and (U_k, ν_k); H^n-a.e. point of B_j ∩ B_k is such. Put H_i := {w : ⟨w, ν_i(y)⟩ > 0} for i ∈ {j, k}.
 (a) Since (U_k)_{y,r} ⊆ (U_j)_{y,r}, L((H_k ∖ H_j) ∩ B_1) ≤ L((H_k Δ (U_k)_{y,r}) ∩ B_1) + L(((U_j)_{y,r} Δ H_j) ∩ B_1) → 0. So L((H_k ∖ H_j) ∩ B_1) = 0.
 (b) Suppose ν_k(y) ≠ ν_j(y). Then w₀ := (ν_k(y) − ν_j(y))/4 satisfies ⟨w₀, ν_k(y)⟩ > 0 > ⟨w₀, ν_j(y)⟩ and |w₀| ≤ 1/2. So a small ball around w₀ lies in (H_k ∖ H_j) ∩ B_1, contradicting (a).
 Hence ν_j = ν_k H^n-a.e. on B_j ∩ B_k.
5. (Common normal and orientation.) Fix a bijection κ : ℕ → ℤ and let B := ⋃_jB_j (Borel).
 (a) For x ∈ B let i(x) := min{i : x ∈ B_{κ(i)}} and ν(x) := ν_{κ(i(x))}(x); for x ∉ B let ν(x) := e_0. Then ν is Borel and |ν| = 1 on B.
 (b) By step 4 (countably many pairs), ν = ν_j H^n-a.e. on B_j for every j.
 (c) Put ξ(x) := ξ_{ν(x)}, a Borel map. By step 3, ∂X_j(η) = ∫_{B_j}ξ(x)(η(x)) dH^n(x) for all j and η, and IsUnitOrientationOf (ξ(x)) (span{ν(x)})^⊥ for every x ∈ B.
6. (Mass bound; Simon (7)–(8).) Fix N ∈ ℕ, J := {−N, …, N}, h_N := Σ_{j∈J}1_{B_j} and M_N := ⋃_{j∈J}B_j.
 (a) Y_N(η) := Σ_{j∈J}∂X_j(η) is a current (a finite sum of currents), so M(Y_N) ≤ C by hypothesis. By step 5, Y_N(η) = ∫_{M_N}h_N(x)ξ(x)(η(x)) dH^n(x).
 (b) Apply oriented_mass_lower with U = V = W := ℝ^{n+1}, M' := M_N, θ' := h_N (Borel, ≥ 0) and ξ' := ξ (Borel, a unit orientation at every point of M_N). Since I := ∫_{M_N}h_N dH^n = Σ_{j∈J}H^n(B_j) < ∞, it gives I ≤ M(Y_N) ≤ C.
 (c) Letting N → ∞, Σ_{j∈ℤ}H^n(B_j) ≤ C < ∞.
7. (Multiplicity.) h := Σ_{j∈ℤ}1_{B_j} : ℝ^{n+1} → [0, ∞] is Borel with ∫h dH^n = Σ_jH^n(B_j) ≤ C, so h < ∞ H^n-a.e. Let M := {x ∈ B : h(x) < ∞}, a Borel set with H^n(B ∖ M) = 0. Put θ(x) := h(x) ∈ ℕ for x ∈ M and θ(x) := 0 otherwise. Then θ is Borel, θ ≥ 1 on M, and ∫_{M∩K}θ dH^n ≤ C for every K.
8. (Rectifiability and tangent planes.)
 (a) M ⊆ ⋃_jB_j is countably n-rectifiable: use countable unions (SimonGMT countablyRectifiable_iUnion, indexed via κ) and subsets. Also H^n(M) ≤ Σ_jH^n(B_j) < ∞.
 (b) For each j, apply im_calculus (a) with U = ℝ^{n+1} to the Borel pairs B_j ∩ M ⊆ M and B_j ∩ M ⊆ B_j; the larger sets have finite H^n-measure. For H^n-a.e. x ∈ B_j ∩ M and every subspace Q: M has approximate tangent space Q at x ⟺ B_j ∩ M does ⟺ B_j does.
 (c) By step 2 and ν = ν_j a.e. on B_j, for H^n-a.e. x ∈ B_j ∩ M, M has approximate tangent space (span{ν(x)})^⊥ at x, and ξ(x) is a unit orientation of it (step 5). As M = ⋃_j(B_j ∩ M), this holds for H^n-a.e. x ∈ M.
9. (IMRep.) By steps 7–8, (M, θ, ξ) is an IMRep in ℝ^{n+1} of degree n:
 - M is Borel, contained in ℝ^{n+1}, and countably n-rectifiable;
 - θ is measurable, positive on M and locally integrable;
 - ξ is Borel, hence a.e. strongly measurable;
 - for H^n-a.e. x ∈ M, Q := (span{ν(x)})^⊥ satisfies HasApproximateTangentSpaceAt n M x Q and IsUnitOrientationOf (ξ x) Q.
 By im_calculus (d), |ξ(x)(α)| ≤ |α| for H^n-a.e. x ∈ M and every α.
10. (It represents T.) Fix η ∈ 𝒟^n. By hypothesis T(η) = Σ_{j∈ℤ}∂X_j(η) (HasSum), and ∂X_j(η) = ∫1_{B_j}ξ(η)dH^n by step 5.
 (a) Domination. H^n(B_j ∖ M) = 0 and |ξ(x)(η(x))| ≤ ‖η‖ for a.e. x ∈ M (step 9). So Σ_j∫|1_{B_j}ξ(η)|dH^n ≤ ‖η‖Σ_jH^n(B_j) < ∞.
 (b) By dominated convergence for series (Mathlib integral_tsum), Σ_j∫_{B_j}ξ(η)dH^n = ∫hξ(η)dH^n = ∫_Mθξ(η)dH^n, because h = θ on M, H^n(B ∖ M) = 0 and h = 0 off B.
 (c) By uniqueness of sums, T(η) = ∫_Mθ(x)ξ(x)(η(x)) dH^n(x) = (M, θ, ξ).action(η).
 Hence T is integer multiplicity. ∎

## Key steps

1. M(∂X_j) < ∞ means U_j has finite perimeter (Hodge correspondence), so de_giorgi gives B_j, ν_j with Gauss–Green, tangent planes ν_j^⊥ and half-space blow-ups.
2. ∂X_j(η) = ∫_{B_j} ξ_{ν_j}(η) dH^n with ξ_ν(α) = −⟨φ_α, ν⟩, which normal_orientation identifies as a unit orientation of ν^⊥ (Simon 3.15).
3. Nested sets have nested half-space blow-ups, so ν_j = ν_k a.e. on B_j ∩ B_k; one Borel normal ν and orientation ξ serve all j.
4. oriented_mass_lower gives Σ_{|j|≤N} H^n(B_j) ≤ M(Σ_{|j|≤N} ∂X_j) ≤ C, so h := Σ_j 1_{B_j} is integrable.
5. (⋃B_j ∩ {h<∞}, h, ξ) is an IMRep (rectifiable union; tangent planes by im_calculus (a)), and dominated convergence for the series shows it represents T.

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
