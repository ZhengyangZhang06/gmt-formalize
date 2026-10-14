# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 (normalization), step 2 (B1, parametrization), step 3 (B2, B2′: tangent planes and sign of the pieces) of the supplied proof, and the area-formula representation X(η) = Σ_i ∫_{A_i} θ_i s_i η(G_i)(DG_i e) used in its steps 4 and 7. This is Simon Ch. 6, 3.3–3.5: the decomposition of T = τ(M, θ, ξ) into Lipschitz pieces and the identity d f_# ξ = ±J ξ̃.

Hypotheses as named in the statement:
- (CB) is the frozen type of cmcdt_lp_covector_norm_bounds; its third conjunct (L3) says |α(τ)| ≤ |α| for orthonormal τ.
- (VO), (MR), (IMC) are the frozen types of dtc_vanish_off_support, cmc_massOn_eq_imRep_measure and cmc_imRep_locality_restrict_sub.

Notation:
- n := k + 1; Hⁿ := μHE[n]; λ := volume on ℝⁿ = Euclid n.
- e_a := EuclideanSpace.single a 1 (a ∈ Fin n), the standard basis of ℝⁿ; |α| := covectorEuclideanNorm α.
- For G : ℝⁿ → ℝ^N and u ∈ ℝⁿ: DG(u) := fderiv ℝ G u; v^G(u) := (DG(u)e_a)_{a ∈ Fin n}; J_G(u) := √det(⟨DG(u)e_a, DG(u)e_b⟩)_{a,b} ≥ 0. This is exactly the Jacobian in the siblings area_lintegral and area_integral.
- ev_z is the evaluation functional α ↦ α(z) on n-covectors. It is continuous linear, and z ↦ ev_z is continuous.
- For a test form η, ‖η‖_∞ := sup_x |η(x)| < ∞, since η is continuous with compact support and α ↦ |α| is continuous.

1. (Normalization.) Let R be an IMRep representing X, with carrier M₀, multiplicity θ and orientation ξ. spt X is closed, hence Borel. (IMC)(b) with U := ℝ^N and E := spt X gives a current A and an IMRep R' representing A, with carrier M := M₀ ∩ spt X, multiplicity θ and orientation ξ.
   Put W := ℝ^N ∖ spt X; it is open. Every ω admissible for massOn W (tsupport ω ⊆ W, |ω(x)| ≤ 1) has tsupport disjoint from spt X, so X(ω) = 0 by (VO). Hence X.massOn W = sSup{ofReal 0} = 0.
   By (MR) for (X, R): 0 = X.massOn W = R.measure W = ∫⁻_{M₀ ∩ W} θ dHⁿ. Since θ ≥ 1 on M₀, Hⁿ(M₀ ∖ spt X) = Hⁿ(M₀ ∩ W) = 0.
   Therefore Hⁿ⌞M = Hⁿ⌞M₀, and for every test form η, R'.action(η) = ∫_M θ ξ(η) dHⁿ = ∫_{M₀} θ ξ(η) dHⁿ = R.action(η) = X(η). So R' represents X. Consequences:
   (a) By (MR) for (X, R') with W := ℝ^N: X.mass = X.massOn ℝ^N = R'.measure(ℝ^N) = ∫⁻_M θ dHⁿ < ∞.
   (b) Hⁿ(M) ≤ ∫⁻_M θ dHⁿ < ∞, because θ ≥ 1 on M.
   (c) By (IMC)(d) for R': for Hⁿ-a.e. x ∈ M, |ξ(x)(α)| ≤ |α| for every α.
   (d) M ⊆ spt X. By the IMRep fields of R', M is Borel and countably n-rectifiable, and for Hⁿ-a.e. x ∈ M there is Q_x with HasApproximateTangentSpaceAt n M x Q_x and IsUnitOrientationOf (ξ x) Q_x.
2. (Pieces, B1.) Apply the sibling bilipschitz_pieces (dpf_rectifiable_bilipschitz_pieces, with P := N) to the Borel, countably n-rectifiable set M. It gives, for i ∈ ℕ, maps G_i : ℝⁿ → ℝ^N with Lipschitz constants L_i, Borel sets A_i ⊆ ℝⁿ and numbers m_i > 0 such that:
   - m_i|u − u'| ≤ |G_i(u) − G_i(u')| for u, u' ∈ A_i;
   - G_i is differentiable at every u ∈ A_i, with DG_i(u) injective;
   - the sets G_i(A_i) are Borel, contained in M and pairwise disjoint;
   - Hⁿ(M ∖ ⋃_i G_i(A_i)) = 0.
   This gives the Lipschitz, Borel and differentiability conclusions, and G_i(A_i) ⊆ M ⊆ spt X. G_i is injective on A_i.
3. (Null sets pull back.) Fix i. For every E ⊆ A_i, λ(E) ≤ m_i^{-n}·Hⁿ(G_i(E)). Indeed, the inverse of G_i on G_i(E) is m_i^{-1}-Lipschitz. Lipschitz maps multiply Hⁿ by at most the n-th power of their constant (Mathlib LipschitzOnWith.hausdorffMeasure_image_le; μHE[n] is a constant multiple of μH[n]). And Hⁿ = λ on ℝⁿ (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). [Optional, not used: if this node is decomposed further, this bound is the lower bound in the accepted theorem dimred_rpd_bilipschitz_image_measure, which can then be reused as a child with its identical frozen type.]
   Consequently, if a property p holds for Hⁿ⌞M-a.e. x, then p(G_i(u)) holds for λ-a.e. u ∈ A_i. To see this, apply the bound to E := A_i ∩ G_i^{-1}(Z), where Z is the exceptional set: Hⁿ(Z ∩ M) = 0 and G_i(E) ⊆ Z ∩ M. The same holds for Hⁿ⌞G_i(A_i)-a.e. properties.
4. (Tangent planes, B2.) Fix i. The sibling piece_tangent (ptd_piece_image_approxTangent_ae with F := G_i, B := A_i, L := L_i, m := m_i) gives: for λ-a.e. u ∈ A_i, G_i(A_i) has approximate tangent space range DG_i(u) at G_i(u).
   Apply (IMC)(a) with U := ℝ^N, the Borel sets G_i(A_i) ⊆ M, and the bound Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞. For Hⁿ⌞G_i(A_i)-a.e. x and every Q, HasApproximateTangentSpaceAt n (G_i(A_i)) x Q ⟺ HasApproximateTangentSpaceAt n M x Q.
   By step 3, this equivalence, the orientation property 1(d) and the bound 1(c) hold at x = G_i(u) for λ-a.e. u ∈ A_i. Let A_i^g be the set of u ∈ A_i at which these three statements and the piece_tangent statement all hold; λ(A_i ∖ A_i^g) = 0.
   Let u ∈ A_i^g and x := G_i(u). M has approximate tangent spaces range DG_i(u) and Q_x at x, so Q_x = range DG_i(u) (SimonGMT HasApproximateTangentSpaceAt.unique). Since e is a basis of ℝⁿ, range DG_i(u) = span(range v^{G_i}(u)). So for u ∈ A_i^g, ξ(G_i(u)) is a unit orientation of span(range v^{G_i}(u)).
5. (Sign, B2′.) For u ∈ A_i, v^{G_i}(u) is linearly independent, since DG_i(u) is injective and e is a basis. Apply the sibling span_orientation to v^{G_i}(u). It gives J_{G_i}(u) > 0 and ξ with α(v) = J·ξ(α), i.e. ξ = J^{-1}·ev_v. So ξ_u := J_{G_i}(u)^{-1}·ev_{v^{G_i}(u)} is a unit orientation of span(range v^{G_i}(u)), and every unit orientation of that span is ξ_u or −ξ_u.
   Let ξ' : ℝ^N → Λ_n(ℝ^N) be strongly measurable with ξ' = ξ Hⁿ⌞M-a.e. (AEStronglyMeasurable.mk, from the IMRep field of R'). Define s_i(u) := 1 if ξ'(G_i(u)) = J_{G_i}(u)^{-1}·ev_{v^{G_i}(u)}, and s_i(u) := −1 otherwise.
   s_i is Borel measurable. The map u ↦ ξ'(G_i(u)) is strongly measurable. The map u ↦ J_{G_i}(u)^{-1}·ev_{v^{G_i}(u)} is Borel: u ↦ DG_i(u) is Borel (measurable_fderiv), and z ↦ ev_z and the Gram determinant are continuous. The set where two measurable maps into the finite-dimensional normed space Λ_n(ℝ^N) agree is measurable.
   By step 3, ξ'(G_i(u)) = ξ(G_i(u)) for λ-a.e. u ∈ A_i. For such u ∈ A_i^g, step 4 and the uniqueness part of span_orientation give ξ(G_i(u)) ∈ {ξ_u, −ξ_u}, hence ξ(G_i(u)) = s_i(u)·ξ_u. That is:
   (★) J_{G_i}(u)·ξ(G_i(u))(α) = s_i(u)·α(v^{G_i}(u)) for every n-covector α, for λ-a.e. u ∈ A_i.
6. (Weights.) Define w_i(u) := θ(G_i(u))·s_i(u) ∈ ℤ and c_i(u) := J_{G_i}(u). w_i is measurable, because θ is Borel and ℕ-valued, G_i is continuous and s_i is Borel. Moreover |w_i(u)| = θ(G_i(u)) for every u. c_i is Borel measurable: this is part (i) of the sibling area_lintegral (codim1_lura_gram_area_formula with f := G_i), whose Jacobian is exactly J_{G_i}. (Alternatively: u ↦ DG_i(u) is Borel by measurable_fderiv, and the Gram determinant and the square root are continuous.)
7. (Pointwise bound.) Let u ∈ A_i and let α be an n-covector. c_i(u) ≥ 0. By span_orientation, α(v^{G_i}(u)) = J_{G_i}(u)·ξ_u(α), and ξ_u is a unit orientation: ξ_u(α) = ±α(τ) for an orthonormal τ. So |ξ_u(α)| ≤ |α| by (L3). Hence |α(DG_i(u)e_0, …, DG_i(u)e_{n−1})| ≤ c_i(u)·|α|.
8. (Area formulas.) For each i: A_i is Borel; G_i is differentiable with injective derivative at every point of A_i; and G_i is injective on A_i.
   - The sibling area_lintegral (codim1_lura_gram_area_formula with m := n, P := N, f := G_i, s := A_i) gives ∫⁻_{G_i(A_i)} g dHⁿ = ∫⁻_{A_i} ofReal(J_{G_i}(u))·g(G_i(u)) dλ(u) for every g ≥ 0.
   - The sibling area_integral (codim1_lur_cd_injective_area_formula_gram with G := G_i, F := A_i) gives ∫_{G_i(A_i)} h dHⁿ = ∫_{A_i} J_{G_i}(u)·h(G_i(u)) dλ(u) for every h : ℝ^N → ℝ.
9. (Mass bound.) By step 6 and step 8 with g := θ: ∫⁻_{A_i} ofReal(|w_i|·c_i) dλ = ∫⁻_{A_i} ofReal(J_{G_i})·θ∘G_i dλ = ∫⁻_{G_i(A_i)} θ dHⁿ. The G_i(A_i) are pairwise disjoint Borel subsets of M. Hence Σ_i ∫⁻_{G_i(A_i)} θ dHⁿ = ∫⁻_{⋃_i G_i(A_i)} θ dHⁿ ≤ ∫⁻_M θ dHⁿ = X.mass (lintegral_iUnion, monotonicity, 1(a)).
10. (Integrability.) By step 3, for Borel B ⊆ ℝ^N, λ(A_i ∩ G_i^{-1}(B)) ≤ m_i^{-n}·Hⁿ(G_i(A_i) ∩ B). So the image of λ⌞A_i under G_i is at most m_i^{-n}·Hⁿ⌞G_i(A_i) as measures. Using lintegral_map (θ is Borel, G_i continuous) and step 9:
    ∫⁻_{A_i} |w_i| dλ = ∫⁻_{A_i} θ∘G_i dλ = ∫⁻ θ d(G_i)_*(λ⌞A_i) ≤ m_i^{-n}·∫⁻_{G_i(A_i)} θ dHⁿ ≤ m_i^{-n}·X.mass < ∞.
    As w_i is measurable, u ↦ (w_i(u) : ℝ) is integrable on A_i.
11. (Representation.) Let η be a test form and f(x) := θ(x)·ξ(x)(η(x)).
    - f is a.e. strongly measurable for Hⁿ⌞M. By 1(c), |f| ≤ ‖η‖_∞·θ Hⁿ⌞M-a.e., and ∫_M θ dHⁿ < ∞ by 1(a). So f is integrable on M, and X(η) = R'.action(η) = ∫_M f dHⁿ.
    - Since Hⁿ(M ∖ ⋃_i G_i(A_i)) = 0 and the G_i(A_i) ⊆ M are pairwise disjoint and Borel, ∫_M f dHⁿ = ∫_{⋃_i G_i(A_i)} f dHⁿ. Mathlib hasSum_integral_iUnion then gives HasSum (i ↦ ∫_{G_i(A_i)} f dHⁿ) (X(η)).
    - For each i, step 8 (area_integral with h := f) gives ∫_{G_i(A_i)} f dHⁿ = ∫_{A_i} J_{G_i}(u)·θ(G_i(u))·ξ(G_i(u))(η(G_i(u))) dλ(u).
    - By (★) with α := η(G_i(u)), this integrand equals θ(G_i(u))·s_i(u)·η(G_i(u))(v^{G_i}(u)) = w_i(u)·η(G_i(u))(DG_i(u)e_0, …, DG_i(u)e_{n−1}) for λ-a.e. u ∈ A_i.
    Hence ∫_{G_i(A_i)} f dHⁿ = ∫_{A_i} w_i(u)·η(G_i(u))(DG_i(u)e) dλ(u) (setIntegral_congr_ae), and HasSum (i ↦ ∫_{A_i} w_i·η(G_i)(DG_i e) dλ) (X(η)).
12. Steps 2, 6 (including the measurability of w_i and c_i), 7, 9, 10 and 11 give every conclusion of the statement for these G_i, A_i, w_i and c_i. ∎

## Key steps

1. Normalize X = τ(M, θ, ξ) with M := M₀ ∩ spt X using (IMC)(b), (MR) and (VO): Hⁿ(M₀ ∖ spt X) = 0 and ∫_M θ = M(X).
2. bilipschitz_pieces gives Lipschitz G_i, Borel A_i and lower bounds m_i, with injective derivatives and disjoint Borel images in M covering M up to a null set.
3. Hⁿ-null subsets of G_i(A_i) pull back to λ-null subsets of A_i, because the inverse of G_i is m_i^{-1}-Lipschitz.
4. piece_tangent, (IMC)(a) and uniqueness of tangent planes show that ξ(G_i u) is a unit orientation of range DG_i(u) for a.e. u.
5. span_orientation gives J·ξ(G_i u)(α) = s_i(u)·α(DG_i(u)e), with a Borel sign s_i obtained by comparing a measurable version of ξ with J⁻¹·ev_{DG_i e}.
6. Put w_i := θ∘G_i·s_i and c_i := J_{G_i} (Borel by area_lintegral (i)); (L3) gives |α(DG_i e)| ≤ c_i|α|.
7. area_lintegral gives Σ_i ∫|w_i|c_i = Σ_i ∫_{G_i(A_i)} θ ≤ M(X); the bi-Lipschitz bound gives ∫_{A_i}|w_i| ≤ m_i^{-n}·M(X).
8. area_integral and the sign identity turn X(η) = Σ_i ∫_{G_i(A_i)} θξ(η) into Σ_i ∫_{A_i} w_i·η(G_i)(DG_i e).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp Contract.lean Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest.json)`
- `rg -n cmcdt_lpi local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g *.lean (no match)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json: statuses and lean_names; prefix cmcdt_lpi_ (no node); accepted nodes matching bilip|area|piece|tangent|orient|density|gram|pullback|jacobian (dpf_rectifiable_bilipschitz_pieces, ptd_piece_image_approxTangent_ae, codim1_lura_gram_area_formula, codim1_lur_cd_injective_area_formula_gram, cmcdt_ims_imrep_of_int_density, dimred_rpd_bilipschitz_image_measure, rsdic_unitOrientation_eq_or_eq_neg, dpf_exists_orthonormal_frame_det_gram, cmr_cc_det_covector_exists, covectorEuclideanNorm_gram_bounds); unaccepted overlap dor_lmb_fcd_jacobian_weak_continuity`
- `python3 string comparison: selected frozen type split at top-level arrows; VO, MR, IMC, IMS blocks equal the frozen types of dtc_vanish_off_support, cmc_massOn_eq_imRep_measure, cmc_imRep_locality_restrict_sub, cmcdt_im_series; reused child types equal their DAG lean_statements`
- `grep -n in SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, countablyRectifiable_range, CountablyRectifiable.mono, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique) and Chapter06/Forms.lean, Currents.lean, Mass.lean (Covector, DifferentialForm, IsTestForm, TestFormOn, GeometricCurrentOn, GeometricCurrentOn.ext, covectorEuclideanNorm, massAdmissibleOn, massOn, mass)`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: LipschitzOnWith.hausdorffMeasure_image_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_def, measurableSet_of_differentiableAt, measurable_fderiv, LipschitzWith.ae_differentiableAt, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, MeasurableSet.image_of_continuousOn_injOn, LinearMap.exists_antilipschitzWith, AlternatingMap.map_linearDependent, hasSum_integral_iUnion, lintegral_iUnion, tendsto_tsum_of_dominated_convergence, volume_preserving_piFinSuccAbove, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, integral_lineDeriv_mul_eq, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, norm_fderiv_le_of_lipschitz, Matrix.det_succ_row_zero, AlternatingMap.eq_smul_basis_det, ContDiffAt.isSymmSndFDerivAt, Integrable.exists_hasCompactSupport_integral_sub_le, gramSchmidtNormed_orthonormal, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, Matrix.det_of_isUpperTriangular (all found; det_of_upperTriangular is a deprecated alias); Hadamard inequality for Gram determinants (no match, proved via Gram–Schmidt)`
- `sed -n 420,520p and 760,900p book/chapter-06.txt (Simon 6.2.24–2.29 and 6.3.3–3.12, the printed source of B3–B5)`
- `grep of /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py (_existing_lean_name_problem, _overlay_accepted_children, accepted-theorem reuse by Lean name) and inherited.py (ancestor-dependency citations)`
- `lake env lean /tmp/lpi/lean/Split2.lean (12 child types, CB, parent assembly; assembly_check axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/lpi/lean/Inst.lean (instance checks)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9bda5f8762/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9889d5f42e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-64a6473a66/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-db95546c3f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-dad7016689/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-74efcb8c6f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Block.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/inherited.py`
- `/tmp/lpi/lean/Split2.lean`
- `/tmp/lpi/lean/Inst.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Contract.lean and Submission.lean. It contains no proofs to reuse: no Lipschitz push-forward integrality, weak continuity of minors or piece representation, and no cmcdt_lpi_ names (no match). Five accepted DAG theorems fit the supplied proof and are reused with identical types: dpf_rectifiable_bilipschitz_pieces (B1), ptd_piece_image_approxTangent_ae (B2), codim1_lura_gram_area_formula and codim1_lur_cd_injective_area_formula_gram (area formulas), and cmcdt_ims_imrep_of_int_density (IMRep from an integer density). The controller allows reuse of an accepted theorem by Lean name under a new parent when the frozen type is identical. SimonGMT provides rectifiability, approximate tangent spaces with uniqueness, currents, mass as an sSup over admissible forms, and test forms. Mathlib provides every tool cited by the new proofs: Rademacher, the approximately-linear partition, Lusin–Souslin, antilipschitz bounds, Lipschitz bounds for Hausdorff measure, μHE = volume on ℝⁿ, Gram–Schmidt, the basis determinant, Laplace expansion, symmetric second derivatives, weak derivatives of Lipschitz functions, mollifier a.e. convergence, Tannery, countable additivity of integrals, and the Fubini splitting of volume on Euclid (n+1). There is no Hadamard inequality for Gram determinants; it is proved in span_orientation via Gram–Schmidt. All 12 child types elaborate. The parent assembly compiles with axioms propext, Classical.choice and Quot.sound.
