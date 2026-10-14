# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 (B3) of the supplied proof, stated for one Lipschitz map H with an integer weight g. Its ingredients are the bi-Lipschitz pieces A_{il}, the images N_{il} with integer densities and induced orientations η_{il}, the integer multiplicity currents Φ_{il} with their mass bound, and their combination by IMS. This is Simon Ch. 6, 3.5–3.9: f_#τ(M, θ, ξ) is integer multiplicity, with the induced orientation d f_# ξ/|d f_# ξ| on f(M_+).

Hypotheses as named in the statement:
- (CB): its third conjunct (L3) says |α(τ)| ≤ |α| for orthonormal τ.
- (IMC): only part (b) is used.
- (IMSc) is the conclusion of the frozen type of cmcdt_im_series. For every sequence W_l ∈ 𝒟_{k+1}(ℝ^{N'}) with Σ_l M(W_l) < ∞ there is S with HasSum (l ↦ W_l(ω)) (S(ω)) for every ω, M(S) ≤ Σ_l M(W_l) and spt S ⊆ closure ⋃_l spt W_l; and S is integer multiplicity if every W_l is.

Notation:
- n := k + 1; λ := volume on ℝⁿ; Hⁿ := μHE[n] on ℝ^{N'}; e_a := EuclideanSpace.single a 1; |α| := covectorEuclideanNorm α.
- DH(u) := fderiv ℝ H u (0 where H is not differentiable); v(u) := (DH(u)e_a)_{a ∈ Fin n}; J(u) := √det(⟨DH(u)e_a, DH(u)e_b⟩)_{a,b}.
- ev_z := (α ↦ α(z)) ∈ Λ_n(ℝ^{N'}); for a test form ω, Ψ_ω(u) := g(u)·ω(H(u))(v(u)).

1. (Integrability.) ‖DH(u)‖ ≤ L for all u (norm_fderiv_le_of_lipschitz), so |DH(u)e_a| ≤ L. Also |ω(y)(z)| ≤ ‖ω(y)‖·∏_a|z_a|, with C_ω := sup_y ‖ω(y)‖ < ∞ because ω is continuous with compact support. Ψ_ω is Borel: g is measurable, H continuous, u ↦ DH(u) Borel (measurable_fderiv) and evaluation continuous. Since |Ψ_ω| ≤ C_ω·Lⁿ·|g|, Ψ_ω is integrable on A.
2. (Where the integrand lives.)
   - D := {u : H is differentiable at u} is Borel (measurableSet_of_differentiableAt), and λ(ℝⁿ ∖ D) = 0 (Rademacher, LipschitzWith.ae_differentiableAt).
   - A⁺ := {u ∈ A ∩ D : DH(u) injective and g(u) ≠ 0} is Borel: DH(u) is injective iff det(⟨DH(u)e_a, DH(u)e_b⟩) ≠ 0, a Borel condition.
   - Let u ∈ (A ∩ D) ∖ A⁺. Either g(u) = 0, or DH(u) is not injective, so v(u) is linearly dependent and ω(H(u))(v(u)) = 0 (an alternating map vanishes on linearly dependent families, AlternatingMap.map_linearDependent). In both cases Ψ_ω(u) = 0.
   Hence Ψ_ω = 0 λ-a.e. on A ∖ A⁺, and ∫_A Ψ_ω dλ = ∫_{A⁺} Ψ_ω dλ. Moreover λ(A⁺) ≤ ∫⁻_A |g| dλ < ∞, since |g| ≥ 1 on A⁺.
3. (Bi-Lipschitz partition.) For a linear map T : ℝⁿ → ℝ^{N'}: if T is injective, choose κ_T > 0 with |Tw| ≥ κ_T|w| for all w (Mathlib LinearMap.exists_antilipschitzWith, κ_T := 1/K) and put r(T) := κ_T/2; otherwise put r(T) := 1. Then r(T) ≠ 0 for every T.
   Apply Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt to f := H, s := A⁺, f' := DH and this r. (At u ∈ A⁺, H is differentiable, so HasFDerivWithinAt H (DH u) A⁺ u.) It gives pairwise disjoint Borel sets t_l (l ∈ ℕ) with A⁺ ⊆ ⋃_l t_l and linear maps T_l such that |H(u) − H(u') − T_l(u − u')| ≤ r(T_l)|u − u'| for u, u' ∈ A_l := A⁺ ∩ t_l. If A⁺ ≠ ∅, then T_l = DH(y_l) for some y_l ∈ A⁺, so T_l is injective.
   Then for u, u' ∈ A_l: |H(u) − H(u')| ≥ |T_l(u − u')| − (κ_{T_l}/2)|u − u'| ≥ κ_l|u − u'|, with κ_l := κ_{T_l}/2 > 0. (If A⁺ = ∅, every A_l is empty; take κ_l := 1.)
   The A_l are Borel and pairwise disjoint, with ⋃_l A_l = A⁺. H is injective on each A_l, and differentiable with injective derivative at every point of A_l.
4. (Jacobian facts.) For u ∈ A⁺, v(u) is linearly independent. By the sibling span_orientation: J(u) > 0; J(u) ≤ ∏_a |DH(u)e_a| ≤ Lⁿ; and ξ_u := J(u)^{-1}·ev_{v(u)} is a unit orientation of span(range v(u)) = range DH(u). (The sibling's ξ satisfies α(v) = J·ξ(α), so ξ = J^{-1}·ev_v.)
5. (One piece.) Fix l.
   - N_l := H(A_l) is Borel (Lusin–Souslin: H is continuous and injective on the Borel set A_l; MeasurableSet.image_of_continuousOn_injOn).
   - Let h_l : ℝ^{N'} → ℝⁿ satisfy h_l(H(u)) = u for u ∈ A_l (an inverse on N_l, arbitrary elsewhere, e.g. Function.invFunOn). For Borel B ⊆ ℝⁿ, N_l ∩ h_l^{-1}(B) = H(A_l ∩ B) is Borel, so h_l is Borel on N_l.
   - m_l(y) := g(h_l(y)) for y ∈ N_l and m_l(y) := 0 otherwise. It is integer-valued and measurable.
   - η_l(y) := ξ_{h_l(y)} = J(h_l(y))^{-1}·ev_{v(h_l(y))} for y ∈ N_l and η_l(y) := 0 otherwise. It is Borel into the finite-dimensional space Λ_n(ℝ^{N'}), hence strongly measurable.
   Check the hypotheses of the sibling int_density_imrep (cmcdt_ims_imrep_of_int_density with P := N', U := ℝ^{N'}, N := N_l, η := η_l, m := m_l):
   - ℝ^{N'} is open, and N_l is a Borel subset of it.
   - N_l ⊆ range H with H Lipschitz, so N_l is countably n-rectifiable (SimonGMT countablyRectifiable_range and CountablyRectifiable.mono).
   - By the sibling area_lintegral (f := H, s := A_l; H is differentiable with injective derivative and injective on A_l): Hⁿ(N_l) = ∫⁻_{A_l} ofReal(J) dλ ≤ Lⁿ·λ(A_l) ≤ Lⁿ·λ(A⁺) < ∞. So Hⁿ(N_l ∩ K) < ∞ for every compact K.
   - Since m_l(H(u)) = g(u) for u ∈ A_l, area_lintegral with the weight |m_l| gives ∫⁻_{N_l ∩ K} |m_l| dHⁿ ≤ ∫⁻_{N_l} |m_l| dHⁿ = ∫⁻_{A_l} ofReal(J)·|g| dλ ≤ Lⁿ·∫⁻_{A_l} |g| dλ < ∞.
   - Orientation. By the sibling piece_tangent (ptd_piece_image_approxTangent_ae with F := H, B := A_l, L, m := κ_l), for λ-a.e. u ∈ A_l, N_l has approximate tangent space range DH(u) at H(u); and η_l(H(u)) = ξ_u is a unit orientation of range DH(u) (step 4). Let E ⊆ A_l be the λ-null exceptional set and E' ⊇ E a Borel λ-null subset of A_l. By area_lintegral, Hⁿ(H(E')) = ∫⁻_{E'} ofReal(J) dλ = 0. Every y ∈ N_l ∖ H(E') is H(u) with u ∈ A_l ∖ E. Hence for Hⁿ⌞N_l-a.e. y there is Q with HasApproximateTangentSpaceAt n N_l y Q and IsUnitOrientationOf (η_l y) Q.
   So int_density_imrep gives an IMRep R_l in ℝ^{N'} with R_l.action(ω) = ∫_{N_l} m_l·η_l(ω) dHⁿ for every form ω.
   By (IMC)(b) with U := E := ℝ^{N'}, there are a current Φ_l and an IMRep R'_l representing Φ_l, with carrier R_l.carrier ∩ ℝ^{N'} = R_l.carrier and with the multiplicity and orientation of R_l. Hence R'_l.action = R_l.action, Φ_l is integer multiplicity, and Φ_l(ω) = ∫_{N_l} m_l·η_l(ω) dHⁿ for every test form ω.
6. (Formula for Φ_l.) Let ω be a test form. The sibling area_integral (G := H, F := A_l, h(y) := m_l(y)·η_l(y)(ω(y))) gives ∫_{N_l} m_l·η_l(ω) dHⁿ = ∫_{A_l} J(u)·g(u)·J(u)^{-1}·ω(H(u))(v(u)) dλ(u) = ∫_{A_l} Ψ_ω dλ, since J > 0 on A_l. So Φ_l(ω) = ∫_{A_l} Ψ_ω dλ.
7. (Mass of Φ_l.) Let ω be admissible for Φ_l.mass = Φ_l.massOn ℝ^{N'}, i.e. a test form with |ω(y)| ≤ 1 for all y. For Hⁿ-a.e. y ∈ N_l, η_l(y) is a unit orientation: η_l(y)(α) = ±α(τ) with τ orthonormal. So |η_l(y)(ω(y))| ≤ |ω(y)| ≤ 1 by (L3). Hence Φ_l(ω) ≤ ∫_{N_l} |m_l| dHⁿ ≤ Lⁿ·∫_{A_l} |g| dλ (step 5), and Φ_l.mass = sSup{ofReal(Φ_l(ω)) : ω admissible} ≤ (L : ℝ≥0∞)ⁿ·∫⁻_{A_l} |g| dλ.
8. (Summation.) By lintegral_iUnion over the disjoint Borel sets A_l, Σ_l Φ_l.mass ≤ Lⁿ·Σ_l ∫⁻_{A_l} |g| dλ = Lⁿ·∫⁻_{A⁺} |g| dλ ≤ Lⁿ·∫⁻_A |g| dλ < ∞.
   Apply (IMSc) (with P := N' and this k) to W := (Φ_l)_{l ∈ ℕ}. It gives S ∈ 𝒟_n(ℝ^{N'}) with HasSum (l ↦ Φ_l(ω)) (S(ω)) for every test form ω; S is integer multiplicity because every Φ_l is.
   For a test form ω, Ψ_ω is integrable on A⁺ = ⋃_l A_l (disjoint Borel sets), so HasSum (l ↦ ∫_{A_l} Ψ_ω dλ) (∫_{A⁺} Ψ_ω dλ) (hasSum_integral_iUnion). By step 6 and uniqueness of sums, S(ω) = ∫_{A⁺} Ψ_ω dλ = ∫_A Ψ_ω dλ (step 2) = ∫_A g(u)·ω(H(u))(DH(u)e_0, …, DH(u)e_{n−1}) dλ(u). ∎

## Key steps

1. Rademacher and alternation: the integrand vanishes a.e. off A⁺ = A ∩ {DH injective} ∩ {g ≠ 0}, and λ(A⁺) ≤ ∫_A|g| < ∞.
2. Mathlib's approximately-linear partition, with r(T) half the coercivity constant of T, splits A⁺ into disjoint Borel pieces A_l on which H is bi-Lipschitz.
3. On N_l = H(A_l), take the integer density m_l = g∘H⁻¹ and the orientation η_l = J⁻¹·(α ↦ α(DH e))∘H⁻¹; piece_tangent and span_orientation show that η_l orients N_l a.e.
4. int_density_imrep and (IMC)(b) give an integer multiplicity current Φ_l. area_integral gives Φ_l(ω) = ∫_{A_l} g·ω(H)(DH e), and (L3) with area_lintegral gives M(Φ_l) ≤ Lⁿ∫_{A_l}|g|.
5. IMS sums the Φ_l, and countable additivity identifies the sum with ∫_A g·ω(H)(DH e).

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
