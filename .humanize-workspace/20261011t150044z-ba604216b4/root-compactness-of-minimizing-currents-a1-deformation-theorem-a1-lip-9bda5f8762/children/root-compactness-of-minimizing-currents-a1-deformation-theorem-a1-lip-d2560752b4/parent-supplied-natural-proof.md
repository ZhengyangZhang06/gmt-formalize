# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.pullback_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 (B4), parts (i)–(iv), of the supplied proof: weak continuity of pull-backs. The L¹-approximation of (ii) is not needed here, because the sibling minor_continuity already accepts L¹ weights. Simon Ch. 6, 2.29 and 3.6 use this when identifying the Lipschitz push-forward with the area-formula current.

Notation. λ := volume on ℝ^m. e_t := EuclideanSpace.single t 1 ∈ ℝ^m and e'_i := EuclideanSpace.single i 1 ∈ ℝ^{N'}. 𝒥 is the finite set of strictly increasing maps J : Fin m → Fin N'.
- For J ∈ 𝒥 and y ∈ ℝ^{N'}, ω_J(y) := ω(y)(e'_{J(0)}, …, e'_{J(m−1)}). ω_J is continuous with compact support, being the evaluation of the continuous, compactly supported ω at a fixed family.
- For a map H : ℝ^m → ℝ^{N'} and u ∈ ℝ^m, M_J(H)(u) := det((DH(u)e_t)_{J(s)})_{s,t ∈ Fin m} with DH(u) := fderiv ℝ H u. In the notation of minor_continuity this is the minor with r := m, rows a := J and columns b := id.
- ‖·‖_op is the operator norm of continuous alternating maps.

1. (Coordinate expansion.) For every m-covector α on ℝ^{N'} and every z : Fin m → ℝ^{N'},
   α(z) = Σ_{J ∈ 𝒥} α(e'_{J(0)}, …, e'_{J(m−1)})·det((z_t)_{J(s)})_{s,t}.   (E)
   Write z_t = Σ_i (z_t)_i e'_i. By multilinearity, α(z) = Σ_{f : Fin m → Fin N'} (∏_t (z_t)_{f(t)})·α(e'_{f(0)}, …, e'_{f(m−1)}).
   - If f is not injective, the family e'∘f has a repetition and the term vanishes (alternation).
   - An injective f factors uniquely as f = J∘π, with J ∈ 𝒥 the increasing enumeration of its image and π a permutation of Fin m. Then α(e'∘J∘π) = sign(π)·α(e'∘J).
   Grouping by J gives α(z) = Σ_J α(e'∘J)·Σ_π sign(π)∏_t (z_t)_{J(π(t))}, and the inner sum is det((z_t)_{J(s)})_{s,t} (Leibniz formula). (Only the scalar identity (E) is used; no coordinate covectors need to be constructed.)
   Applying (E) with α := ω(H(u)) and z := (DH(u)e_t)_t gives, for every map H and every u,
   ω(H(u))(DH(u)e_0, …, DH(u)e_{m−1}) = Σ_{J ∈ 𝒥} ω_J(H(u))·M_J(H)(u).   (E')
2. (Bounds and measurability.) Each H_j and H₀ is L-Lipschitz, so ‖DH_j(u)‖ ≤ L and ‖DH₀(u)‖ ≤ L for every u (norm_fderiv_le_of_lipschitz). Hence every entry of the matrices in M_J is bounded by L, and |M_J(H_j)|, |M_J(H₀)| ≤ K := m!·L^m. Let C_J := sup|ω_J| < ∞.
   The functions u ↦ ω(H_j(u))(DH_j(u)e) and the terms of (E') are Borel: u ↦ DH_j(u) is Borel (measurable_fderiv), H_j is continuous, and ω and evaluation are continuous. All integrands below are dominated by |w|·Σ_J C_J·K, which is integrable. So all integrals exist and, by (E'), ∫ w·ω(H)(DH e) = Σ_J ∫ w·(ω_J∘H)·M_J(H) for H ∈ {H_j, H₀}.
   It therefore suffices to prove, for each fixed J ∈ 𝒥, that ∫ w·(ω_J∘H_j)·M_J(H_j) → ∫ w·(ω_J∘H₀)·M_J(H₀).
3. (Two terms.) Write the difference as T1_j + T2_j, where
   T1_j := ∫ w·(ω_J∘H_j − ω_J∘H₀)·M_J(H_j) and T2_j := ∫ w·(ω_J∘H₀)·(M_J(H_j) − M_J(H₀)).
   (a) T1_j → 0. ω_J is uniformly continuous (continuous with compact support) and H_j → H₀ uniformly. So δ_j := sup_u |ω_J(H_j(u)) − ω_J(H₀(u))| → 0, and |T1_j| ≤ δ_j·K·‖w‖_{L¹} → 0.
   (b) T2_j → 0. Apply the sibling minor_continuity with m, p := N', r := m, the same L, v := (H_j)_j, v₀ := H₀, rows a := J, columns b := id and weight c := w·(ω_J∘H₀). The weight is measurable and |c| ≤ C_J|w|, so c is integrable. The sibling gives ∫ c·M_J(H_j) → ∫ c·M_J(H₀), i.e. T2_j → 0. (Its matrix entry fderiv ℝ (v j) u (EuclideanSpace.single (b t) 1) (a s) is (DH_j(u)e_t)_{J(s)}.)
4. Summing over the finitely many J ∈ 𝒥 gives ∫ w(u)·ω(H_j(u))(DH_j(u)e) du → ∫ w(u)·ω(H₀(u))(DH₀(u)e) du. For m = 0 the argument still applies: 𝒥 has one element (the empty map), every determinant equals 1, and T2_j = 0. ∎

## Key steps

1. Coordinate expansion: α(z) = Σ_J α(e'_J)·det((z_t)_{J(s)}) over strictly increasing J, by multilinearity, alternation and the Leibniz formula.
2. Hence ω(H u)(DH(u)e) = Σ_J ω_J(H u)·M_J(H)(u), with |M_J| ≤ m!L^m and ω_J continuous with compact support.
3. For each J, the term with ω_J(H_j) − ω_J(H₀) tends to 0 by uniform continuity of ω_J and uniform convergence of H_j.
4. The remaining term tends to 0 by minor_continuity with the L¹ weight w·ω_J(H₀).

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
