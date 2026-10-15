# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.cylinder_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 (B5) of the supplied proof: the product pieces Ĝ_i(t, u) = ι(t, G_i(u)) on (0, 1) × A_i of 8(b) and the Fubini representation of 8(f). The pieces are combined exactly as in step 5(d) of the supplied proof (piece_current and IMS) instead of being glued into a single carrier ι((0, 1) × M). This specializes the supplied argument. Steps 8(a) (product-null lemma), 8(c) (product measure identity) and 8(d)–(e) (the IMRep of the product and its tangent planes) are needed only for that gluing. IMS combines integer multiplicity pieces with summable masses directly, so they become unnecessary. Simon Ch. 6, 2.18–2.20 and 3.2(2): [[(0,1)]] × τ(M, θ, ξ) = τ((0,1) × M, θ, e₁ ∧ ξ).

Hypotheses (antecedents of the statement, exact frozen Lean types):
- (CB) is the frozen type of cmcdt_lp_covector_norm_bounds:
  (L1) |A^#β| ≤ ‖A‖^k·|β| (Lean: covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β);
  (L2) |ι_vβ| ≤ |v|·|β| (Lean: covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β);
  (L3) |α(τ)| ≤ |α| for orthonormal τ.
- (VO), (MR), (IMC) are the frozen types of dtc_vanish_off_support, cmc_massOn_eq_imRep_measure and cmc_imRep_locality_restrict_sub.
- (IMS) is the frozen type of cmcdt_im_series, and (IMSc) := (IMS) applied to (VO), (MR) and (IMC). (IMSc) says: for all P, k and every sequence W_i ∈ 𝒟_{k+1}(ℝ^P) with Σ_i M(W_i) < ∞ there is S with HasSum (i ↦ W_i(ω)) (S(ω)) for every ω, M(S) ≤ Σ_i M(W_i) and spt S ⊆ closure ⋃_i spt W_i; and S is integer multiplicity if every W_i is.
Fix N, k, X and C as in the statement, and put n := k + 1; |·| := covectorEuclideanNorm; e_b := EuclideanSpace.single b 1 ∈ ℝⁿ.

Notation:
- ι(t, x) := toLp(Fin.cons t (ofLp x)) ∈ ℝ^{N+1} for t ∈ ℝ and x ∈ ℝ^N; likewise ι'(t, u) ∈ ℝ^{n+1} for u ∈ ℝⁿ.
- tail(z) := toLp(Fin.tail(ofLp z)) ∈ ℝⁿ for z ∈ ℝ^{n+1}, so that z = ι'(z_0, tail z).
- e₀ := EuclideanSpace.single 0 1 = ι(1, 0) ∈ ℝ^{N+1}.
- Jv := ι(0, v) is a linear isometry ℝ^N → ℝ^{N+1} (‖Jv‖ = ‖v‖, so ‖J‖ ≤ 1).
- ê_a := EuclideanSpace.single a 1 ∈ ℝ^{n+1}, so ê_0 = ι'(1, 0) and ê_{succ b} = ι'(0, e_b).

1. (Pieces of X.) Apply the sibling piece_representation to (CB), (VO), (MR), (IMC) and X; X is integer multiplicity with X.mass < ∞. It gives, for i ∈ ℕ, maps G_i with Lipschitz constants L_i, Borel sets A_i ⊆ ℝⁿ, measurable w_i : ℝⁿ → ℤ and measurable c_i : ℝⁿ → ℝ such that:
   - G_i is differentiable at every u ∈ A_i;
   - w_i is integrable on A_i;
   - for u ∈ A_i, c_i(u) ≥ 0 and |α(DG_i(u)e_0, …, DG_i(u)e_{n−1})| ≤ c_i(u)·|α| for every n-covector α on ℝ^N;
   - Σ_i ∫⁻_{A_i} ofReal(|w_i|·c_i) dλ ≤ X.mass;
   - HasSum (i ↦ ∫_{A_i} w_i(u)·η(G_i u)(DG_i(u)e_0, …, DG_i(u)e_{n−1}) du) (X(η)) for every test form η on ℝ^N.
   (G_i(A_i) ⊆ spt X is also provided but not needed here.) Put B_i := ∫⁻_{A_i} ofReal(|w_i|c_i); then Σ_i B_i ≤ X.mass < ∞.
2. (Product pieces.) For each i define Ĝ_i : ℝ^{n+1} → ℝ^{N+1} by Ĝ_i(z) := ι(z_0, G_i(tail z)), Â_i := {z : z_0 ∈ (0, 1) and tail z ∈ A_i}, and ŵ_i(z) := w_i(tail z).
   (a) Ĝ_i is max(1, L_i)-Lipschitz: |Ĝ_i z − Ĝ_i z'|² = |z_0 − z'_0|² + |G_i(tail z) − G_i(tail z')|² ≤ |z_0 − z'_0|² + L_i²|tail z − tail z'|² ≤ max(1, L_i)²|z − z'|².
   (b) Â_i is Borel, being the preimage of (0, 1) × A_i under the continuous map z ↦ (z_0, tail z). ŵ_i : ℝ^{n+1} → ℤ is measurable.
   (c) (Fubini.) Ψ(t, u) := ι'(t, u) is a measurable equivalence ℝ × ℝⁿ → ℝ^{n+1} carrying volume ⊗ volume to volume. This follows from Mathlib MeasureTheory.volume_preserving_piFinSuccAbove with pivot 0, composed with EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp. Moreover Ψ((0, 1) × A_i) = Â_i. Hence, for every function f on ℝ^{n+1} that is integrable on Â_i (or nonnegative and measurable), ∫_{Â_i} f dλ^{n+1} = ∫_{A_i} ∫_{(0,1)} f(ι'(t, u)) dt du. In particular ∫⁻_{Â_i} |ŵ_i| = ∫⁻_{A_i} |w_i| < ∞, so ŵ_i is integrable on Â_i.
   (d) (Derivative.) Let z ∈ Â_i and u := tail z ∈ A_i. G_i is differentiable at u, and ι, tail and z ↦ z_0 are continuous linear. So Ĝ_i = ι ∘ (z ↦ (z_0, G_i(tail z))) is differentiable at z with DĜ_i(z)ζ = ι(ζ_0, DG_i(u)(tail ζ)). Hence DĜ_i(z)ê_0 = ι(1, 0) = e₀ and DĜ_i(z)ê_{succ b} = ι(0, DG_i(u)e_b) = J(DG_i(u)e_b). That is, (DĜ_i(z)ê_a)_{a ∈ Fin (n+1)} = Fin.cons e₀ (b ↦ J(DG_i(u)e_b)).
3. (Representation of C.) Fix a test form ω on ℝ^{N+1}, let η be the test form given by the hypothesis, and put f_{i,ω}(z) := ω(Ĝ_i z)(DĜ_i(z)ê_0, …, DĜ_i(z)ê_n).
   - For u ∈ A_i, the hypothesis with x := G_i(u) and v := (DG_i(u)e_b)_b gives η(G_i u)(DG_i(u)e) = ∫_0^1 ω(ι(t, G_i u))(Fin.cons e₀ (b ↦ J(DG_i(u)e_b))) dt.
   - For t ∈ (0, 1), ι'(t, u) ∈ Â_i and Ĝ_i(ι'(t, u)) = ι(t, G_i u), so by 2(d) the integrand is f_{i,ω}(ι'(t, u)). The interval integral over [0, 1] equals the integral over (0, 1). Hence η(G_i u)(DG_i(u)e) = ∫_{(0,1)} f_{i,ω}(ι'(t, u)) dt.
   - ŵ_i·f_{i,ω} is measurable and bounded on Â_i by |ŵ_i|·sup_y‖ω(y)‖·max(1, L_i)^{n+1}, so it is integrable on Â_i.
   By piece_representation and 2(c):
   C(ω) = X(η) = Σ_i ∫_{A_i} w_i(u)·η(G_i u)(DG_i(u)e) du = Σ_i ∫_{A_i} w_i(u)·∫_{(0,1)} f_{i,ω}(ι'(t, u)) dt du = Σ_i ∫_{Â_i} ŵ_i(z)·ω(Ĝ_i z)(DĜ_i(z)ê) dz,
   as a HasSum.
4. (Integer pieces.) For each i, apply the sibling piece_current to (CB), (IMC), (IMSc) with N' := N + 1, k := k + 1, H := Ĝ_i, A := Â_i and g := ŵ_i. It gives an integer multiplicity Ŝ_i ∈ 𝒟_{n+1}(ℝ^{N+1}) with Ŝ_i(ω) = ∫_{Â_i} ŵ_i(z)·ω(Ĝ_i z)(DĜ_i(z)ê) dz for every test form ω.
5. (Masses.) Let z = ι'(t, u) with t ∈ (0, 1) and u ∈ A_i.
   - f_{i,ω}(z) = β_{t,u}(DG_i(u)e) with the n-covector β_{t,u} := (ω(ι(t, G_i u)).curryLeft e₀).compContinuousLinearMap J on ℝ^N, because (γ.curryLeft x)(w) = γ(Fin.cons x w).
   - By (L1) (‖J‖ ≤ 1) and (L2) (‖e₀‖ = 1), |β_{t,u}| ≤ |ω(ι(t, G_i u))|. So by step 1, |f_{i,ω}(z)| ≤ c_i(u)·|ω(ι(t, G_i u))|.
   - Let ω be admissible (|ω(y)| ≤ 1 for all y). The function z ↦ |ŵ_i(z)·f_{i,ω}(z)| is measurable and integrable on Â_i (step 3). Apply 2(c) (Tonelli) to it, and then bound the inner integral pointwise in u by the previous item (lintegral_mono; c_i is measurable by step 1):
     |Ŝ_i(ω)| ≤ ∫_{Â_i} |ŵ_i·f_{i,ω}| dλ^{n+1} = ∫_{A_i} |w_i(u)|·∫_{(0,1)} |f_{i,ω}(ι'(t, u))| dt du ≤ ∫_{A_i} |w_i(u)|·c_i(u) du = B_i.toReal.
   Hence Ŝ_i.mass = sSup{ofReal(Ŝ_i(ω)) : ω admissible} ≤ B_i, and Σ_i Ŝ_i.mass ≤ X.mass < ∞.
6. (Sum.) Apply (IMSc) (with P := N + 1 and degree (k + 1) + 1) to W := (Ŝ_i)_i. It gives an integer multiplicity Ĉ with HasSum (i ↦ Ŝ_i(ω)) (Ĉ(ω)) for every ω. By steps 3 and 4, C(ω) = Σ_i Ŝ_i(ω) = Ĉ(ω) for every test form ω. So an IMRep representing Ĉ also represents C, and C is integer multiplicity. ∎

## Key steps

1. piece_representation gives X(η) = Σ_i ∫_{A_i} w_i·η(G_i)(DG_i e) with Σ_i ∫|w_i|c_i ≤ M(X).
2. Product pieces Ĝ_i(z) = ι(z_0, G_i(tail z)) on Â_i = (0,1) × A_i with ŵ_i = w_i∘tail are Lipschitz, Borel and integrable, and DĜ_i(z)ê = (e₀, J·DG_i(u)e).
3. The slice formula for η and Fubini (λ^{n+1} = λ¹ ⊗ λⁿ) give C(ω) = X(η) = Σ_i ∫_{Â_i} ŵ_i·ω(Ĝ_i)(DĜ_i ê).
4. piece_current makes each term an integer multiplicity Ŝ_i; (L1), (L2) and c_i give M(Ŝ_i) ≤ ∫|w_i|c_i.
5. IMS sums the Ŝ_i to an integer multiplicity current equal to C.

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
