# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.piece_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. The blow-up argument of the proof of Simon Ch. 3, 1.6 '⇒' (chapter-03.txt lines 109–144), applied to one bi-Lipschitz Lipschitz piece instead of a piece of a C¹ submanifold. It provides the identification T_vB = (tangent plane of the piece) that the area formula on rectifiable sets (Ch. 3, 2.1–2.4) needs in step 4(e) of the supplied proof; it is used by the sibling area_formula. The same statement occurs, not yet accepted, as ptd_piece_image_approxTangent_ae in another branch.

Notation. H^n := μHE[n]; on ℝ^n it equals Lebesgue measure λ = volume. J(a) := areaJacobianAt F a = normDet DF(a). η_{y,r}(z) := r^{-1}(z − y) (SimonGMT blowUpMap). A := F(B). HasApproximateTangentSpaceAt n S y Q means: dim Q = n and ∫_{η_{y,r}(S)} f dH^n → ∫_Q f dH^n as r → 0⁺ for every f ∈ C_c(ℝ^P).

0. Preliminaries.
(a) F is injective on B (if F(a) = F(a′) then m|a − a′| ≤ 0) and continuous, so A is Borel (Lusin–Souslin, MeasurableSet.image_of_continuousOn_injOn).
(b) J is Borel (SimonGMT measurable_areaJacobianAt) and 0 ≤ J ≤ L^n: ‖DF(a)‖ ≤ L, and for a linear T, normDet T·λ(B_1(0)) = H^n(T(B_1(0))) ≤ ‖T‖^n λ(B_1(0)) (Mathlib LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume and SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn). In particular J is locally integrable.
(c) Area formula: ∫_A g dH^n = ∫_B J(a)·g(F(a)) dλ(a) for every g : ℝ^P → ℝ (SimonGMT integral_area_formula_of_injective_derivative with s := B, using 0(a), the hypotheses on DF, finrank ℝ^n = n and μHE[n] = λ on ℝ^n; no integrability is needed).
(d) Scaling: η_{y,r} (r > 0) is a similarity with ratio r^{-1}, so H^n(η_{y,r}(S)) = r^{-n}H^n(S) (translation invariance and homogeneity of H^n: Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_homothety_image), and hence ∫_{η_{y,r}(S)} g dH^n = r^{-n}∫_S g(η_{y,r}(z)) dH^n(z) for Borel S and every g (η_{y,r} is a measurable embedding; MeasurableEmbedding.integral_map).
1. (Good points.) By the Lebesgue differentiation theorem for λ (Mathlib IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub applied to the locally integrable function g₀ := 1_B·J), for λ-a.e. b ∈ ℝ^n,
 (β) r^{-n}∫_{B̄_r(b)} |1_B(a)J(a) − 1_B(b)J(b)| dλ(a) → 0 as r → 0⁺.
Fix b ∈ B satisfying (β); λ-a.e. b ∈ B does. Put y := F(b), Λ := DF(b) (injective by hypothesis) and Q := range Λ, so dim Q = n.
2. (Coercivity.) Λ is injective on the finite-dimensional ℝ^n, so there is κ > 0 with |Λc| ≥ κ|c| for all c.
3. (Rescaled formula.) Fix f ∈ C_c(ℝ^P) and R > 0 with f = 0 outside B_R(0); let M := sup|f|. For r > 0 put Φ_r(c) := (F(b + rc) − F(b))/r. By 0(d), 0(c) and the substitution a = b + rc (λ is translation invariant and λ(r·S) = r^n λ(S)):
 I(r) := ∫_{η_{y,r}(A)} f dH^n = r^{-n}∫_A f(η_{y,r}(z)) dH^n(z) = r^{-n}∫_B J(a) f((F(a) − y)/r) dλ(a) = ∫_{ℝ^n} 1_B(b + rc)J(b + rc) f(Φ_r(c)) dλ(c).
4. (Localization.) If b + rc ∈ B and f(Φ_r(c)) ≠ 0, then |Φ_r(c)| < R, and since b, b + rc ∈ B, m·r|c| ≤ |F(b + rc) − F(b)| < rR, so |c| < R/m. If f(Λc) ≠ 0 then |Λc| < R, so |c| < R/κ. Let ρ := max(R/m, R/κ) and D_ρ := B̄_ρ(0). Both c ↦ 1_B(b + rc)J(b + rc)f(Φ_r(c)) and c ↦ J(b)f(Λc) vanish outside D_ρ.
5. (Convergence.) For c ∈ D_ρ, |1_B(b + rc)J(b + rc)f(Φ_r(c)) − J(b)f(Λc)| ≤ M|1_B(b + rc)J(b + rc) − J(b)| + J(b)|f(Φ_r(c)) − f(Λc)|.
(i) Since b ∈ B, ∫_{D_ρ} |1_B(b + rc)J(b + rc) − J(b)| dλ(c) = r^{-n}∫_{B̄_{rρ}(b)} |1_B J − 1_B(b)J(b)| dλ = ρ^n·(rρ)^{-n}∫_{B̄_{rρ}(b)} |1_B J − 1_B(b)J(b)| dλ → 0 by (β).
(ii) F is differentiable at b: for θ > 0 there is s_θ > 0 with |F(b + h) − F(b) − Λh| ≤ θ|h| for |h| < s_θ. For 0 < r < s_θ/ρ and c ∈ D_ρ this gives |Φ_r(c) − Λc| ≤ θρ. So Φ_r → Λ uniformly on D_ρ; f is uniformly continuous, hence sup_{D_ρ}|f∘Φ_r − f∘Λ| → 0 and ∫_{D_ρ} J(b)|f(Φ_r(c)) − f(Λc)| dλ(c) ≤ J(b)λ(D_ρ)·sup_{D_ρ}|f∘Φ_r − f∘Λ| → 0.
By step 4 the integrands vanish off D_ρ, so I(r) → I_∞ := ∫_{ℝ^n} J(b)f(Λc) dλ(c) as r → 0⁺.
6. (Identification.) Λ is injective and J(b) = normDet Λ, so by the linear area formula (Mathlib LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume: H^n(Λ(S)) = normDet Λ·λ(S), i.e. H^n⌞Q is the image of normDet Λ·λ under the injective map Λ) ∫_Q f dH^n = ∫_{ℝ^n} normDet Λ·f(Λc) dλ(c) = I_∞.
7. (Conclusion.) For every f ∈ C_c(ℝ^P), ∫_{η_{F(b),r}(F(B))} f dH^n → ∫_{range DF(b)} f dH^n as r → 0⁺, and dim range DF(b) = n. So HasApproximateTangentSpaceAt n (F(B)) (F(b)) (range DF(b)) holds at every b ∈ B satisfying (β), that is, for (volume.restrict B)-a.e. b. ∎

## Key steps

1. Area formula for the injective piece and scaling of H^n: ∫_{η_{F(b),r}(F(B))} f dH^n = ∫ 1_B(b+rc)J_F(b+rc) f((F(b+rc) − F(b))/r) dc.
2. The bi-Lipschitz lower bound and injectivity of DF(b) confine both integrands to a fixed ball.
3. At Lebesgue points b ∈ B of 1_B·J_F, differentiability of F at b gives convergence to ∫ J_F(b) f(DF(b)c) dc.
4. The linear area formula identifies the limit with ∫_{range DF(b)} f dH^n.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; python3 read of snapshot project/lake-manifest.json`
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem extDeriv_pullback|theorem extDeriv_apply|theorem LipschitzOnWith.extend_finite_dimension|theorem ContinuousOn.measurableEmbedding|theorem MeasurableSet.image_of_continuousOn_injOn|theorem euclideanHausdorffMeasure_image_eq_normDet_mul_volume|theorem det_succ_column_zero|theorem det_le |theorem ae_tendsto_average_norm_sub|theorem ae_tendsto_measure_inter_div|theorem gramSchmidtNormed_orthonormal|theorem integral_withDensity_eq_integral_smul ' <snapshot>/mathlib/Mathlib`
- `rg -n 'Cauchy-Binet|Cauchy–Binet|cauchyBinet' <snapshot>/mathlib/Mathlib (no match); rg -n 'eq_smul_basis_det' <snapshot>/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `grep -n '^theorem|^def' simongmt Chapter06/{Forms,Currents,Mass}.lean, Chapter03/{Rectifiable,SubmanifoldCover,FinitePerimeter,Differential}.lean, Chapter02/{WeightedArea,Area,AreaFormula,AreaLipschitz,AreaCritical,AreaApproximation,Lipschitz,WhitneyExtension}.lean`
- `grep -rln 'C¹ approximation|C1 approximation|Lusin' simongmt/Poincare (no C¹ Approximation Theorem); grep -n for integral_area_formula_of_injective_derivative, weighted_area_formula_of_injective_derivative, areaJacobianAt_eq_sqrt_det_adjoint_comp, measurable_areaJacobianAt, euclideanHausdorffMeasure_image_le_of_lipschitzOn, tsupport_exteriorDerivative_subset, HasApproximateTangentSpaceAt.unique, exists_contDiff_one_extension_of_whitney, area_image_criticalSet_eq_zero`
- `python3 scans of dag.json (673→719 nodes): frozen types/status of codim1_rdo_graph_chart, codim1_rdo_de_giorgi_gauss_green, dor_ims_massOn_le_measure and the selected node; keyword scan 'C¹ approximation|area formula|approximate tangent|Lemma 1.2|bilipschitz'; diffeo_pushforward subtree statuses; lean_name lookup of the 7 new codim1_lur_* names (no hits)`
- `git grep -l codim1_lur <1377 unique ref tips> -- 'GMT/*.lean' (no match)`
- `git show {fae4fd1e,a2ba78fc,048ff2b9,bed5b849}:GMT/Ch07/Submission.lean + '#print axioms' for dor_ims_massOn_le_measure, dpf_rectifiable_bilipschitz_pieces, regcomp_approx_tangent_locality, ptd_piece_image_measurable_ae_pullback; lean -DautoImplicit=false (LEAN_PATH from .lake/build/lib/lean/GMT/Ch07/Submission.trace)`
- `lean -DautoImplicit=false /tmp/lup-split/final/Types.lean; lean -DautoImplicit=false /tmp/lup-split/final/Assembly.lean (#print axioms Submission.codim1_rdo_local_unit_representation); lean /tmp/lup-split/final/Inst.lean (rfl instance checks)`
- `sed -n 1,480p book/chapter-03.txt (Ch. 3, 1.1–2.10); sed -n 160,175p book/chapter-02.txt (C¹ Approximation Theorem 1.5, Whitney 1.6)`
- `read nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-{5d8d9c70c5,de9c9e6c74} (handoff, decomposition-v1.json) and the parent-supplied natural proofs of the four reused nodes and of ptd_piece_image_approxTangent_ae`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-5d8d9c70c5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-de9c9e6c74/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-approx-tangent-locality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-e483a373f0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-64a6473a66/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/lup-split/final/Types.lean`
- `/tmp/lup-split/final/Assembly.lean`
- `/tmp/lup-split/final/Inst.lean`
- `/tmp/lup-split/reuse/Check_dor_ims_massOn_le_measure.lean`
- `/tmp/lup-split/reuse/Check_dpf_rectifiable_bilipschitz_pieces.lean`
- `/tmp/lup-split/reuse/Check_regcomp_approx_tangent_locality.lean`
- `/tmp/lup-split/reuse/Check_ptd_piece_image_measurable_ae_pullback.lean`

Pins match.
- Snapshot manifest: project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib.
- Snapshot lake-manifest: simongmt 2b366308, equal to .lake/packages/simongmt.
- Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Library (what exists).
- Snapshot Mathlib: extDeriv_pullback and extDeriv_apply (Analysis/Calculus/DifferentialForm/Basic.lean:259, 198); LipschitzOnWith.extend_finite_dimension (Analysis/Normed/Module/FiniteDimension.lean:207); MeasurableSet.image_of_continuousOn_injOn and ContinuousOn.measurableEmbedding (MeasureTheory/Constructions/Polish/Basic.lean:821, 865); LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (Analysis/InnerProductSpace/NormDet.lean:433); Matrix.det_succ_column_zero, Matrix.det_le and AlternatingMap.eq_smul_basis_det; ae_tendsto_average_norm_sub (MeasureTheory/Covering/DensityTheorem.lean:150); integral_withDensity_eq_integral_smul.
- SimonGMT: integral_area_formula_of_injective_derivative and weighted_area_formula_of_injective_derivative (Chapter02/WeightedArea.lean:151, 76); areaJacobianAt_eq_sqrt_det_adjoint_comp; measurable_areaJacobianAt; euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216); tsupport_exteriorDerivative_subset (Chapter06/Currents.lean:182); HasApproximateTangentSpaceAt.unique (Chapter03/Rectifiable.lean:232); the Whitney C¹ extension theorem (Chapter02/WhitneyExtension.lean:373).

Library (what is missing).
- The snapshot Mathlib has no Cauchy–Binet (rg: no match).
- SimonGMT has no C¹ Approximation Theorem (Ch. 2, 1.5) and no area formula on rectifiable sets; the Chapter03/Rectifiable.lean header says the area/coarea theorems are not asserted.
- LinearMap.normDet and the Chapter02 area modules are not imported by GMT.Ch07.Submission, so the child statements use Matrix.det Gram determinants instead.

DAG.
- The 7 new codim1_lur_* names occur in no dag.json node (719 nodes) and in no GMT/*.lean at any of 1377 unique ref tips.
- Reused with byte-identical types, all accepted: dor_ims_massOn_le_measure (fae4fd1e), dpf_rectifiable_bilipschitz_pieces (a2ba78fc), regcomp_approx_tangent_locality (048ff2b9) and ptd_piece_image_measurable_ae_pullback (bed5b849). A fresh compilation of each candidate Submission.lean with #print axioms gives only propext, Classical.choice and Quot.sound.
- ptd_piece_image_approxTangent_ae (decomposing) has the same type as the new piece_tangent but is not accepted. dpf_area_formula_bilipschitz_rectifiable (speculative-ready) concerns self-maps of ℝ^P and is not accepted either.

Lean.
- Types.lean elaborates all 11 child types after import GMT.Ch07.Submission with the contract opens (exit 0, sorry warnings only).
- Inst.lean confirms by rfl that the Gram determinants are Matrix.det over Matrix (Fin k) (Fin k) ℝ, that .indicator is Set.indicator, and that the adjoint term is the continuous linear map ι* applied to w − x.
- Assembly.lean proves Submission.codim1_rdo_local_unit_representation (frozen type copied from dag.json). It takes codim1_rdo_graph_chart and codim1_rdo_de_giorgi_gauss_green (frozen types from dag.json) and chart_divergence, chart_perimeter and pushforward_rep as axioms. #print axioms lists only these five plus propext, Classical.choice and Quot.sound; no sorryAx occurs.
