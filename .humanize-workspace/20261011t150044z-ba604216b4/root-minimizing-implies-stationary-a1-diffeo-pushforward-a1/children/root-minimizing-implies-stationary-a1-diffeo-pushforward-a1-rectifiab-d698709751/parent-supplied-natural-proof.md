# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.rectifiable_area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the parent proof; Simon Ch. 3, 2.3–2.6 (chapter-03.txt lines 362–411: J^M_f = sqrt(det(D_{τ_p}f · D_{τ_q}f)) for an orthonormal basis τ of T_xM, and for 1:1 f, ∫_M h J^M_f dH^n = ∫_{f(M)} h∘f^{-1} dH^n, formula 2.6), proved through the bi-Lipschitz pieces instead of Simon's C¹ pieces; details filled in. Notation: E := ℝ^P, H^n := μHE[n], λ := Lebesgue measure on ℝ^n, Q(x) := approxTangentPlane n M x; for a linear L : E → E and a subspace V with standard orthonormal basis e^V (stdOrthonormalBasis ℝ V), J(L, V) := sqrt(det(⟨L e^V_a, L e^V_b⟩)_{a,b}); so J(x) = J(Dφ(x), Q(x)). Let Λ be a Lipschitz constant of φ.
1. Pieces. By the sibling dpf_rectifiable_bilipschitz_pieces: Lipschitz F_i (constants L_i), Borel B_i, m_i > 0, the lower bound on B_i (so F_i is injective on B_i), differentiability with injective derivative on B_i, P_i := F_i(B_i) Borel ⊆ M pairwise disjoint, Z := M ∖ ⋃ P_i with H^n(Z) = 0.
2. Tangent identification. By the sibling dpf_approxTangent_ae_bilipschitz_piece with Y := M (Borel, ⊆ U, locally H^n-finite) and (F_i, B_i, L_i, m_i): for λ-a.e. b ∈ B_i, HasApproximateTangentSpaceAt n M (F_i b) (range DF_i(b)); by the definition of approxTangentPlane (Exists.choose_spec) and uniqueness of approximate tangent planes (SimonGMT HasApproximateTangentSpaceAt.unique), Q(F_i b) = range DF_i(b) for λ-a.e. b ∈ B_i.
3. Jacobian identity. For L and V as in the notation, normDet(L|_V)² = det(⟨L e^V_a, L e^V_b⟩) (Mathlib LinearMap.normDet_sq_eq_det_gram with the orthonormal basis e^V of V, applied to L|_V = (L : E →ₗ E).domRestrict V, whose values on e^V_a are L e^V_a) and normDet ≥ 0, hence normDet(L|_V) = J(L, V). In particular J(x) = normDet(Dφ(x)|_{Q(x)}).
4. Splitting both sides. φ is injective, so φ(M) = φ(Z) ∪ ⋃_i φ(P_i) with all these sets pairwise disjoint; each φ(P_i) is Borel (Lusin–Souslin: φ continuous and injective) and H^n(φ(Z)) ≤ Λ^n H^n(Z) = 0. For any h : E → [0, ∞] and S = S₀ ∪ ⋃_i S_i with H^n(S₀) = 0 and S_i measurable and pairwise disjoint, H^n⌞S = H^n⌞(⋃ S_i) (the sets are a.e. equal; Measure.restrict_congr_set), and ∫⁻_{⋃S_i} h dH^n = Σ_i ∫⁻_{S_i} h dH^n (Mathlib lintegral_iUnion: measurable disjoint pieces, no measurability of h needed). Therefore ∫⁻_{φ(M)} g dH^n = Σ_i ∫⁻_{φ(P_i)} g dH^n and ∫⁻_M J(x) g(φx) dH^n(x) = Σ_i ∫⁻_{P_i} J(x) g(φx) dH^n(x). It remains to compare the i-th terms.
5. One piece. Φ_i := φ∘F_i is Lipschitz and injective on B_i, and φ(P_i) = Φ_i(B_i) (Set.image_comp); the area formula below is stated with μHE[finrank ℝ ℝ^n], which is μHE[n] by finrank_euclideanSpace_fin. For b ∈ B_i, DΦ_i(b) = Dφ(F_i b)∘DF_i(b) (chain rule; φ is C¹) and normDet(DΦ_i(b)) = normDet(Dφ(F_i b)|_{range DF_i(b)}) · normDet(DF_i(b)) (Mathlib LinearMap.normDet_comp). By the weighted injective Lipschitz area formula (SimonGMT weighted_area_formula_lipschitz_injOn; finrank ℝ ℝ^n = n; it accepts an arbitrary weight E → [0, ∞] and gives ∫⁻_{f(s)} w dH^n = ∫⁻_s ofReal(areaJacobianAt f a) w(f a) dλ, with areaJacobianAt f a = normDet(Df(a))):
 ∫⁻_{φ(P_i)} g dH^n = ∫⁻_{B_i} normDet(DΦ_i(b)) g(Φ_i b) db = ∫⁻_{B_i} normDet(DF_i(b)) · [normDet(Dφ(F_i b)|_{range DF_i(b)}) g(φ(F_i b))] db (ofReal of a product of nonnegative reals is the product of the ofReals).
 By steps 2 and 3, for λ-a.e. b ∈ B_i, normDet(Dφ(F_i b)|_{range DF_i(b)}) = normDet(Dφ(F_i b)|_{Q(F_i b)}) = J(F_i b), so by lintegral_congr_ae the last integral equals ∫⁻_{B_i} normDet(DF_i(b)) w(F_i b) db with w(x) := J(x) g(φ(x)), which by the same area formula for F_i (Lipschitz, injective on B_i) equals ∫⁻_{F_i(B_i)} w dH^n = ∫⁻_{P_i} J(x) g(φ(x)) dH^n(x).
6. Summing step 5 over i and using step 4 gives ∫⁻_{φ(M)} g dH^n = ∫⁻_M J(x) g(φ(x)) dH^n(x). (Uniform in n ≥ 0: for n = 0, Q(x) = {0} a.e., the Gram matrix is empty and J = 1, and normDet of maps out of ℝ^0 is 1. Imports: the Lean proof needs Poincare.SimonGMT.Chapter02.AreaLipschitz and Mathlib.Analysis.InnerProductSpace.NormDet, which the submission may import.)

## Key steps

1. Decompose M into disjoint bi-Lipschitz pieces P_i = F_i(B_i) plus a null set; φ(M) decomposes likewise.
2. Q(F_i b) = range DF_i(b) for a.e. b ∈ B_i by the density lemma and uniqueness of tangent planes.
3. normDet(L|_V) equals the Gram-determinant expression in any orthonormal basis of V.
4. On each piece, the weighted area formula for φ∘F_i, normDet_comp, the a.e. tangent identification and the area formula for F_i give ∫⁻_{φ(P_i)} g = ∫⁻_{P_i} J·(g∘φ).
5. Sum over the pieces using lintegral_iUnion (no measurability of g needed).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/{parent-child-handoff.json,decomposition-scope-v1.json,decomposition-scope-v2.json,decomposition-v2.json,decomposition-audit-v1.json,decomposition-audit-v2.json,decomposition-review-receipt-v1.json,decomposition-review-receipt-v2.json}; sha256(handoff natural_proof) = edb40234e38681383059766fc8fce5de4e38aeb8b70b1da74d3e2f3509f688a2`
- `python3 -I: dag.json scan of all 451 nodes for the 11 dpf_ lean_names (no hits) and for approxTangent/pushforward/area_formula/bilipschitz lean_names`
- `grep -l '"<each dpf_ name>"' nodes/*/decomposition-v*.json (hits only in this node's own v1/v2)`
- `grep -n diffeo-pushforward issue-workers.json; git branch -a | grep diffeo; git grep -n 'dpf_\|imrep_c1_diffeo' <node proof branch> -- GMT (no matches)`
- `rg -n 'pushforward|Pushforward' project/GMT --glob '*.lean'`
- `rg -n 'dpf_|imrep_c1_diffeo|approxTangent.*map|area_formula' project/GMT --glob '*.lean' (no match)`
- `grep -rn in mathlib/Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, ae_tendsto_measure_inter_div, ae_tendsto_average_norm_sub, image_of_continuousOn_injOn, hausdorffMeasure_image_le, contDiff_symm, extDerivWithin_pullback, det_isEmpty, theorem lintegral_iUnion, normDet_comp, normDet_sq_eq_det_gram, euclideanHausdorffMeasure_image, normDet_of_subsingleton, euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton, exists_antilipschitzWith, analyticOnNhd_compContinuousLinearMapCLM, continuous_compContinuousLinearMapCLM, norm_compContinuousLinearMap_le, convolution_tendsto_right_of_continuous, hasFDerivAt_convolution_right, contDiff_convolution_left, lipschitzWith_of_nnnorm_fderiv_le, toHomeomorphOfContinuousClosed, ofInjectiveEndo, eq_smul_basis_det, comp_quasiMeasurePreserving, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, euclideanHausdorffMeasure_homothety_image, euclideanHausdorffMeasure_eq_volume, lintegral_withDensity_eq_lintegral_mul_non_measurable, norm_fderiv_le_of_lipschitz, addHaar_closedBall_eq_addHaar_ball, exists_cthickening_subset_open, continuous_det, det_fromBlocks_zero₂₁, gramSchmidtOrthonormalBasis`
- `grep -n -A12 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' Mathlib/MeasureTheory/Function/Jacobian.lean; grep -A6 'Homeomorph.contDiff_symm' Mathlib/Analysis/Calculus/ContDiff/Operations.lean; grep -A8 euclideanHausdorffMeasure_homothety_image Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep -A5 'normDet_comp\|normDet_sq_eq_det_gram\|euclideanHausdorffMeasure_image' Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn in simongmt/Poincare/SimonGMT: def areaRegularSet, measurableSet_areaRegularSet, area_image_compl_regularSet_eq_zero, weighted_area_formula_lipschitz_injOn, measurable_areaJacobianAt, def HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, def blowUpMap, exteriorDerivativeOn_pullbackFormWithin, def pullbackFormWithin, exteriorDerivativeTestOn, boundary_apply, def TestFormOnConverges, def IsTestForm, def IsSmoothForm, exteriorDerivative_isTestForm, tsupport_exteriorDerivative_subset, def CountablyRectifiable, def areaJacobianAt, structure GeometricCurrentOn`
- `grep -n '^theorem\|^lemma' simongmt/Poincare/SimonGMT/Chapter03/*.lean`
- `lake env lean /tmp/dpf-a3-review/Types.lean`
- `lake env lean /tmp/dpf-a3-review/Assembly.lean (#print axioms assembly_conditional)`
- `lake env lean /tmp/dpf-a3-review/Wiring.lean`
- `lake env lean /tmp/dpf-a3-review/Instances.lean (#print axioms gram_eq_normDet_check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-review-receipt-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/tmp/dpf-a3-review/Types.lean`
- `/tmp/dpf-a3-review/Assembly.lean`
- `/tmp/dpf-a3-review/Wiring.lean`
- `/tmp/dpf-a3-review/Instances.lean`

No declaration in the local snapshot proves this push-forward statement or any of the 11 children, so the children are new. The only related project item is the Ch06 contract's LipschitzPushforwardIntegerMultiplicity, a different Prop about IsLipschitzPushforward that is still unproved (its main_theorem is sorry). SimonGMT Chapter03 asserts no theorem that rectifiable sets have approximate tangent planes almost everywhere. Every library fact the child proofs rely on exists in the pinned Mathlib (25730c7c) and SimonGMT (2b36630) with compatible hypotheses:
- the partition theorem, with rpos : ∀ A, r A ≠ 0;
- Homeomorph.contDiff_symm and the homothety scaling of μHE;
- Besicovitch density and Lebesgue differentiation;
- normDet_comp, normDet_sq_eq_det_gram and euclideanHausdorffMeasure_image;
- SimonGMT's weighted injective Lipschitz area formula, which takes an arbitrary weight and has no rank hypothesis;
- HasApproximateTangentSpaceAt (finrank plus C_c blow-up convergence) and its uniqueness.
All 11 frozen child types and the parent type elaborate in the comparator's replayed contract scope. The parent assembly compiles, and its conditional form uses only propext, Classical.choice and Quot.sound. Sibling wiring and the inferred instances were confirmed in Lean: the Matrix.of Gram expression equals normDet of the restricted map, ‖L‖ is the operator norm, and HasOrthogonalProjection is found. No name collides with the 451 DAG nodes or with other nodes' stored proposals.
