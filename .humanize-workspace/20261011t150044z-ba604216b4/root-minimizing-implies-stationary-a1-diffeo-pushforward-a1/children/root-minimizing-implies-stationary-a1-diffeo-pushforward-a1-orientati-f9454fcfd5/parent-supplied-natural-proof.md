# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.orientation_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof; Simon 6.3.4–3.5 and 3.7 (chapter-06.txt lines 787–831: df_x#ξ = ±D_{τ_1}f ∧ ⋯ ∧ D_{τ_n}f = det(D_{τ_i}f · η_j) η_1 ∧ ⋯ ∧ η_n, J^M_f = |det(D_{τ_i}f · η_j)|, so df_x#ξ = J^M_f η with η = ±η_1 ∧ ⋯ ∧ η_n), with the details filled in. Notation: E := ℝ^P; for an n-covector β, β∘L := β.compContinuousLinearMap L, so (ξ.comp (compContinuousLinearMapCLM L))(β) = ξ(β∘L) =: ζ(β), and (β∘L)(w) = β(Lw₁, …, Lw_n); for vectors w = (w₁, …, w_n), G(w) := (⟨w_a, w_b⟩)_{a,b}.
1. Data. By IsUnitOrientationOf ξ Q there are an orthonormal τ : Fin n → E with span τ = Q and s ∈ {1, −1} with ξ(β) = s β(τ) for all β. τ is a basis of Q, so dim Q = n, and e := stdOrthonormalBasis ℝ Q is indexed by Fin (dim Q) = Fin n (reindex along dim Q = n; the determinant is invariant under this reindexing).
2. Basis independence. e and τ are orthonormal bases of Q, so e_b = Σ_a O_{ab} τ_a with O an orthogonal n×n matrix. Then G(Le) = Oᵀ G(Lτ) O, so det G(Le) = det(O)² det G(Lτ) = det G(Lτ), and J = sqrt(det G(Lτ)). (Alternatively both determinants equal normDet(L|_Q)², Mathlib LinearMap.normDet_sq_eq_det_gram.)
3. Gram–Schmidt. v_a := Lτ_a (a = 1, …, n) are linearly independent (L injective, τ independent), and span v = L(span τ) = L(Q) = Submodule.map L Q. Let σ be the orthonormal basis of L(Q) obtained by Gram–Schmidt from v (Mathlib gramSchmidtNormed / gramSchmidtOrthonormalBasis), and A_{ab} := ⟨v_b, σ_a⟩, so v_b = Σ_a A_{ab} σ_a; for Gram–Schmidt A is upper triangular (σ_a ∈ span(v_1, …, v_a)). A is invertible because v is a basis of L(Q).
4. Determinants. By orthonormality of σ, ⟨v_a, v_b⟩ = Σ_c A_{ca}A_{cb}, i.e. G(Lτ) = AᵀA, so det G(Lτ) = det(A)² and J = |det A| > 0. For every n-covector β, β(v) = det(A) β(σ): the restriction of β to the n-dimensional space L(Q) is an alternating n-form, hence equals β(σ)·det_σ (Mathlib AlternatingMap.eq_smul_basis_det), and det_σ(v) = det A (Basis.det_apply: the matrix of v in the basis σ is A).
5. Bound. As A is upper triangular, det A = Π_a A_{aa} and |A_{aa}| = |⟨v_a, σ_a⟩| ≤ |v_a| = |Lτ_a| ≤ ‖L‖, so J = Π_a |A_{aa}| ≤ ‖L‖^n. (Equivalently, Hadamard's inequality det G(v) ≤ Π_a |v_a|² ≤ ‖L‖^{2n}.)
6. Orientation. For every β: ζ(β) = ξ(β∘L) = s (β∘L)(τ) = s β(Lτ) = s β(v) = s det(A) β(σ). Hence (J^{-1}ζ)(β) = s·sign(det A)·β(σ) with s·sign(det A) ∈ {1, −1}; σ is orthonormal with span σ = L(Q). So IsUnitOrientationOf (J^{-1}ζ) (L(Q)) holds, with the same orthonormal family σ and the same sign for every β.
7. The case n = 0 is included: τ, σ, A are empty, Q = L(Q) = {0}, the determinant of the empty matrix is 1 (Matrix.det_isEmpty), J = 1 ∈ (0, ‖L‖^0], β∘L = β for every 0-covector β (it takes no arguments), so J^{-1}ζ = ξ, which orients {0} = L(Q) with the same sign. (Imports: gramSchmidtNormed lives in Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho and normDet in Mathlib.Analysis.InnerProductSpace.NormDet; the submission may import them, the frozen statement does not use them.)

## Key steps

1. Write ξ = s·(evaluation at τ) with τ an orthonormal basis of Q; dim Q = n.
2. The Gram determinant of L on Q does not depend on the orthonormal basis, so J = sqrt(det G(Lτ)).
3. Gram–Schmidt: Lτ = σA with σ orthonormal spanning L(Q), A upper triangular invertible; G(Lτ) = AᵀA, J = |det A| > 0.
4. |A_aa| ≤ |Lτ_a| ≤ ‖L‖ gives J ≤ ‖L‖^n.
5. β(Lτ) = det(A)β(σ), so J^{-1}ζ(β) = s·sign(det A)·β(σ): a unit orientation of L(Q).

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
