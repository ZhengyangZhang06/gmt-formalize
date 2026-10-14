# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_tangent_transport-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof. Simon 6.3.7 (chapter-06.txt lines 822–831) uses, without proof, that at H^n-a.e. point the approximate tangent space of f(M) is spanned by the images d^M f_x(τ_i); for the C¹ diffeomorphism φ this is supplied here from the siblings, with the details filled in. Notation: E := ℝ^P, H^n := μHE[n], λ := Lebesgue measure on ℝ^n (= μHE[n] there), Q(x) := approxTangentPlane n M x (by definition the chosen plane P with HasApproximateTangentSpaceAt n M x P when one exists, ⊥ otherwise). Replacing Λ by max(Λ, 1) (both Lipschitz and antilipschitz bounds survive enlarging the constant) we assume Λ ≥ 1.
1. Pieces. By the sibling dpf_rectifiable_bilipschitz_pieces (M Borel, countably n-rectifiable) there are Lipschitz F_i (with constants L_i), Borel B_i ⊆ ℝ^n and m_i > 0 with m_i|a − a'| ≤ |F_i a − F_i a'| on B_i, F_i differentiable with injective derivative on B_i, P_i := F_i(B_i) Borel ⊆ M pairwise disjoint, and Z := M ∖ ⋃_i P_i H^n-null.
2. Tangent planes of M along the pieces. Apply the sibling dpf_approxTangent_ae_bilipschitz_piece with Y := M (Borel, ⊆ U, H^n(M ∩ C) < ∞ for compact C ⊆ U) and (F_i, B_i, L_i, m_i) (F_i(B_i) ⊆ M): for λ-a.e. b ∈ B_i, HasApproximateTangentSpaceAt n M (F_i b) (range DF_i(b)). For such b the existential in the definition of approxTangentPlane holds, so HasApproximateTangentSpaceAt n M (F_i b) Q(F_i b) (Exists.choose_spec), and by uniqueness of approximate tangent planes (SimonGMT HasApproximateTangentSpaceAt.unique; Simon Ch. 3 1.5(1)) Q(F_i b) = range DF_i(b).
3. Properties of φ(M). φ is continuous and injective (antilipschitz), so φ(M) is Borel (Lusin–Souslin, MeasurableSet.image_of_continuousOn_injOn). Since φ^{-1}(U) = U, x ∈ M ⊆ U implies φ(x) ∈ U, so φ(M) ⊆ U. For compact C ⊆ U: φ^{-1}(C) is closed (φ continuous) and bounded (|x − x₀| ≤ Λ|φ(x) − φ(x₀)| for a fixed x₀), hence compact, and φ^{-1}(C) ⊆ φ^{-1}(U) = U; as φ(M) ∩ C ⊆ φ(M ∩ φ^{-1}(C)), H^n(φ(M) ∩ C) ≤ Λ^n H^n(M ∩ φ^{-1}(C)) < ∞ (LipschitzWith.hausdorffMeasure_image_le; μHE[n] is a fixed multiple of μH[n]).
4. Tangent planes of φ(M) along the pieces. Φ_i := φ∘F_i is (ΛL_i)-Lipschitz; for a, a' ∈ B_i, |Φ_i(a) − Φ_i(a')| ≥ Λ^{-1}|F_i(a) − F_i(a')| ≥ (m_i/Λ)|a − a'|; at b ∈ B_i, φ is differentiable at F_i(b) (φ is C¹) and F_i at b, so DΦ_i(b) = Dφ(F_i b)∘DF_i(b) (chain rule, fderiv_comp), which is injective as a composition of injective maps; Φ_i(B_i) ⊆ φ(M). Apply the sibling dpf_approxTangent_ae_bilipschitz_piece with Y := φ(M) (step 3) and (Φ_i, B_i, ΛL_i, m_i/Λ): for λ-a.e. b ∈ B_i, HasApproximateTangentSpaceAt n φ(M) (φ(F_i b)) (range(Dφ(F_i b)∘DF_i(b))), and range(Dφ(F_i b)∘DF_i(b)) = Dφ(F_i b)(range DF_i(b)) (LinearMap.range_comp, after ContinuousLinearMap.coe_comp).
5. Combination. By steps 2 and 4 there is a λ-null N_i ⊆ B_i such that for every b ∈ B_i ∖ N_i, x := F_i(b) satisfies HasApproximateTangentSpaceAt n M x Q(x) and, since Q(x) = range DF_i(b), HasApproximateTangentSpaceAt n φ(M) φ(x) (Dφ(x)(Q(x))).
6. Transfer to x. Every x ∈ M at which the conclusion fails lies in Z ∪ ⋃_i F_i(N_i) (an x ∈ P_i has the form F_i(b) with b ∈ B_i, and b ∈ N_i if the conclusion fails at x). H^n(Z) = 0 and H^n(F_i(N_i)) ≤ L_i^n H^n(N_i) = L_i^n λ(N_i) = 0. So the exceptional set is H^n-null, i.e. the conclusion holds for μHE[n]⌞M-a.e. x. (The argument is uniform in n ≥ 0; for n = 0 all planes are {0}.)

## Key steps

1. Decompose M into disjoint bi-Lipschitz pieces F_i(B_i) plus a null set (sibling bilipschitz_pieces).
2. The density lemma with Y = M gives T_{F_i b}M = range DF_i(b) for a.e. b, hence Q(F_i b) = range DF_i(b) by uniqueness.
3. φ(M) is Borel, contained in U and locally H^n-finite (φ bi-Lipschitz, φ^{-1}(U) = U).
4. The density lemma with Y = φ(M) and pieces φ∘F_i gives T_{φF_i b}φ(M) = Dφ(F_i b)(range DF_i(b)) for a.e. b.
5. Lipschitz images of λ-null parameter sets are H^n-null, so both statements hold H^n-a.e. on M.

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
