# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 9 of the parent proof; Simon 6.3.6–3.9 for injective f (chapter-06.txt lines 815–862: f_#T = τ(f(M), θ∘f^{-1}, η) with the induced orientation η of 3.5/3.7) and 6.2.24(3) (lines 426–440: for 1:1 f, f_#T(ω) = ∫_{f(M_+)} ⟨ω(y), η(y)⟩ dH^n by the area formula), with the details filled in. Notation: E := ℝ^P, H^n := μHE[n], μ := H^n⌞M, Q(x) := approxTangentPlane n M x, ψ := φ^{-1}; J(x) := sqrt(det(⟨Dφ(x)e_a, Dφ(x)e_b⟩)) with e = stdOrthonormalBasis ℝ Q(x) (the Jacobian of the siblings); ζ(x) := (R.orient x).comp (compContinuousLinearMapCLM (Dφ x)), i.e. ζ(x)(β) = ξ(x)(β∘Dφ(x)). Replacing Λ by max(Λ, 1) we assume Λ ≥ 1.
1. Facts on φ and ψ. ψ is Λ-Lipschitz (for y = φ(x), y' = φ(x'): |ψy − ψy'| = |x − x'| ≤ Λ|y − y'|), hence continuous and Borel measurable. φ(U) = U (φ^{-1}(U) = U and φ is surjective); for compact C ⊆ U, ψ(C) = φ^{-1}(C) is compact and ⊆ U. For every A ⊆ E, H^n(φ(A)) ≤ Λ^n H^n(A) and H^n(ψ(A)) ≤ Λ^n H^n(A) (LipschitzWith.hausdorffMeasure_image_le; μHE[n] is a fixed multiple of μH[n]). ‖Dφ(x)‖ ≤ Λ (norm_fderiv_le_of_lipschitz).
2. Local finiteness of M. θ ≥ 1 on M (R.mult_pos), so H^n(M ∩ C) ≤ ∫⁻_{M∩C} θ dH^n < ∞ for compact C ⊆ U (R.locallyIntegrable_mult).
3. Inputs. (G) By the sibling dpf_approxTangent_bilipschitz_image_ae (U open, M = R.carrier Borel ⊆ U, R.rectifiable, step 2, φ C¹ with injective derivatives, Λ-Lipschitz, Λ-antilipschitz, φ^{-1}(U) = U): for μ-a.e. x, HasApproximateTangentSpaceAt n M x Q(x) and HasApproximateTangentSpaceAt n φ(M) φ(x) (Dφ(x)Q(x)). (H) By the sibling dpf_area_formula_bilipschitz_rectifiable (φ injective): ∫⁻_{φ(M)} g dH^n = ∫⁻_M J(x) g(φ(x)) dH^n(x) for every g : E → [0, ∞]. (I) By the sibling dpf_aestronglyMeasurable_gramJacobian with μ, Q, L := Dφ (continuous, hence a.e. strongly measurable) and the projection hypothesis: J is μ-a.e. strongly measurable. (O) By R.orients: for μ-a.e. x there is Q' with HasApproximateTangentSpaceAt n M x Q' and IsUnitOrientationOf ξ(x) Q'.
 Let G ⊆ M be the set of x where (G) and (O) hold; H^n(M ∖ G) = 0. For x ∈ G, Q' = Q(x) by uniqueness (HasApproximateTangentSpaceAt.unique), so ξ(x) orients Q(x), and the sibling dpf_unitOrientation_map_gramNormalized (with ξ(x), Q(x), Dφ(x) injective, J = J(x)) gives 0 < J(x) ≤ ‖Dφ(x)‖^n ≤ Λ^n and IsUnitOrientationOf (J(x)^{-1} ζ(x)) (Dφ(x)Q(x)).
4. Definition of R'. Carrier M' := φ(M); multiplicity θ'(y) := θ(ψ(y)); orientation ξ'(y) := J(ψ(y))^{-1} • ζ(ψ(y)) (equal to 0 where J(ψ(y)) = 0, as 0^{-1} = 0).
5. The fields of IMRep. (a) M' = ψ^{-1}(M) (φ bijective) is Borel since ψ is continuous. (b) M' = φ(M) ⊆ φ(U) = U. (c) M' is countably n-rectifiable: if M ⊆ M₀ ∪ ⋃_j F_j(ℝ^n) as in CountablyRectifiable, then M' ⊆ φ(M₀) ∪ ⋃_j (φ∘F_j)(ℝ^n), H^n(φ(M₀)) ≤ Λ^n · 0 = 0 and φ∘F_j is Lipschitz. (d) θ' = θ∘ψ is measurable. (e) For y ∈ M', ψ(y) ∈ M, so θ'(y) = θ(ψ(y)) > 0. (f) Local integrability: for compact C ⊆ U, apply (H) to g := 1_C θ' (note θ'(φ(x)) = θ(x) and 1_C(φ(x)) = 1_{ψ(C)}(x)): ∫⁻_{M'∩C} θ' dH^n = ∫⁻_M J(x) 1_{ψ(C)}(x) θ(x) dH^n(x) ≤ Λ^n ∫⁻_{M∩ψ(C)} θ dH^n < ∞, using J ≤ Λ^n μ-a.e. (step 3) and R.locallyIntegrable_mult for the compact ψ(C) ⊆ U. (g) ξ' is a.e. strongly measurable for μ' := H^n⌞M': the map f(x) := J(x)^{-1} • ζ(x) is μ-a.e. strongly measurable (J by (I) and inversion on ℝ is measurable; ζ because ξ is μ-a.e. strongly measurable (R.aestronglyMeasurable_orient), Dφ is continuous and (ξ, L) ↦ ξ.comp (compContinuousLinearMapCLM L) is continuous, by ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM and continuity of composition). ψ is quasi-measure-preserving from μ' to μ: it is measurable, and for Borel A, μ'(ψ^{-1}(A)) = H^n(φ(M) ∩ φ(A)) = H^n(φ(M ∩ A)) ≤ Λ^n μ(A), so the image measure of μ' under ψ is absolutely continuous with respect to μ (it suffices to test measurable sets, Measure.AbsolutelyContinuous.mk). Hence ξ' = f∘ψ is μ'-a.e. strongly measurable (AEStronglyMeasurable.comp_quasiMeasurePreserving). (h) Orientation: for y ∈ φ(G), x := ψ(y) ∈ G, and by step 3 ξ'(y) = J(x)^{-1} ζ(x) is a unit orientation of Dφ(x)Q(x), which is an approximate tangent plane of M' at y = φ(x) by (G). M' ∖ φ(G) = φ(M ∖ G) has H^n-measure ≤ Λ^n · 0 = 0, so this holds for μ'-a.e. y. Thus R' := (M', θ', ξ') is an IMRep U n.
6. The action. Fix ω ∈ 𝒟^n(U); let h(y) := θ'(y) ξ'(y)(ω(y)) and g_ω(x) := θ(x) ξ(x)(ω(φ(x))∘Dφ(x)) = θ(x) ζ(x)(ω(φ(x))).
 (a) For x ∈ G: J(x) h(φ(x)) = J(x) θ(x) J(x)^{-1} ζ(x)(ω(φ(x))) = g_ω(x) since J(x) > 0 and ψ(φ(x)) = x. Since J ≥ 0, J·(h∘φ)⁺ = (g_ω)⁺, J·(h∘φ)⁻ = (g_ω)⁻ and J·|h∘φ| = |g_ω| μ-a.e. (positive and negative parts).
 (b) g_ω is μ-integrable: it is μ-a.e. strongly measurable (θ measurable, ξ μ-a.e. strongly measurable, x ↦ ω(φ(x))∘Dφ(x) continuous, evaluation continuous), and for μ-a.e. x, |g_ω(x)| ≤ θ(x)‖ω‖_∞ Λ^n 1_{ψ(tsupport ω)}(x) (|ξ(x)(β)| ≤ ‖β‖ because ξ(x) = ±evaluation at an orthonormal frame, by (O); ‖β∘L‖ ≤ ‖β‖‖L‖^n; ω(φ(x)) = 0 unless x ∈ ψ(tsupport ω), a compact subset of U), which is integrable by R.locallyIntegrable_mult.
 (c) h is μ'-integrable: it is μ'-a.e. strongly measurable (θ' measurable, ξ' a.e. strongly measurable by 5(g), ω continuous, evaluation continuous), and by (H) with g := ‖h‖₊ and (a), ∫⁻_{M'} |h| dH^n = ∫⁻_M J |h∘φ| dH^n = ∫⁻_M |g_ω| dH^n < ∞ by (b).
 (d) By (H) applied to g := ofReal(h⁺) and to g := ofReal(h⁻), and (a): ∫⁻_{M'} h^± dH^n = ∫⁻_M J (h∘φ)^± dH^n = ∫⁻_M (g_ω)^± dH^n. For integrable real functions ∫ f = ∫⁻ f⁺ − ∫⁻ f⁻ (integral_eq_lintegral_pos_part_sub_lintegral_neg_part), so R'.action(ω) = ∫_{M'} h dH^n = ∫_M g_ω dH^n = ∫_M θ(x) ξ(x)(ω(φ(x))∘Dφ(x)) dH^n(x).
7. Dimension zero needs no change: for n = 0, Q(x) = {0}, J = 1, β∘Dφ(x) = β for 0-covectors, so ζ = ξ and ξ' = ξ∘ψ.

## Key steps

1. ψ = φ^{-1} is Lipschitz, φ(U) = U, φ and ψ change H^n by at most Λ^n; θ ≥ 1 makes M locally H^n-finite.
2. Siblings give, a.e. on M: T_{φx}φ(M) = Dφ(x)T_xM, the area formula with J, a.e. measurability of J, and (with R.orients and uniqueness) 0 < J ≤ Λ^n and J^{-1}ζ orients Dφ(x)T_xM.
3. Define R' := (φ(M), θ∘ψ, (J^{-1}ζ)∘ψ) and verify every IMRep field (Borel, rectifiable, local integrability via the area formula, measurability via quasi-measure-preservation of ψ, a.e. orientation).
4. J·(h∘φ) = g_ω a.e. on M; the area formula on positive and negative parts gives R'.action ω = ∫_M g_ω.

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
