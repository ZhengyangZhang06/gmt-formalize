# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: items 2.6 (rectifiable representation of smooth push-forwards: g_#X(ω) = X(η) = ∫_M θ⟨ω(g(x)), Dg(x)_#ξ(x)⟩ dH^k, using H^k(M ∖ spt X) = 0) and 5.9 (integrality of Lipschitz push-forwards through the premise (S5′); parent I.7) of the supplied proof of deformation_pushforward_homotopy. The premise (S5′) of this child is verbatim the premise of the parent statement (the conclusion of the sibling deformation_im_pushforward_limit after its premise LipschitzPushforwardIntegerMultiplicity).

Notation. As in the sibling lipschitz_pushforward: locally admissible sequences (G_n, O, L) and the property LipPF(X, G, S) of the statement; A_ρ := thickening ρ A; H^k := μHE[k]. Reused facts: (R3) compatible_form (iwl_sp_exists_compatible_testForm); (R5) support_null (iwl_sp_rectifiable_support_null): if IsRectifiableTriple U k M θ ξ and T(ω) = tauAction k M θ ξ ω for all ω, then H^k(M ∖ spt T) = 0; sibling smooth_approx (N1).

1. (Representation.) X is integer multiplicity: there are M, θ, ξ with IsRectifiableTriple univ k M θ ξ, θ(x) ∈ ℕ for x ∈ M (as ∃ j : ℕ, θ x = j) and X(ω) = tauAction k M θ ξ ω for all ω.

2. (Approximations.) Apply smooth_approx (N1) with A := spt X and δ := r: there are Ĝ : ℝ^m → ℝ^{m′}, L ≥ 0 and maps G_n with Ĝ L-Lipschitz, Ĝ = G on (spt X)_r, each G_n C^∞ and L-Lipschitz, G_n → Ĝ uniformly on ℝ^m, and ‖DG_n(x)‖ ≤ Λ for x ∈ O₀ := (spt X)_{r/2}. Since Ĝ = G on O₀, (G_n, O₀, Λ) is locally admissible for (X, G) (O₀ open, spt X ⊆ O₀, uniform convergence to G on O₀).

3. (Apply (S5′).) Ĝ is L-Lipschitz, and Ĝ⁻¹(K) ∩ spt X = G⁻¹(K) ∩ spt X is compact for compact K (Ĝ = G on spt X ⊆ (spt X)_r). Applying (S5′) to P := m, Q := m′, k, X, (M, θ, ξ), g := Ĝ, Λ := L gives S′ ∈ D_k(ℝ^{m′}) with IsIntegerMultiplicity S′ and: for every sequence (g_n) of C¹ maps with a common Lipschitz bound converging uniformly to Ĝ and every ω, ∫_M θ(x)·nVectorPushforward k (Dg_n(x)) (ξ(x)) (ω(g_n x)) dH^k(x) → S′(ω). Take g_n := G_n: C^∞ implies C¹ (ContDiff.of_le), the common Lipschitz bound is L, and G_n → Ĝ uniformly. Hence for every ω:
 (∗) I_n(ω) := ∫_M θ(x)·nVectorPushforward k (DG_n(x)) (ξ(x)) (ω(G_n x)) dH^k(x) → S′(ω).

4. (Rectifiable formula, 2.6.) Choose n₀ with |G_n − G| ≤ 1 on spt X for n ≥ n₀ (uniform convergence on O₀ ⊇ spt X). For n ≥ n₀, G_n is proper on spt X (G_n⁻¹(K) ∩ spt X is closed and contained in the compact G⁻¹(cthickening 1 K) ∩ spt X), so (R3) (U = V = univ, A = spt X) gives, for each ω, a form η_n ∈ D^k(ℝ^m) compatible with (G_n, ω) near spt X, on an open N_n ⊇ spt X. By (R5), H^k(M ∖ spt X) = 0, so for H^k-a.e. x ∈ M we have x ∈ spt X ⊆ N_n and
 η_n(x) = ω(G_n x).compContinuousLinearMap(DG_n(x)) = covectorPullback k (DG_n(x)) (ω(G_n x)),
 hence ξ(x)(η_n(x)) = (ξ(x) ∘ covectorPullback k (DG_n(x)))(ω(G_n x)) = nVectorPushforward k (DG_n(x)) (ξ(x)) (ω(G_n x)) by the definition nVectorPushforward k L w = w.comp (covectorPullback k L). Therefore (integral_congr_ae for the measure H^k⌞M)
 X(η_n) = tauAction k M θ ξ η_n = ∫_M θ(x)ξ(x)(η_n(x)) dH^k(x) = I_n(ω) (n ≥ n₀).

5. (Identification.) For n ≥ n₀ the η_n are compatible with (G_n, ω) near spt X, so LipPF(X, G, S) applied to the locally admissible (G_n, O₀, Λ) gives X(η_n) → S(ω) (set η_n := 0 for n < n₀; compatibility is only required eventually). By step 4 and (∗), X(η_n) = I_n(ω) → S′(ω). Limits in ℝ are unique, so S(ω) = S′(ω) for all ω, S = S′ (GeometricCurrentOn.ext), and S is integer multiplicity. ∎

## Key steps

1. smooth_approx on (spt X)_r gives a Lipschitz extension Ĝ and C^∞ maps G_n → Ĝ uniformly with a common Lipschitz bound and ‖DG_n‖ ≤ Λ near spt X; they are locally admissible for (X, G).
2. (S5′) for (X, M, θ, ξ, Ĝ) gives an integer multiplicity S′ with ∫_M θ⟨ω(G_n), DG_n#ξ⟩ dH^k → S′(ω).
3. 2.6: for η_n compatible with (G_n, ω) near spt X, X(η_n) equals that integral because H^k(M ∖ spt X) = 0 (support_null) and ξ(η_n) = nVectorPushforward k (DG_n) ξ (ω∘G_n) on spt X.
4. LipPF gives X(η_n) → S(ω); hence S = S′ is integer multiplicity.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sed -n 1,364p GMT/Ch06/Contract.lean; diff GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical): IsRectifiableTriple, tauAction, IsIntegerMultiplicity, IsLipschitzPushforward, scope namespace GMT.Ch06 with its opens`
- `grep -n '^structure|^def|^abbrev|^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality,FormsDuality,Product,GeometricPointProduct,ParametricCurrentContinuity,AffineCurrentPushforward}.lean: GeometricCurrentOn (sequential continuity at 0), TestFormOnConverges, boundary = T ∘ exteriorDerivativeTestOn, massOn = sSup over covectorEuclideanNorm ≤ 1, support = U \ zeroRegion, covectorPullback = compContinuousLinearMapCLM, nVectorPushforward n L w = w.comp (covectorPullback n L), SimonMultiIndex = Fin n ↪o Fin p. Only point products {p}×T on E × F and affine push-forwards exist; there are no products with [[0,1]] in Eucl (m+1), no Lipschitz push-forward of normal currents and no homotopy formula`
- `grep -n 'def CountablyRectifiable|def HasWeightedApproximateTangentSpaceAt|def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (lines 34, 330, 96)`
- `sed -n 180,275p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (Filter.EventuallyEq.extDeriv_eq, extDeriv_apply, extDeriv_pullback)`
- `grep for the library inputs cited in the child proofs: weighted_area_formula_lipschitz_injOn, areaRegularSet, measurableSet_areaRegularSet, area_image_compl_regularSet_eq_zero (simongmt Chapter02/AreaLipschitz.lean:101,31,34,59); measurable_areaJacobianAt (AreaApproximation.lean:44); exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Mathlib/MeasureTheory/Function/Jacobian.lean:255); MeasurableSet.image_of_continuousOn_injOn (Constructions/Polish/Basic.lean:821); LinearMap.normDet_sq_eq_det_gram (InnerProductSpace/NormDet.lean:303); LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308); HasCompactSupport.contDiff_convolution_left (Calculus/ContDiff/Convolution.lean:427); exists_contDiff_tsupport_subset (BumpFunction/FiniteDimension.lean:45); norm_fderiv_le_of_lipschitzOn (FDeriv/Basic.lean:939); intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148). All found`
- `python3 over dag.json (645 nodes): statuses, lean_names, depends_on and candidate commits of the deformation subtree and of all push-forward/product/homotopy/cutoff/mollifier/slice/hausdorff nodes. Also the isolated-comparator-result.json of the five reused nodes (passed) and the accepted status of every declaration that the child proofs name as reusable later`
- `python3: byte comparison of the hausdorff_product proof, key steps, lean_statement, title and statement with nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json (identical)`
- `git show --stat 0bfba9891418f887822d6878214d8c1c46326aaa; git show 0bfba989:GMT/Ch06/Submission.lean | grep iwl_cr_hp_ (the accepted Lean proof of the identical statement and its four sub-lemmas are present)`
- `rg 'dph_' over GMT/, the local reference project snapshot and simongmt; python3 over dag.json lean_names; git grep 'dph_' over the 1581 distinct commits of all 3680 local refs (no match)`
- `read /runtime/flows/*/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, child activation by Lean name, accepted reused children without handoff) and store.py (Store.update refreshes the shared DAG). Attempt 1's name check ran on a DAG view taken when its attempt started, before the hausdorff node was accepted`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on all 12 child statements and the parent statement (all valid); verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem) for the exact child-comparator scope`
- `lake env lean /tmp/dph2/lean/AllStmts.lean: the 12 child statements and the parent statement, each as `theorem _root_.HumanizeNodeComparator.target_<key> : (stmt) := by sorry` after the replayed scope (EXIT 0, 13 sorry warnings, no errors)`
- `lake env lean /tmp/dph2/lean/IfaceCheck.lean: attempt-1 interface check whose hypotheses are byte-identical to the current lipschitz_pushforward and smooth_homotopy statements (clause (8), tail/cons, (E1) and (Aff) instantiations); EXIT 0, no errors`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-slice-forms-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dph2/lean/AllStmts.lean`
- `/tmp/dph2/lean/IfaceCheck.lean`

The pinned project and SimonGMT have no push-forward of normal currents, no products with [[0,1]] in Eucl (m+1) and no homotopy formula (only point products on E × F and affine push-forwards), so Parts 1–5 of the supplied proof are new obligations. Five comparator-accepted declarations with no sibling prerequisites cover facts that the supplied proof uses as black boxes, and they are reused by name with byte-identical types: cmb_abs_apply_le_of_massOn_le (F1), isoperimetric_apply_eq_zero_of_disjoint_support (F2), iwl_sp_exists_compatible_testForm (2.1), iwl_cr_ci_slice_testForm (3.1 slices) and iwl_sp_rectifiable_support_null (F9, same type as lpf_rectifiable_support_null). The product formula 3.5(b) becomes the fresh child dph_hausdorff_product_formula, as attempt 1's correction requires; its type is identical to the accepted iwl_cr_hausdorff_product_formula, its proof is that node's accepted proof verbatim, and its accepted Lean code and four accepted sub-declarations can be reused. iwl_cr_interval_product_im (unaccepted) and iwl_smooth_pushforward (integer multiplicity only) are not reused. Every library lemma cited in the child proofs exists in the pinned snapshot. All 12 child statements and the parent elaborate in the exact comparator scope. The seven new names are globally unique, and the Lean interface check of the parent's operator plumbing recompiles against the current statements.
