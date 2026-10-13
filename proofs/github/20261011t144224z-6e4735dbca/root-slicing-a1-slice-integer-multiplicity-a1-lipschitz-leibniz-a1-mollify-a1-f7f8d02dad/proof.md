# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.mollify-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P, ℝⁿ = Eucl n; Hᵏ := μHE[k] (Mathlib's Euclidean Hausdorff measure, equal to Lebesgue measure Lᵏ = volume on ℝᵏ); |·| is the Euclidean norm and ⟨·,·⟩ the inner product; Df(x) := fderiv ℝ f x (the Fréchet derivative where it exists and 0 otherwise). Source: parent proof, Step 3 (mollification h_σ := ρ_σ * h), with σ = σ_k := 1/(k+1). Lᴾ := volume on ℝ^P is translation invariant and invariant under y ↦ −y.
1. (Mollifiers.) For k ∈ ℕ put σ_k := 1/(k+1) > 0. Choose ρ_k : ℝ^P → ℝ which is C^∞, has compact support, satisfies ρ_k ≥ 0, ρ_k(y) = 0 whenever |y| ≥ σ_k, and ∫ ρ_k dLᴾ = 1. For instance take the smooth bump function φ_k centred at 0 with inner radius σ_k/2 and outer radius σ_k (Mathlib `ContDiffBump`, support = open ball B_{σ_k}(0), values in [0,1], equal to 1 on the closed ball of radius σ_k/2) and ρ_k := φ_k/∫φ_k dLᴾ (Mathlib `ContDiffBump.normed`); ∫φ_k > 0 because φ_k is continuous, ≥ 0 and positive on a ball of positive measure. (Mathlib facts: `ContDiffBump.contDiff_normed`, `hasCompactSupport_normed`, `nonneg_normed`, `integral_normed`, `support_normed_eq`; these need the extra import Mathlib.Analysis.Calculus.BumpFunction.Normed, which a submission may add.)
2. (Definition.) g_k(x) := ∫ ρ_k(y) h(x − y) dLᴾ(y), i.e. g_k = ρ_k ⋆ h, the convolution with respect to the bilinear map (a, b) ↦ a·b (`ContinuousLinearMap.lsmul ℝ ℝ`). For fixed x the integrand y ↦ ρ_k(y)h(x − y) is continuous and vanishes outside the compact support of ρ_k, hence is Lᴾ-integrable (`HasCompactSupport.convolutionExists_left`, h being continuous and so locally integrable).
3. (Smoothness.) h is continuous, hence locally integrable; ρ_k is C^∞ with compact support. The convolution of a C^∞ compactly supported function with a locally integrable function is C^∞ (`HasCompactSupport.contDiff_convolution_left`, Lᴾ being translation and negation invariant). So g_k is C^∞.
4. (Lipschitz.) For x, x' ∈ ℝ^P, by linearity of the integral (both integrands are integrable by step 2), ρ_k ≥ 0 and the Lipschitz bound for h: |g_k(x) − g_k(x')| = |∫ ρ_k(y)(h(x − y) − h(x' − y)) dy| ≤ ∫ ρ_k(y)|h(x − y) − h(x' − y)| dy ≤ ∫ ρ_k(y) L|x − x'| dy = L|x − x'|, using ∫ρ_k = 1. So g_k is L-Lipschitz.
5. (Uniform error.) Fix x. Since ∫ρ_k = 1, g_k(x) − h(x) = ∫ ρ_k(y)(h(x − y) − h(x)) dy. If ρ_k(y) ≠ 0 then |y| < σ_k and |h(x − y) − h(x)| ≤ L|y| ≤ Lσ_k. Hence |g_k(x) − h(x)| ≤ ∫ ρ_k(y)Lσ_k dy = Lσ_k = L/(k+1) (Mathlib `ContDiffBump.dist_normed_convolution_le` with the bound dist(h(y), h(x)) ≤ Lσ_k on B_{σ_k}(x)).
6. (Uniform convergence.) Let ε > 0 and choose k₀ ∈ ℕ with k₀ > L/ε. For k ≥ k₀ and every x, |g_k(x) − h(x)| ≤ L/(k+1) < ε. Hence g_k → h uniformly on ℝ^P (TendstoUniformly g h atTop).
7. (Conclusion.) Steps 3, 4 and 6 give the three required properties. ∎
(This proof has been checked in Lean 4 / Mathlib 25730c7c in the exact comparator scope, with the extra imports Mathlib.Analysis.Calculus.BumpFunction.Normed, …BumpFunction.Convolution and …ContDiff.Convolution; axioms propext, Classical.choice, Quot.sound.)

## Key steps

1. Normalized smooth bumps ρ_k ≥ 0 with ∫ρ_k = 1 and support in B_{1/(k+1)}(0).
2. g_k := ρ_k ⋆ h is C^∞ (convolution of a compactly supported C^∞ function with a continuous function).
3. |g_k(x) − g_k(x')| ≤ ∫ρ_k(y)|h(x−y) − h(x'−y)|dy ≤ L|x − x'|.
4. |g_k(x) − h(x)| ≤ ∫ρ_k(y)L|y|dy ≤ L/(k+1), so g_k → h uniformly.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read GMT/Ch06/Contract.lean (IsRectifiableTriple, tauAction, IsMeasureRepresentation) and replay its scope with verifier/gmt-compare.py contract_scope(…, 'GMT.Ch06.main_theorem')`
- `python3 scan of dag.json (458 nodes at submission): statuses/lean_statements of slicing_mb_lb_extDeriv_smul, slicing_mb_lb_smul_testForm, slicing_mb_lb_wedge_testForm (accepted), slicing_mb_sa_* (accepted), lpf_raf_chart_change_of_variables, lpf_ccr_hasDerivAt_line_of_comp, lpf_tde_chart_directional_deriv, lpf_ccr_ae_pullback, lpf_raf_chart_preimage_null (accepted), lpf_countably_rectifiable_c1_cover, lpf_weighted_tangent_on_c1_chart (speculative-ready), rectifiability_weighted_tangent_ae (accepted); collision check for slicing_im_ll_* (none)`
- `rg 'slicing_im_ll' local-references/197bdd4b88278494 and lake-packages-25730c7c/simongmt (no match)`
- `git show <candidate>:GMT/Ch06/Submission.lean for the 203 accepted candidates: 8 add Mathlib/SimonGMT imports (allowed by the comparator)`
- `grep Mathlib: LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt (Rademacher.lean), measurable_fderiv, norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.extend_real, MemLp.exist_eLpNorm_sub_le (Normed/Lp/SmoothApprox.lean), exists_contDiff_support_eq_eq_one_iff, tendsto_tsum_of_dominated_convergence (Normed/Group/Tannery.lean), integral_iUnion_ae, HasCompactSupport.contDiff_convolution_left, ContDiffBump.normed/dist_normed_convolution_le, alternatizeUncurryFin_apply, norm_alternatizeUncurryFin_le, InnerProductSpace.toDual_symm_apply, Submodule.orthogonal_orthogonal, VitaliFamily.ae_tendsto_lintegral_enorm_sub_div, Besicovitch.vitaliFamily`
- `read SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt(.unique)), Chapter06/{Forms,Currents,FormsDuality}.lean (exteriorDerivative, TestFormOn, GeometricCurrentOn.boundary_apply, exteriorDerivativeTestOn, simpleNVector_apply), Chapter02/AreaLipschitz.lean (weighted_area_formula_lipschitz_injOn)`
- `sed book/chapter-06.txt Lemma 4.5 printed proof (eqs (1)–(3)); chapter-03.txt 1.1–1.6; chapter-02.txt 4.5–4.14; chapter-01.txt 3.6–3.7, 3.15, 3.23`
- `lake env lean /tmp/lleib_split/check/Stmts.lean (six child types in the exact comparator scope: no errors)`
- `lake env lean /tmp/lleib_split/check/Assembly.lean (parent type from five child types; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/lleib_split/check/C3.lean (smooth_identity from the three reused frozen types; same axioms)`
- `lake env lean /tmp/lleib_split/check/{C1,C2}.lean (full proofs of mollify and multiplier_limit; same axioms)`
- `lake env lean /tmp/lleib_split/check/C4.lean (full proof of tangent_field, type byte-identical; same axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-extderiv-leibniz-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-smul-test-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-wedge-test-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/lleib_split/check/Stmts.lean`
- `/tmp/lleib_split/check/Assembly.lean`
- `/tmp/lleib_split/check/C3.lean`
- `/tmp/lleib_split/check/C1.lean`
- `/tmp/lleib_split/check/C2.lean`
- `/tmp/lleib_split/check/C4.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract. Child types therefore use only contract, SimonGMT and Mathlib names; all six new types elaborate in the exact comparator scope. Three accepted declarations of the slice-mass-bound branch have exactly the types the smooth Leibniz identity needs (slicing_mb_lb_extDeriv_smul, slicing_mb_lb_smul_testForm, slicing_mb_lb_wedge_testForm), so they are reused with byte-identical types. The C¹-chart cover and the C¹-chart tangent identification exist only as speculative-ready lpf nodes, so they are not reused; tangential_weak_limit proves them inside its natural proof. The chart change of variables and the directional-derivative lemmas are accepted (lpf_raf_chart_change_of_variables, lpf_ccr_hasDerivAt_line_of_comp) and are cited. Mathlib supplies Rademacher, integration by parts for Lipschitz functions, density of C_c^∞ in L¹, a smooth Urysohn function, Tannery's theorem, convolution smoothness, normalized bumps and Besicovitch differentiation. SimonGMT supplies the injective Lipschitz area formula and the uniqueness of weighted tangent planes. Neither library has a weak-convergence lemma for tangential gradients on rectifiable sets. Accepted candidates show that extra imports in Submission.lean pass the comparator. Scratch Lean checks prove: the parent type from five child types, smooth_identity from the three reused types, and mollify, multiplier_limit and tangent_field in full; all print axioms propext, Classical.choice, Quot.sound. No proposed new name occurs in the snapshot, SimonGMT or the DAG.
