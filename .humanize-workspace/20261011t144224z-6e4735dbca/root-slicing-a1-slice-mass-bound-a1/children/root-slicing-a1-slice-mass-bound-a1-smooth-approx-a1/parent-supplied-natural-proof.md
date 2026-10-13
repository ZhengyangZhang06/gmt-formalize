# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 3(i)–(iii) (McShane extension, mollification f_σ = ρ_σ * f̃, Rademacher, and the gradient bound obtained by differentiating under the integral sign), i.e. the closing sentence of Simon Ch. 6, 4.11 (“use f^{(σ)} in place of f”), specialized to a compact set K ⊆ W.

Setting. P ∈ ℕ; W ⊆ ℝ^P open; f : ℝ^P → ℝ with |f(x) − f(y)| ≤ L|x − y| for x, y ∈ W; LW ≥ 0 with ‖Df(x)‖ ≤ LW for Lebesgue-a.e. x ∈ W, where Df(x) := fderiv ℝ f x (which is 0 at points where f is not differentiable); K ⊆ W compact; δ > 0. Lebesgue measure on ℝ^P is denoted λ^P.

1. (Room around K.) Since K is compact, W is open and K ⊆ W, there is r > 0 such that the closed r-neighbourhood K_r := {z : dist(z, K) ≤ r} is contained in W (`IsCompact.exists_cthickening_subset_open`). (If K = ∅ any r > 0 works.)

2. (McShane extension.) By `LipschitzOnWith.extend_real` there is f̃ : ℝ^P → ℝ with |f̃(x) − f̃(y)| ≤ L|x − y| for all x, y ∈ ℝ^P and f̃ = f on W.

3. (Derivatives of f̃ on W.) For z ∈ W, f̃ and f agree on the open neighbourhood W of z, hence Df̃(z) = Df(z) (`Filter.EventuallyEq.fderiv_eq`). Consequently the set N₂ := {z ∈ W : ‖Df̃(z)‖ > LW} = {z ∈ W : ‖Df(z)‖ > LW} is λ^P-null by hypothesis. By Rademacher's theorem (`LipschitzWith.ae_differentiableAt`), f̃ is differentiable at every point outside a λ^P-null set N₁.

4. (Mollification.) Choose σ with 0 < σ < r and Lσ ≤ δ (e.g. σ := min(r/2, δ/(L+1))). Let ρ : ℝ^P → ℝ be C^∞ with ρ ≥ 0, ρ(y) = 0 for |y| ≥ σ, and ∫ρ dλ^P = 1 (e.g. ρ := (∫φ)⁻¹·φ for a `ContDiffBump` φ centred at 0 with outer radius σ; `ContDiffBump.normed` is the same construction but needs `import Mathlib.Analysis.Calculus.BumpFunction.Normed`). Define g(x) := ∫ ρ(y) f̃(x − y) dy (= (ρ ⋆ f̃)(x)).

5. (Smoothness.) ρ is C^∞ with compact support and f̃ is continuous, hence locally integrable, so g = ρ ⋆ f̃ is C^∞ on ℝ^P (`HasCompactSupport.contDiff_convolution_left`).

6. (Uniform closeness.) For every x, using ∫ρ = 1, ρ ≥ 0 and ρ(y) = 0 for |y| ≥ σ: |g(x) − f̃(x)| = |∫ρ(y)(f̃(x − y) − f̃(x)) dy| ≤ ∫ρ(y)·L|y| dy ≤ Lσ ≤ δ (this direct estimate suffices; `ContDiffBump.dist_normed_convolution_le` is the packaged version and needs `import Mathlib.Analysis.Calculus.BumpFunction.Convolution`). For x ∈ K ⊆ W, f̃(x) = f(x), hence |g(x) − f(x)| ≤ δ.

7. (Directional derivatives of g.) Fix x ∈ K and e ∈ ℝ^P. For s ∈ ℝ, g(x + se) = ∫ F(s, y) dy with F(s, y) := ρ(y) f̃(x + se − y). (a) For each y, s ↦ F(s, y) is Lipschitz with constant L|e|ρ(y), since |F(s, y) − F(s′, y)| ≤ ρ(y)·L|s − s′||e|; the function y ↦ L|e|ρ(y) is integrable. (b) F(0, ·) is continuous with compact support, hence integrable, and each F(s, ·) is continuous, hence measurable; y ↦ ρ(y)·Df̃(x − y)e is measurable (`measurable_fderiv`). (c) The map y ↦ x − y preserves λ^P, so {y : x − y ∈ N₁} is null; for every other y, f̃ is differentiable at x − y and s ↦ F(s, y) has derivative ρ(y)·Df̃(x − y)e at s = 0. By the theorem on differentiation under the integral sign with a Lipschitz domination (`hasDerivAt_integral_of_dominated_loc_of_lip`; dominated convergence for the difference quotients, which are bounded by L|e|ρ(y)), s ↦ g(x + se) is differentiable at s = 0 with derivative ∫ ρ(y) Df̃(x − y)e dy. Since g is differentiable at x (step 5), this derivative is Dg(x)e. Hence Dg(x)e = ∫ ρ(y) Df̃(x − y)e dy. (Equivalently, the Fréchet version `hasFDerivAt_integral_of_dominated_loc_of_lip`, applied to x′ ↦ ρ(y)f̃(x′ − y) near x with the Lipschitz bound Lρ(y), gives Dg(x) = ∫ ρ(y)·Df̃(x − y) dy directly.)

8. (Bound.) If ρ(y) ≠ 0 then |y| < σ < r, so x − y ∈ K_r ⊆ W. The set {y : x − y ∈ N₂} is null (measure preservation as in 7(c)); for all other y with ρ(y) ≠ 0 we have x − y ∈ W \ N₂, i.e. ‖Df̃(x − y)‖ ≤ LW. Therefore |Dg(x)e| ≤ ∫ρ(y)|Df̃(x − y)e| dy ≤ ∫ρ(y)·LW|e| dy = LW|e|.

9. (Operator norm.) Step 8 holds for every e ∈ ℝ^P, so ‖Dg(x)‖ ≤ LW (`ContinuousLinearMap.opNorm_le_bound`) for every x ∈ K.

10. (Conclusion.) g is C^∞ (step 5), |g(x) − f(x)| ≤ δ for x ∈ K (step 6) and ‖Dg(x)‖ ≤ LW for x ∈ K (step 9). ∎

## Key steps

1. Choose r > 0 with the closed r-neighbourhood of K inside W; McShane-extend f|W to a globally L-Lipschitz f̃; Df̃ = Df on W, so ‖Df̃‖ ≤ LW a.e. on W, and f̃ is differentiable a.e. (Rademacher).
2. g := ρ ⋆ f̃ with a normalized C^∞ bump ρ supported in the σ-ball, σ < r, Lσ ≤ δ: g is C^∞ and |g − f̃| ≤ Lσ ≤ δ, with f̃ = f on K.
3. Differentiation under the integral sign with Lipschitz domination: Dg(x)e = ∫ρ(y)Df̃(x−y)e dy for x ∈ K.
4. For ρ(y) ≠ 0, x − y ∈ W, and translation/reflection invariance of Lebesgue measure gives |Dg(x)e| ≤ LW|e|, hence ‖Dg(x)‖ ≤ LW on K.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical)`
- `rg -n 'slicing_mb_' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'theorem norm_deriv_le_of_lipschitz|theorem LipschitzOnWith.extend_real|theorem LipschitzWith.ae_differentiableAt|theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegrable_deriv|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem liminf_const_mul_of_ne_top|theorem hasDerivAt_integral_of_dominated_loc_of_lip|HasCompactSupport.contDiff_convolution_left|theorem alternatizeUncurryFin_apply|theorem tendsto_measure_biInter_gt|theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq|theorem fderiv_fun_smul|theorem ofReal_integral_eq_lintegral_ofReal|theorem tendsto_integral_filter_of_dominated_convergence' local-references/197bdd4b88278494/mathlib/Mathlib/{Analysis,Order,MeasureTheory,Topology,LinearAlgebra}`
- `grep -n 'covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|abbrev Covector|abbrev DifferentialForm|def IsTestForm|abbrev exteriorDerivative|abbrev TestFormOn|structure GeometricCurrentOn|boundary_apply|tsupport_exteriorDerivative_subset|abbrev NVector' simongmt/Poincare/SimonGMT/Chapter06/{Mass,Forms,Currents,FormsDuality}.lean`
- `python3 scan of dag.json (200 nodes): lean_name uniqueness of the seven proposed names; search of titles/statements/lean_statements for alternatizeUncurryFin, smulRight, liminf, Monotone, cut-off, mollif, wedge, Dini, McShane, Rademacher (no identical type)`
- `python3 read of nodes/root-slicing-a1-slice-mass-bound-a1/{parent-child-handoff.json, decomposition-v3.json, decomposition-audit-v1..v4.json, decomposition-review-receipt-v1..v4.json}`
- `python3 read of .humanize/swarm-configs/*.json for github_selected_issue 676: 97b6c024c2834d99b1a86982198ed548.json max_nodes=1000 max_depth=6 (older 9bd566bbce374e36839dbfed5b2a4b01.json max_nodes=200)`
- `contract_scope/child_modules in verifier/gmt-compare.py (replayed child scope)`
- `lake env printenv LEAN_PATH; lean -o /tmp/smb_split_v5_bWB45t/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean /tmp/smb_split_v5_bWB45t/check/Stmts.lean (7 child types + parent in the comparator child scope: 0 errors)`
- `lean /tmp/smb_split_v5_bWB45t/check/Instances.lean (wedge degree m+1, operator norms by rfl, C^∞ index)`
- `lean /tmp/smb_split_v5_bWB45t/check/Assembly.lean (#print axioms HumanizeNodeComparator.assembly: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/smb_split_v5_bWB45t/check/Plumbing.lean (dependency instantiations type-check)`
- `lean /tmp/smb_split_v5_bWB45t/check/Names.lean (#check of every lemma cited in the child proofs)`
- `sed -n '1340,1415p' book/chapter-06.txt (Simon Ch. 6, 4.6–4.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/97b6c024c2834d99b1a86982198ed548.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/smb_split_v5_bWB45t/check/Stmts.lean`
- `/tmp/smb_split_v5_bWB45t/check/Instances.lean`
- `/tmp/smb_split_v5_bWB45t/check/Assembly.lean`
- `/tmp/smb_split_v5_bWB45t/check/Plumbing.lean`
- `/tmp/smb_split_v5_bWB45t/check/Names.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and it is byte-identical to the workspace Submission, so child types may use only contract, SimonGMT and Mathlib names. SimonGMT supplies GeometricCurrentOn with boundary ∂T(ω) = T(dω), massOn via covectorEuclideanNorm, TestFormOn, exteriorDerivative (Mathlib's extDeriv, i.e. alternatizeUncurryFin ∘ fderiv) and tsupport_exteriorDerivative_subset. Mathlib supplies McShane extension (LipschitzOnWith.extend_real), Rademacher's theorem (LipschitzWith.ae_differentiableAt), convolution smoothness, differentiation under the integral, Lebesgue's theorem for monotone functions with the integral bound for their derivative, liminf algebra in ℝ≥0∞, dominated convergence along countably generated filters and continuity from above. Every cited name exists at the pinned revision. Neither library contains the sharp cut-off, the wedge coefficient-norm bound, the smooth approximation with an a.e. gradient bound, the slice estimates or the Dini-derivative majorant; these become the seven children. In a scratch compile of the frozen Submission, all seven child types and the parent type elaborate in the comparator's child scope. The exact parent follows from slicing_mass_representation, slicing_representation_unique, slicing_mb_pointwise and slicing_mb_density_majorant with axioms [propext, Classical.choice, Quot.sound], and the dependency instantiations type-check. No proposed name occurs in the snapshot project or among the 200 DAG nodes. The active issue-676 configuration allows 1000 nodes at depth ≤ 6. The printed Simon text (4.9–4.11) matches the supplied proof.
