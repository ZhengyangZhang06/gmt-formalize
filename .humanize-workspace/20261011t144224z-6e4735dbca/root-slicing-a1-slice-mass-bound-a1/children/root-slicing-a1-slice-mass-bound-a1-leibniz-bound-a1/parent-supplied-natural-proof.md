# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 4(a) (Simon Ch. 6, 4.11: ∂T(γ∘f ω) − T(γ∘f dω) = T(γ′(f) df∧ω)) combined with the representation estimate (**) of Step 1 and the wedge estimate of Step 3(iv), for an arbitrary smooth multiplier ψ in place of γ∘f_σ.

Setting. P, m ∈ ℕ; U ⊆ ℝ^P; T ∈ D_{m+1}(U) (GeometricCurrentOn U (m+1)); μ a Borel measure on ℝ^P and v : ℝ^P → Λ_{m+1}(ℝ^P) with IsMeasureRepresentation T μ v, i.e. for every η ∈ D^{m+1}(U) the function x ↦ v(x)(η(x)) is μ-integrable and T(η) = ∫ v(x)(η(x)) dμ(x); and |v(x)(α)| ≤ |α| for every x and every (m+1)-covector α, where |·| = covectorEuclideanNorm. ω ∈ D^m(U) (C^∞, compact support, tsupport ω ⊆ U) and ψ : ℝ^P → ℝ is C^∞. Write dω := exteriorDerivative ω and Dψ(x) := fderiv ℝ ψ x. For a continuous linear functional ℓ on ℝ^P and an m-covector γ write ℓ∧γ := alternatizeUncurryFin(ℓ.smulRight γ).

1. (Three forms.) Define, for x ∈ ℝ^P,
 η₁(x) := ψ(x)·ω(x),  η₂(x) := ψ(x)·dω(x),  η₃(x) := Dψ(x) ∧ ω(x) = alternatizeUncurryFin((Dψ(x)).smulRight(ω(x))).

2. (They are test forms.) Notation: support φ := {x : φ(x) ≠ 0} is the ordinary support of a form φ and tsupport φ := closure(support φ) its topological support.
 (a) (Smoothness.) ψ, ω and dω are C^∞ (dω by `exteriorDerivative_isTestForm`, which also gives that dω has compact support), and Dψ is C^∞ (`ContDiff.fderiv_right`). η₁ and η₂ are products of C^∞ maps under the continuous bilinear scalar multiplication (`ContDiff.smul`), and η₃ is the image of the C^∞ map x ↦ (Dψ(x)).smulRight(ω(x)) (`ContDiff.smulRight`) under the continuous linear map alternatizeUncurryFin (`ContinuousAlternatingMap.alternatizeUncurryFinCLM`); hence η₁, η₂ and η₃ are C^∞.
 (b) (Supports of η₁ and η₃.) If ω(x) = 0 then η₁(x) = ψ(x)·0 = 0 and η₃(x) = alternatizeUncurryFin((Dψ(x)).smulRight 0) = alternatizeUncurryFin(0) = 0. Hence support η₁ ⊆ support ω and support η₃ ⊆ support ω. Taking closures (`closure_mono`), tsupport η₁ ⊆ tsupport ω and tsupport η₃ ⊆ tsupport ω, and η₁, η₃ have compact support because ω has (`HasCompactSupport.mono`).
 (c) (Support of η₂.) If dω(x) = 0 then η₂(x) = ψ(x)·0 = 0. Hence support η₂ ⊆ support(dω). Taking closures, tsupport η₂ ⊆ tsupport(dω), and tsupport(dω) ⊆ tsupport ω (`tsupport_exteriorDerivative_subset`), so tsupport η₂ ⊆ tsupport ω. η₂ has compact support because dω has (part (a); `HasCompactSupport.mono` with support η₂ ⊆ support(dω)); alternatively, tsupport η₂ is a closed subset of the compact set tsupport ω. No inclusion of support η₂ in the ordinary support of ω is claimed or used, since ω(x) = 0 does not force dω(x) = 0. For example, take P ≥ 1 and m = 0, and let ω be a compactly supported smooth function equal to the first coordinate y₁ near 0; then ω(0) = 0 but dω(0) = dy₁ ≠ 0.
 (d) Consequently, for i = 1, 2, 3, η_i is C^∞ with compact support and tsupport η_i ⊆ tsupport ω ⊆ U. Therefore η₁ ∈ D^m(U) and η₂, η₃ ∈ D^{m+1}(U), and η₁, η₂ have exactly the pointwise formulas η₁(x) = ψ(x)·ω(x), η₂(x) = ψ(x)·dω(x) required in the statement.

3. (Leibniz rule.) At every x, the product rule (`fderiv_fun_smul`) gives D(ψω)(x) = ψ(x)·Dω(x) + (Dψ(x)).smulRight(ω(x)). Since the exterior derivative is d = alternatizeUncurryFin ∘ D (`extDeriv`) and alternatizeUncurryFin is linear (`ContinuousAlternatingMap.alternatizeUncurryFin_add`, `ContinuousAlternatingMap.alternatizeUncurryFin_smul`),
 dη₁(x) = ψ(x)·dω(x) + alternatizeUncurryFin((Dψ(x)).smulRight(ω(x))) = η₂(x) + η₃(x).
So the test forms dη₁ and η₂ + η₃ are equal.

4. (Boundary identity.) By the definition of the boundary (∂T(η) = T(dη)) and linearity of T: ∂T(η₁) = T(dη₁) = T(η₂ + η₃) = T(η₂) + T(η₃). Hence ∂T(η₁) − T(η₂) = T(η₃).

5. (Representation bound.) By IsMeasureRepresentation, T(η₃) = ∫ v(x)(η₃(x)) dμ with integrable integrand, so in [0,∞]: ofReal|T(η₃)| ≤ ∫⁻ ofReal|v(x)(η₃(x))| dμ(x) (the absolute value of an integral is at most the integral of the absolute value). By the normalization, |v(x)(η₃(x))| ≤ |η₃(x)| for every x.

6. (Wedge bound.) By the sibling `slicing_mb_wedge_norm_le` applied with α := Dψ(x) and γ := ω(x): |η₃(x)| = covectorEuclideanNorm(alternatizeUncurryFin((Dψ(x)).smulRight(ω(x)))) ≤ ‖Dψ(x)‖·|ω(x)|.

7. (Conclusion.) Combining steps 4–6: ofReal|∂T(η₁) − T(η₂)| = ofReal|T(η₃)| ≤ ∫⁻ ofReal(‖Dψ(x)‖·|ω(x)|) dμ(x) = ∫⁻ ‖Dψ(x)‖₊·ofReal(|ω(x)|) dμ(x). Together with step 2 (η₁(x) = ψ(x)ω(x), η₂(x) = ψ(x)dω(x)) this is the claim. ∎

## Key steps

1. η₁ = ψω, η₂ = ψ dω and η₃ = alternatizeUncurryFin((Dψ).smulRight ω) are C^∞. support η₁ ⊆ support ω and support η₃ ⊆ support ω, while support η₂ ⊆ support dω, so tsupport η₂ ⊆ tsupport dω ⊆ tsupport ω. Compact supports come from ω and dω, so all three are test forms in U.
2. Product rule and linearity of alternatizeUncurryFin: dη₁ = η₂ + η₃, so ∂T(η₁) − T(η₂) = T(η₃).
3. Representation and normalization: ofReal|T(η₃)| ≤ ∫⁻ ofReal|η₃(x)| dμ.
4. Sibling slicing_mb_wedge_norm_le: |η₃(x)| ≤ ‖Dψ(x)‖·|ω(x)|.

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
