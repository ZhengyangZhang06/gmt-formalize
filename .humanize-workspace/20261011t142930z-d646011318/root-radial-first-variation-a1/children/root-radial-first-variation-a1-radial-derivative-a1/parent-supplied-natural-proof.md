# Parent-supplied natural-language proof

- Parent DAG node: `root.radial_first_variation-a1`
- Child DAG node: `root.radial_first_variation-a1.radial_derivative-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. n, ℓ ∈ ℕ; E = Ambient n ℓ = EuclideanSpace ℝ (Fin (n+ℓ)) = ℝ^{n+ℓ}, a finite-dimensional real inner product space with inner product ⟨·,·⟩ = inner ℝ and norm |·| = ‖·‖. Real division by 0 is 0 (Lean convention: a/0 = 0 for every a ∈ ℝ). γ'(t) denotes deriv γ t. innerSL ℝ w is the linear functional u ↦ ⟨w, u⟩; for a functional L and a vector w, L.smulRight w is the map u ↦ L(u)w; ContinuousLinearMap.id ℝ E is the identity I. HasFDerivAt g L x means g(x + v) = g(x) + L v + o(|v|) as v → 0 (Fréchet differentiability of g at x with derivative L). Notation: r = |x − ξ|, g(y) = γ(|y − ξ|)(y − ξ), and the claimed derivative is L_x(v) = γ(r)v + (γ'(r)/r)⟨x − ξ, v⟩(x − ξ).

1. Case x = ξ. Then r = 0 and x − ξ = 0. The coefficient γ'(0)/0 equals 0 and the vector x − ξ is 0, so the claimed derivative is L_ξ(v) = γ(0)v, i.e. L_ξ = γ(0)I. For v ∈ E we have g(ξ) = γ(0)·0 = 0 and g(ξ + v) = γ(|v|)v, hence g(ξ + v) − g(ξ) − γ(0)v = (γ(|v|) − γ(0))v.
2. γ is C¹, hence continuous, and |v| → 0 as v → 0; therefore ε(v) := γ(|v|) − γ(0) → 0 as v → 0. Consequently |g(ξ + v) − g(ξ) − γ(0)v| = |ε(v)|·|v| = o(|v|) as v → 0, which says exactly that g is Fréchet differentiable at ξ with derivative γ(0)I = L_ξ. This proves the claim when x = ξ.
3. Case x ≠ ξ, so r > 0. The map y ↦ y − ξ is differentiable at x with derivative I. The map y ↦ |y − ξ|² = ⟨y − ξ, y − ξ⟩ is differentiable at x with derivative v ↦ 2⟨x − ξ, v⟩ (product rule for the inner product). Since |x − ξ|² = r² > 0 and t ↦ √t is differentiable at every t > 0 with derivative 1/(2√t), the chain rule shows that y ↦ |y − ξ| = √(|y − ξ|²) is differentiable at x with derivative v ↦ (1/(2r))·2⟨x − ξ, v⟩ = r⁻¹⟨x − ξ, v⟩.
4. γ is C¹, so it is differentiable at r with derivative γ'(r) = deriv γ r. By the chain rule, φ(y) := γ(|y − ξ|) is differentiable at x with Dφ(x)v = γ'(r)·r⁻¹⟨x − ξ, v⟩.
5. By the product rule for a real-valued function times a vector-valued function, g(y) = φ(y)·(y − ξ) is differentiable at x with Dg(x)v = φ(x)·v + (Dφ(x)v)·(x − ξ) = γ(r)v + (γ'(r)/r)⟨x − ξ, v⟩(x − ξ) = L_x(v), using φ(x) = γ(r) and γ'(r)·r⁻¹ = γ'(r)/r. This proves the claim when x ≠ ξ, and with step 2 the lemma is proved.

## Key steps

1. At x = ξ the claimed derivative is γ(0)I because γ'(0)/0 = 0 and x − ξ = 0
2. g(ξ + v) − g(ξ) − γ(0)v = (γ(|v|) − γ(0))v = o(|v|) by continuity of γ at 0
3. For x ≠ ξ: y ↦ |y − ξ| = √(|y − ξ|²) has derivative r⁻¹⟨x − ξ, ·⟩ (chain rule with √ at r² > 0)
4. Chain rule: D[γ(|y − ξ|)](x) = γ'(r) r⁻¹⟨x − ξ, ·⟩
5. Product rule with y ↦ y − ξ (derivative I) gives Dg(x)v = γ(r)v + (γ'(r)/r)⟨x − ξ, v⟩(x − ξ)

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n "theorem trace_smulRight|theorem trace_eq_rank|IsProj.*trace|trace.*starProjection|trace_orthogonalProjection|theorem trace_comp_comm|theorem trace_id\b|theorem trace_one" <snapshot>/mathlib/Mathlib`
- `rg -n "IsProj|isProj" <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/ ; rg -n "starProjection_eq_self_iff|starProjection_inner_eq_zero|inner_starProjection_left_eq_right|norm_sq_eq_add_norm_sq_projection|starProjection_add_starProjection_orthogonal|starProjection_orthogonal_val" <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/*.lean`
- `rg -n "theorem HasFDerivAt.norm|theorem hasStrictFDerivAt_norm|theorem DifferentiableAt.norm |HasFDerivAt.sqrt|‖⁻¹ • innerSL" <snapshot>/mathlib/Mathlib ; rg -n "^theorem|^lemma" <snapshot>/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean`
- `rg -n "theorem support_fderiv_subset|theorem fderiv_of_notMem_tsupport|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem HasFDerivAt.smul |toDual_symm_apply|theorem setIntegral_congr_ae |theorem hasFDerivAt_iff_isLittleO_nhds_zero|theorem IsLittleO.smul_isBigO|theorem isLittleO_one_iff|theorem HasDerivAt.comp_hasFDerivAt |theorem ContDiff.differentiable |theorem image_eq_one_of_notMem_mulTSupport|theorem real_inner_smul_left" <snapshot>/mathlib/Mathlib`
- `rg -n "trace|starProjection|radial|hasFDerivAt.*norm|tangentialDiv" lake-packages-25730c7c/simongmt/Poincare ; rg -n "RadialVectorField|tangentialDivergence_smul|trace_radialEndomorphism" simongmt/Poincare/SimonGMT/Chapter04`
- `lake env lean /tmp/radial-fv-decomp/test/SimonAx.lean (#check and #print axioms of Poincare.SimonGMT.Chapter04.RectifiableVarifold.trace_radialEndomorphism, trace_starProjection, hasFDerivAt_squaredRadialVectorField)`
- `rg -n "radial_vector_field_hasFDerivAt|trace_scalar_add_rankOne_comp_starProjection|tangentialDiv_weighted_radial_field" <run dir> simongmt/Poincare <snapshot>/mathlib/Mathlib (and dag.json lean_name listing)`
- `grep -n "3.2|5.1|divM" book/chapter-04.txt`
- `python3 -I scope.py (verifier/gmt-compare.py contract_scope for GMT.Ch04.main_theorem) ; python3 -I validate.py (verifier/lean_contract.py validate_lean_statement on all four statements)`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/radial-fv-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/radial-fv-decomp/olean lean /tmp/radial-fv-decomp/final/Sim.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/LinearAlgebra/Projection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Norm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Asymptotics/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/tmp/radial-fv-decomp/final/Sim.lean`

Snapshot contract sha256 6e58e5dd…0f4770b is byte-identical to the workspace Contract.lean/Submission.lean (project ff75f52a, Mathlib 25730c7c). Every step of the split exists in the snapshot Mathlib: LinearMap.trace_smulRight, LinearMap.IsProj.trace, LinearMap.trace_id (LinearAlgebra/Trace.lean); Submodule.starProjection_apply_mem, starProjection_eq_self_iff, inner_starProjection_left_eq_right, norm_sq_eq_add_norm_sq_starProjection (InnerProductSpace/Projection/Basic.lean); HasFDerivAt.norm_sq, HasFDerivAt.sqrt, HasDerivAt.comp_hasFDerivAt, HasFDerivAt.fun_smul, hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_one_iff, IsLittleO.smul_isBigO; InnerProductSpace.toDual_symm_apply (gradient); fderiv_of_notMem_tsupport, image_eq_zero_of_notMem_tsupport, setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_congr_ae, real_inner_smul_left. Mathlib has no HasFDerivAt lemma for the norm at a nonzero point (FDeriv/Norm.lean only has scaling lemmas), so child 1 goes through √(|y−ξ|²); SimonGMT Chapter04/FirstVariation.lean avoids the centre by using a squared-radius field (hasFDerivAt_squaredRadialVectorField), so the radius-r derivative at x = ξ is genuinely new (child 1), while its trace_radialEndomorphism (axioms propext, Classical.choice, Quot.sound) is child 2 with b = 1 (it is not imported by the contract). The three child names have no match in the run directory, dag.json, SimonGMT or Mathlib. The four statements pass verifier/lean_contract.py, and in the replayed contract scope (open MeasureTheory Metric Set Filter Topology; open scoped ENNReal ContDiff CompactlySupported; namespace GMT.Ch04; noncomputable section; open RectifiableVarifold) /tmp/radial-fv-decomp/final/Sim.lean declares Submission.radial_vector_field_hasFDerivAt, Submission.trace_scalar_add_rankOne_comp_starProjection, Submission.tangentialDiv_weighted_radial_field and the parent Submission.radial_first_variation (parent proved from child 3 only) with exactly these types, plus comparator-style `exact Submission.X` targets; lean exits 0 with no errors, only deprecation warnings, and #print axioms gives [propext, Classical.choice, Quot.sound] for all four. An independent reviewer rebuilt the olean, re-ran Sim.lean and confirmed it.
