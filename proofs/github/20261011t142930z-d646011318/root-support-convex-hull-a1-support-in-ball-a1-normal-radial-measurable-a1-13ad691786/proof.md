# Parent-supplied natural-language proof

- Parent DAG node: `root.support_convex_hull-a1.support_in_ball-a1`
- Child DAG node: `root.support_convex_hull-a1.support_in_ball-a1.normal_radial_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. T_x := V.tangentSpace x, p_x := T_x.starProjection and p_x^⊥ := (T_x)ᗮ.starProjection (orthogonal projections, continuous linear maps E → E); μ := V.weight. By definition V.normalRadialSq ξ x = |p_x^⊥(x − ξ)|² / |x − ξ|², with real division (a/0 = 0). This is step 7(b) of the parent proof together with the bound 0 ≤ q ≤ 1 stated in the parent's conventions.

1. For every subspace T of the finite-dimensional space E, the orthogonal projection onto T^⊥ equals id − p_T (Mathlib Submodule.starProjection_orthogonal': Tᗮ.starProjection = 1 − T.starProjection). Hence x ↦ p_x^⊥ is the map x ↦ 1 − p_x, the difference of a constant map and the μ-a.e. strongly measurable map x ↦ p_x; so x ↦ p_x^⊥ is μ-a.e. strongly measurable.

2. Evaluation (L, v) ↦ L v is a continuous bilinear map (E →L[ℝ] E) × E → E (Mathlib ContinuousLinearMap.apply, used through ContinuousLinearMap.aestronglyMeasurable_comp₂). The map x ↦ x − ξ is continuous, hence μ-a.e. strongly measurable. Therefore x ↦ p_x^⊥(x − ξ) is μ-a.e. strongly measurable.

3. Composing with the continuous maps v ↦ |v| and s ↦ s², the map x ↦ |p_x^⊥(x − ξ)|² is μ-a.e. strongly measurable. The map x ↦ (|x − ξ|²)⁻¹ is Borel measurable (inversion ℝ → ℝ is measurable and x ↦ |x − ξ|² is continuous), hence μ-a.e. strongly measurable (ℝ is second countable). The product x ↦ |p_x^⊥(x − ξ)|² · (|x − ξ|²)⁻¹ is μ-a.e. strongly measurable, and it equals q(x) for every x, because a/b = a·b⁻¹ for all real a, b (including b = 0, where both sides are 0). Hence q is μ-a.e. strongly measurable.

4. Lower bound. For every x, the numerator |p_x^⊥(x − ξ)|² and the denominator |x − ξ|² are ≥ 0, and a quotient of nonnegative reals is ≥ 0; so q(x) ≥ 0.

5. Upper bound. If x = ξ then x − ξ = 0 and q(x) = 0/0 = 0 ≤ 1. If x ≠ ξ then |x − ξ|² > 0; orthogonal projections do not increase norms (Mathlib Submodule.norm_starProjection_apply_le), so |p_x^⊥(x − ξ)| ≤ |x − ξ|, hence |p_x^⊥(x − ξ)|² ≤ |x − ξ|² and q(x) ≤ 1. ∎

## Key steps

1. p_x^⊥ = 1 − p_x (Submodule.starProjection_orthogonal'), so x ↦ p_x^⊥ is μ-a.e. strongly measurable
2. x ↦ p_x^⊥(x − ξ) is μ-a.e. strongly measurable (continuous bilinear evaluation of an a.e.-measurable operator field at the continuous field x − ξ)
3. q(x) = |p_x^⊥(x − ξ)|² · (|x − ξ|²)⁻¹ pointwise, a product of a.e.-strongly measurable functions
4. 0 ≤ q ≤ 1: nonnegative quotient; q(ξ) = 0; |p_x^⊥ v| ≤ |v| for x ≠ ξ

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean; git -C <snapshot>/mathlib rev-parse HEAD`
- `rg -n 'lemma support_mem_ae\b|lemma subset_compl_support_of_isOpen|lemma support_subset_of_isClosed|lemma measure_compl_support\b' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'theorem IntegrableOn.of_ae_sdiff_eq_zero|theorem LocallyIntegrableOn.integrableOn_compact_subset|theorem integral_eq_zero_iff_of_nonneg_ae|theorem ContinuousLinearMap.aestronglyMeasurable_comp₂|lemma starProjection_orthogonal.|theorem norm_starProjection_apply_le|theorem contDiff_norm_sq|theorem Filter.EventuallyEq.fderiv_eq|theorem ContDiff.continuous_deriv' <snapshot>/mathlib/Mathlib`
- `rg -n 'protected theorem monotone|theorem zero_of_nonpos|theorem pos_of_pos|theorem nonneg|protected theorem contDiff' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean; rg -n 'lemma Monotone.deriv_nonneg' <snapshot>/mathlib/Mathlib; rg -n 'theorem one_of_mem_closedBall|protected theorem hasCompactSupport' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n 'theorem abs_real_inner_le_norm' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `rg -n 'AEStronglyMeasurable.inner' <snapshot-equivalent .lake/packages/mathlib>/Mathlib (found only in MeasureTheory/Function/StronglyMeasurable/Inner.lean, not imported by the contract: #check fails in comparator scope)`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/CompactSupportMaximum.lean; rg -n 'support_subset_closedBall_of_radial_lt|integral_eq_zero_iff_of_nonneg_ae|support_mem_ae|support_subset_of_isClosed' that file`
- `python3 -I scan of dag.json lean_names/lean_statements (normalRadialSq, IsTestField, support) and of every nodes/*/decomposition-v*.json and parent-child-handoff.json (reserved names; any stand-alone normalRadialSq measurability statement)`
- `rg -l --no-ignore -F -e exists_radial_cutoff_test_field -e aestronglyMeasurable_normalRadialSq_and_bounds -e support_subset_closedBall_of_radial_identity .humanize GMT simongmt/Poincare mathlib/Mathlib <snapshot>/project (no match)`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/sib-a1-split/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/sib-a1-split/olean lean /tmp/sib-a1-split/check/{Probe1,Probe2,Assembly1,ChildC1,ChildC2,ChildC3,Final,FinalSorry}.lean`
- `python3 -I verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch04.main_theorem'); verifier/lean_contract.py validate_lean_statement on the three child statements and the parent statement`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/CompactSupportMaximum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1-support-in-ball-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/sib-a1-split/check/Final.lean`
- `/tmp/sib-a1-split/check/FinalSorry.lean`
- `/tmp/sib-a1-split/check/Assembly1.lean`

Snapshot: project ff75f52, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b).

The snapshot Mathlib supplies every ingredient the three children need:
- Measure.support_mem_ae, measure_compl_support, subset_compl_support_of_isOpen and support_subset_of_isClosed (Measure/Support.lean).
- Submodule.starProjection_orthogonal' and norm_starProjection_apply_le (Projection/Basic.lean).
- ContDiffBump.one_of_mem_closedBall, hasCompactSupport and contDiff (BumpFunction/Basic.lean).
- expNegInvGlue.contDiff, monotone, nonneg, zero_of_nonpos and pos_of_pos (SmoothTransition.lean).
- Monotone.deriv_nonneg, ContDiff.continuous_deriv, Filter.EventuallyEq.fderiv_eq, contDiff_norm_sq and abs_real_inner_le_norm.
- LocallyIntegrableOn.integrableOn_compact_subset, IntegrableOn.of_ae_sdiff_eq_zero, integral_eq_zero_iff_of_nonneg_ae, ContinuousLinearMap.aestronglyMeasurable_comp₂, Integrable.of_bound and IsCompact.exists_bound_of_continuousOn.

AEStronglyMeasurable.inner is defined only in StronglyMeasurable/Inner.lean, which the contract does not import. The children therefore use continuous_inner.comp_aestronglyMeasurable instead.

The pinned SimonGMT Chapter04/CompactSupportMaximum.lean proves 6.1 only for SimonGMT's own varifold structure, using an expNegInvGlue/smoothTransition profile, integral_eq_zero_iff_of_nonneg_ae and support_subset_of_isClosed. It serves as a pattern only and is not reusable for the contract's RectifiableVarifold.

Nothing is reused from other DAG nodes:
- No declaration in the snapshot, project, SimonGMT or the DAG has any of the three child names (no matches).
- None of the 73 DAG nodes states normalRadialSq measurability on its own. weighted_mono_cutoff_first_variation embeds a restricted version inside a larger conclusion.
- weighted_mono_radial_test_field has different hypotheses: γ is constant near 0 and vanishes beyond b.

Lean checks against a freshly compiled Submission olean, in the comparator scope:
- All three child types elaborate and pass validate_lean_statement.
- All three are proved without sorry.
- The exact frozen parent type is proved from them.
- The comparator targets compile.
- #print axioms reports only propext, Classical.choice and Quot.sound.
