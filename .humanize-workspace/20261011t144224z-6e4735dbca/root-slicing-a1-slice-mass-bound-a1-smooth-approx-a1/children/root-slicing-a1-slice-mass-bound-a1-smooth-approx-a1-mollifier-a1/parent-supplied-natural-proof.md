# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollifier-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 4 (the mollifier ρ := (∫φ)⁻¹·φ for a `ContDiffBump` φ centred at 0 with outer radius σ). The packaged `ContDiffBump.normed` lives in `Mathlib.Analysis.Calculus.BumpFunction.Normed`, which the frozen `GMT.Ch06.Submission` does not import, so the normalisation is carried out explicitly below.

Setting. P ∈ ℕ and σ ∈ ℝ with σ > 0. ℝ^P is `Eucl P` with its Euclidean norm |·|. λ^P is Lebesgue measure (`volume` on `Eucl P`), an additive Haar measure that is positive on nonempty open sets.

1. (Smooth bump.) Since 0 < σ/2 and σ/2 < σ, there is a smooth bump function φ : ℝ^P → ℝ centred at 0 with inner radius σ/2 and outer radius σ. This is the structure `ContDiffBump (0 : Eucl P)` with `rIn := σ/2` and `rOut := σ`. It has the following standard properties:
   - φ is C^∞ (`ContDiffBump.contDiff`), in particular continuous (`ContDiffBump.continuous`);
   - φ(y) ≥ 0 for every y (`ContDiffBump.nonneg`);
   - φ has compact support (`ContDiffBump.hasCompactSupport`);
   - its support {y : φ(y) ≠ 0} is exactly the open ball B(0, σ) (`ContDiffBump.support_eq`).

2. (Integrability.) φ is continuous with compact support, hence λ^P-integrable (`Continuous.integrable_of_hasCompactSupport`).

3. (Positive mass.) Put c := ∫ φ dλ^P. Since φ ≥ 0 and φ is integrable, c > 0 holds if and only if λ^P({y : φ(y) ≠ 0}) > 0 (`integral_pos_iff_support_of_nonneg`). By step 1 this set is the open ball B(0, σ) with σ > 0, and λ^P(B(0, σ)) > 0 (`Metric.measure_ball_pos`; this holds in every dimension, including P = 0). Hence c > 0, so c ≠ 0 and c⁻¹ > 0.

4. (Definition.) Define ρ : ℝ^P → ℝ by ρ(y) := c⁻¹ · φ(y).

5. (Smoothness.) ρ is the product of the constant function c⁻¹ and the C^∞ function φ, hence C^∞ (`contDiff_const.mul`, i.e. `ContDiff.mul`).

6. (Compact support.) Wherever φ(y) = 0 we have ρ(y) = 0. So the support of ρ is contained in the support of φ, and ρ has compact support (`HasCompactSupport.mul_left`).

7. (Nonnegativity.) For every y, ρ(y) = c⁻¹ φ(y) ≥ 0, because c⁻¹ > 0 and φ(y) ≥ 0.

8. (Vanishing for |y| ≥ σ.) Let |y| ≥ σ. Then y ∉ B(0, σ) = {φ ≠ 0}, hence φ(y) = 0 (`Function.notMem_support`) and ρ(y) = c⁻¹ · 0 = 0.

9. (Unit integral.) ∫ ρ dλ^P = ∫ c⁻¹ φ dλ^P = c⁻¹ ∫ φ dλ^P = c⁻¹ · c = 1 (`integral_const_mul`, using c ≠ 0).

10. (Conclusion.) By steps 5–9, ρ is C^∞, has compact support, is nonnegative, vanishes whenever |y| ≥ σ, and satisfies ∫ρ dλ^P = 1. ∎

## Key steps

1. Take the ContDiffBump φ centred at 0 with radii σ/2 < σ: it is C^∞, nonnegative, compactly supported, and its support is exactly the open ball B(0, σ).
2. φ is integrable, and c = ∫φ > 0 because φ ≥ 0 and its support B(0, σ) has positive Lebesgue measure.
3. ρ := c⁻¹·φ is C^∞, compactly supported and nonnegative; ρ(y) = 0 for |y| ≥ σ because such y lie outside B(0, σ); and ∫ρ = c⁻¹·c = 1.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical); git show 2351f06fca407f3b56cb58e019903b5fcbbc5536:GMT/Ch06/Submission.lean (proof base = frozen contract, no helper lemmas); rg -n '^import' local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH); lean -o /tmp/smooth_approx_split_Usohr8/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `#check after import GMT.Ch06.Submission: IsCompact.exists_cthickening_subset_open, LipschitzOnWith.extend_real, Filter.EventuallyEq.fderiv_eq, LipschitzWith.ae_differentiableAt, hasFDerivAt_integral_of_dominated_loc_of_lip, HasCompactSupport.contDiff_convolution_left, convolution_def, ContDiffBump.{contDiff,continuous,nonneg,hasCompactSupport,support_eq}, measurable_fderiv, Measure.measurePreserving_sub_left, Measure.QuasiMeasurePreserving.ae, integral_pos_iff_support_of_nonneg, Metric.measure_ball_pos, norm_integral_le_of_norm_le, integral_const_mul, integral_mul_const, integral_sub, Function.notMem_support, Measurable.smul, LipschitzWith.of_dist_le_mul, HasCompactSupport.{mul_left,mul_right,abs} (all present); ContDiffBump.normed, ContDiffBump.integral_normed, ContDiffBump.dist_normed_convolution_le (unknown constants)`
- `rg -n 'theorem hasFDerivAt_integral_of_dominated_loc_of_lip|theorem LipschitzWith.ae_differentiableAt|contDiff_convolution_left|exists_cthickening_subset_open|theorem measurable_fderiv|structure ContDiffBump|theorem support_eq|def normed|theorem integral_pos_iff_support_of_nonneg|theorem norm_integral_le_of_norm_le|theorem measure_ball_pos|theorem ae|measurePreserving_div_left|theorem Filter.EventuallyEq.fderiv_eq|theorem convolution_def|theorem Continuous.integrable_of_hasCompactSupport|theorem HasCompactSupport.mul_right' local-references/197bdd4b88278494/mathlib/Mathlib`
- `sed -n 1,60p local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `rg -n -i 'mollif|convolution|ContDiffBump|ae_differentiableAt|hasFDerivAt_integral' lake-packages-25730c7c/simongmt/Poincare`
- `rg -n 'slicing_mb_sa_|mollifier_exists|mollify_lipschitz' local-references/197bdd4b88278494/project (no match)`
- `python3 scan of dag.json: children of root.slicing-a1.slice_mass_bound-a1; nodes mentioning ContDiffBump/convolution/mollif/Lipschitz/∫ ρ; lean_name uniqueness of the three proposed names (223 names, no collision)`
- `git grep -l -E 'slicing_mb_sa_|mollify_lipschitz|mollifier_exists' over all 638 refs -- GMT/Ch06/Submission.lean (no match)`
- `python3 gen.py using contract_scope/child_modules of verifier/gmt-compare.py; lean Challenge_slicing_mb_sa_mollifier_exists.lean, Challenge_slicing_mb_sa_mollify_lipschitz_close.lean, Challenge_slicing_mb_sa_mollify_lipschitz_hasFDerivAt.lean, Challenge_slicing_mb_smooth_approx.lean (only the expected sorry warning)`
- `lean /tmp/smooth_approx_split_Usohr8/check/Instances.lean (CLM smul and volume by rfl; C^∞ index ≠ ω; convolution identification; measure_ball_pos for all P)`
- `lean /tmp/smooth_approx_split_Usohr8/check/Assembly.lean (#print axioms HumanizeNodeComparator.assembly: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/smooth_approx_split_Usohr8/check/ChildA.lean, ChildB.lean, ChildC.lean (scratch proofs; axioms [propext, Classical.choice, Quot.sound])`
- `lean /tmp/smooth_approx_split_Usohr8/check/EndToEnd.lean (Submission.X declarations + comparator-style exact Submission.X for 3 children and the parent; standard axioms)`
- `sed -n 1395,1403p book/chapter-06.txt (Simon 4.11 closing sentence)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/smooth_approx_split_Usohr8/check/Challenge_slicing_mb_sa_mollifier_exists.lean`
- `/tmp/smooth_approx_split_Usohr8/check/Challenge_slicing_mb_sa_mollify_lipschitz_close.lean`
- `/tmp/smooth_approx_split_Usohr8/check/Challenge_slicing_mb_sa_mollify_lipschitz_hasFDerivAt.lean`
- `/tmp/smooth_approx_split_Usohr8/check/Challenge_slicing_mb_smooth_approx.lean`
- `/tmp/smooth_approx_split_Usohr8/check/Instances.lean`
- `/tmp/smooth_approx_split_Usohr8/check/Assembly.lean`
- `/tmp/smooth_approx_split_Usohr8/check/ChildA.lean`
- `/tmp/smooth_approx_split_Usohr8/check/ChildB.lean`
- `/tmp/smooth_approx_split_Usohr8/check/ChildC.lean`
- `/tmp/smooth_approx_split_Usohr8/check/EndToEnd.lean`
- `/tmp/smooth_approx_split_Usohr8/check/Names.lean`
- `/tmp/smooth_approx_split_Usohr8/check/Names2.lean`
- `/tmp/smooth_approx_split_Usohr8/check/Names3.lean`

Snapshot and workspace agree. The pinned snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract. It is byte-identical to the workspace Submission and to the proof base 2351f06f, which adds no helper lemmas. Child types may therefore use only contract, SimonGMT and Mathlib names reachable from `import GMT.Ch06.Submission`.

Available there (each name type-checks in a scratch file): McShane extension (`LipschitzOnWith.extend_real`), Rademacher (`LipschitzWith.ae_differentiableAt`), `hasFDerivAt_integral_of_dominated_loc_of_lip`, `HasCompactSupport.contDiff_convolution_left`, `convolution_def`, basic `ContDiffBump` (contDiff/nonneg/hasCompactSupport/support_eq), `measurable_fderiv`, `Measure.measurePreserving_sub_left` (to_additive of `measurePreserving_div_left`), `Measure.QuasiMeasurePreserving.ae`, `integral_pos_iff_support_of_nonneg`, `Metric.measure_ball_pos`, `norm_integral_le_of_norm_le` and `IsCompact.exists_cthickening_subset_open`.

Not available: `ContDiffBump.normed`, `integral_normed` and `dist_normed_convolution_le`, because BumpFunction/Normed.lean and BumpFunction/Convolution.lean are not imported. Mathlib's BumpFunction/SmoothApprox.lean gives only uniform smooth approximation without derivative control, and it is not imported either. SimonGMT offers only a Rademacher wrapper (Chapter02/Lipschitz.lean) and Chapter08 mollifiers built on the unimported normed bump. So neither library provides, under these imports, the normalized mollifier, the Lipschitz mollification error bound, or the derivative formula for mollified Lipschitz functions. These become the three children.

In the comparator's replayed child scope, the three child types and the parent type elaborate. The parent is proved from the three child types with axioms [propext, Classical.choice, Quot.sound]. Each child has a scratch proof with the same axioms, and the end-to-end Submission.X / `exact Submission.X` check passes.

No collisions: the proposed names occur neither in the snapshot project, nor among the 223 DAG lean_names, nor in GMT/Ch06/Submission.lean on any of the 638 git refs. No existing DAG node has an identical type; the constancy mollifier nodes concern iteratedFDeriv of convolutions with integrable or test functions.

Simon p. 158 (4.11) prints only "use f^{(σ)} in place of f", so the child proofs are extracted from the supplied Steps 4, 6 and 7.
