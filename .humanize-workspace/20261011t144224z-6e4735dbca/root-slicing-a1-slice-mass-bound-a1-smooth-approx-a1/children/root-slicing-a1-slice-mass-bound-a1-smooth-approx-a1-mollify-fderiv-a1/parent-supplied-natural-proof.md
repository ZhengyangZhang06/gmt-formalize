# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollify_fderiv-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 7, in the Fréchet form recorded there: "the Fréchet version `hasFDerivAt_integral_of_dominated_loc_of_lip`, applied to x′ ↦ ρ(y)f̃(x′ − y) near x with the Lipschitz bound Lρ(y), gives Dg(x) = ∫ ρ(y)·Df̃(x − y) dy directly". Step 7(a)–(c) supplies the hypotheses. The statement here allows an arbitrary globally Lipschitz F, an arbitrary continuous compactly supported ρ and an arbitrary point x, since Step 7 uses neither x ∈ K nor ρ ≥ 0.

Setting.
- P ∈ ℕ; L ≥ 0 and F : ℝ^P → ℝ with |F(a) − F(b)| ≤ L|a − b| for all a, b ∈ ℝ^P (`LipschitzWith L F`).
- ρ : ℝ^P → ℝ continuous with compact support; x ∈ ℝ^P.
- DF(z) := fderiv ℝ F z, an element of the Banach space ℝ^P →L[ℝ] ℝ (equal to 0 where F is not differentiable).
- Integrals are with respect to Lebesgue measure λ^P (`volume` on `Eucl P`). Integrals of (ℝ^P →L[ℝ] ℝ)-valued functions are Bochner integrals.
- G(x′) := ∫ ρ(y)F(x′ − y) dy.

1. (Rademacher, translated.) F is Lipschitz on the finite-dimensional space ℝ^P and λ^P is an additive Haar measure. By Rademacher's theorem (`LipschitzWith.ae_differentiableAt`), F is differentiable at λ^P-a.e. z ∈ ℝ^P. The map τ(y) := x − y preserves λ^P (`Measure.measurePreserving_sub_left`: Lebesgue measure is invariant under y ↦ −y and under translations). Hence τ is quasi-measure-preserving, and almost-everywhere statements pull back along it (`Measure.QuasiMeasurePreserving.ae`). Therefore, for λ^P-a.e. y, F is differentiable at x − y.

2. (The data.) For x′, y ∈ ℝ^P put
   - Φ(x′, y) := ρ(y)F(x′ − y),
   - Φ′(y) := ρ(y)·DF(x − y) ∈ ℝ^P →L[ℝ] ℝ,
   - b(y) := L·|ρ(y)|.
   (a) (Measurability and integrability of Φ.) For every x′, y ↦ Φ(x′, y) is continuous, because ρ and F are continuous and y ↦ x′ − y is continuous. Hence it is a.e.-strongly measurable. The function y ↦ Φ(x, y) vanishes wherever ρ vanishes, so it is continuous with compact support (`HasCompactSupport.mul_right`) and therefore integrable (`Continuous.integrable_of_hasCompactSupport`).
   (b) (Measurability of Φ′.) DF : ℝ^P → (ℝ^P →L[ℝ] ℝ) is measurable for every function F (`measurable_fderiv`). Also y ↦ x − y is measurable, ρ is continuous hence measurable, and scalar multiplication ℝ × (ℝ^P →L[ℝ] ℝ) → (ℝ^P →L[ℝ] ℝ) preserves measurability (`Measurable.smul`). Hence Φ′ is measurable, in particular a.e.-strongly measurable.
   (c) (Lipschitz in the parameter.) For every y and all a, a′ ∈ ℝ^P:
       |Φ(a, y) − Φ(a′, y)| = |ρ(y)|·|F(a − y) − F(a′ − y)| ≤ |ρ(y)|·L·|(a − y) − (a′ − y)| = L|ρ(y)|·|a − a′|.
       So x′ ↦ Φ(x′, y) is Lipschitz on all of ℝ^P with constant |b(y)| = L|ρ(y)|.
   (d) (Integrable majorant.) b = L·|ρ| is continuous and vanishes wherever ρ does. So it has compact support (`Continuous.abs`, `HasCompactSupport.abs`) and is integrable (`Continuous.integrable_of_hasCompactSupport`, `Integrable.const_mul`).
   (e) (Pointwise derivative.) Let y be such that F is differentiable at x − y.
       - The map x′ ↦ x′ − y has derivative the identity at x (`hasFDerivAt_sub_const`).
       - F has derivative DF(x − y) at x − y (`DifferentiableAt.hasFDerivAt`).
       - By the chain rule (`HasFDerivAt.comp`), x′ ↦ F(x′ − y) has derivative DF(x − y) ∘ id = DF(x − y) at x.
       - Multiplying by the constant ρ(y) multiplies the derivative by ρ(y) (`HasFDerivAt.const_mul`).
       Thus x′ ↦ Φ(x′, y) has Fréchet derivative Φ′(y) at x. By step 1 this holds for λ^P-a.e. y.

3. (Differentiation under the integral sign.) Apply the theorem on differentiating a parametric integral with a Lipschitz majorant (`hasFDerivAt_integral_of_dominated_loc_of_lip`) to Φ, Φ′ and b at the point x, with the neighbourhood s := ℝ^P of x. Its hypotheses are exactly:
   - Φ(x′, ·) is a.e.-strongly measurable for x′ near x, and Φ(x, ·) is integrable (step 2(a));
   - Φ′ is a.e.-strongly measurable (step 2(b));
   - for a.e. y, x′ ↦ Φ(x′, y) is Lipschitz on s with constant |b(y)| (step 2(c), valid for every y);
   - b is integrable (step 2(d));
   - for a.e. y, x′ ↦ Φ(x′, y) has derivative Φ′(y) at x (step 2(e)).
   Inside that theorem, dominated convergence is applied to the difference quotients, which are bounded by |b(y)| by step 2(c). The theorem yields that Φ′ is integrable and that G = (x′ ↦ ∫ Φ(x′, y) dy) has Fréchet derivative ∫ Φ′(y) dy = ∫ ρ(y)·DF(x − y) dy at x.

4. (Conclusion.) The function x′ ↦ ∫ ρ(y)F(x′ − y) dy has Fréchet derivative ∫ ρ(y)·DF(x − y) dy at x. Since x was arbitrary, this holds at every x ∈ ℝ^P. ∎

## Key steps

1. Rademacher plus invariance of Lebesgue measure under y ↦ x − y: F is differentiable at x − y for a.e. y.
2. Φ(x′, y) = ρ(y)F(x′ − y) is continuous in y with compact support (so Φ(x, ·) is integrable), and Φ′(y) = ρ(y)·DF(x − y) is measurable by measurable_fderiv.
3. For every y, x′ ↦ Φ(x′, y) is L|ρ(y)|-Lipschitz on ℝ^P with integrable majorant L|ρ|; for a.e. y it has derivative ρ(y)·DF(x − y) at x by the chain rule.
4. hasFDerivAt_integral_of_dominated_loc_of_lip with s = ℝ^P gives HasFDerivAt (x′ ↦ ∫ρ(y)F(x′ − y)dy) (∫ρ(y)·DF(x − y)dy) x.

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
