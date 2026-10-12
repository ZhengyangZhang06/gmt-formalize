# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.abs_variation-a1`
- Child DAG node: `root.bv_results-a1.abs_variation-a1.smoothed_abs-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. Fix n, w : Rn n → ℝ with ContDiff ℝ 1 w, and η with 0 < η. For t ∈ ℝ put ψ(t) := √(t² + η²) − η. The function in the statement, F := fun x ↦ √(w x ^ 2 + η ^ 2) − η, equals ψ ∘ w.

1. (Positivity.) For every t ∈ ℝ, t² + η² ≥ η² > 0. So t² + η² ≠ 0 and √(t² + η²) > 0 (Real.sqrt_pos).

2. (Lower bound.) For every t, |t| ≤ √(t² + η²). Indeed |t| = √(t²) (Real.sqrt_sq_eq_abs) and t² ≤ t² + η², so monotonicity of the square root (Real.sqrt_le_sqrt) gives the claim.

3. (Upper bound.) For every t, √(t² + η²) ≤ |t| + η. Indeed (|t| + η)² = t² + 2|t|η + η² ≥ t² + η², using |t|² = t², |t| ≥ 0 and η > 0. Hence √(t² + η²) ≤ √((|t| + η)²) = |t| + η, by Real.sqrt_le_sqrt and by Real.sqrt_sq with |t| + η ≥ 0.

4. (Conjunct (c).) Fix x and put t := w x. By step 2, F x − |t| = √(t² + η²) − |t| − η ≥ −η. By step 3, F x − |t| ≤ 0 ≤ η. Hence abs (F x − |w x|) ≤ η (abs_le).

5. (Conjunct (a).) The map x ↦ w x ^ 2 is C¹ (ContDiff.pow), and adding the constant η² keeps it C¹. By step 1 the result never vanishes. ContDiff.sqrt needs only a nowhere-vanishing C¹ argument, so x ↦ √(w x ^ 2 + η ^ 2) is C¹. Subtracting the constant η keeps it C¹ (ContDiff.sub with contDiff_const).

6. (Conjunct (b).) Fix x and put t₀ := w x.
 - The scalar map t ↦ t² + η² has derivative 2t₀ at t₀ (HasDerivAt.pow for the identity, then add_const).
 - Its value at t₀ is nonzero by step 1. HasDerivAt.sqrt then shows t ↦ √(t² + η²) has derivative c := 2t₀ / (2√(t₀² + η²)) at t₀. Subtracting η does not change the derivative (sub_const), so ψ has derivative c at t₀.
 - w is C¹ and 1 ≠ 0, so w is differentiable (ContDiff.differentiable). Hence HasFDerivAt w (fderiv ℝ w x) x.
 - By the chain rule HasDerivAt.comp_hasFDerivAt, ψ ∘ w has Fréchet derivative c • fderiv ℝ w x at x. So fderiv ℝ F x = c • fderiv ℝ w x and ‖fderiv ℝ F x‖ = |c| · ‖fderiv ℝ w x‖ (norm_smul).
 - Finally |c| = |t₀| / √(t₀² + η²) ≤ 1, by step 2 and because the denominator is positive (step 1; div_le_one).
 Therefore ‖fderiv ℝ F x‖ ≤ 1 · ‖fderiv ℝ w x‖ = ‖fderiv ℝ w x‖.

7. Steps 5, 6 and 4 give the three conjuncts (a), (b) and (c) of the statement. ∎

## Key steps

1. t² + η² > 0, and |t| ≤ √(t²+η²) ≤ |t| + η for all real t.
2. Hence |F(x) − |w(x)|| ≤ η pointwise.
3. F = √(w² + η²) − η is C¹ by ContDiff.sqrt, since the radicand never vanishes.
4. Chain rule: DF(x) = (w(x)/√(w(x)²+η²))·Dw(x). The coefficient has absolute value ≤ 1, so ‖DF(x)‖ ≤ ‖Dw(x)‖.

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json`
- `cmp local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean workspaces/gmt-ch02/GMT/Ch02/Contract.lean; diff GMT/Ch02/Contract.lean GMT/Ch02/Submission.lean`
- `grep -n 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem setIntegral_eq_integral_of_ae_compl_eq_zero' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -n 'theorem contDiff_normed|theorem nonneg_normed|theorem support_normed_eq|theorem integral_normed|def normed|^variable' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean; grep -n instance BumpFunction/InnerProduct.lean BumpFunction/FiniteDimension.lean`
- `grep -n 'contDiff_convolution_left|contDiff_convolution_right' mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `grep -rn 'theorem HasFDerivAt.sqrt|theorem HasDerivAt.sqrt|theorem ContDiff.sqrt|theorem HasDerivAt.comp_hasFDerivAt|theorem enorm_integral_le_lintegral_enorm|theorem ContDiff.differentiable' (Analysis/SpecialFunctions/Sqrt.lean, Analysis/Calculus/Deriv/Comp.lean, MeasureTheory/Integral/Bochner/Basic.lean, Analysis/Calculus/ContDiff/Defs.lean)`
- `grep -rn -E '(theorem|lemma) (_root_\.)?(IsCompact\.cthickening|IsCompact\.exists_cthickening_subset_open|mem_thickening_iff|thickening_mono|cthickening_mono|self_subset_thickening|thickening_subset_cthickening)' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `grep -n 'setLIntegral_const|setLIntegral_mono'|setLIntegral_le_lintegral|lintegral_indicator|lintegral_add_left|integrable_indicator_iff|tendsto_one_div_add_atTop_nhds_zero_nat|Filter.Tendsto.div_atTop' (MeasureTheory/Integral/Lebesgue/{Basic,Add}.lean, MeasureTheory/Integral/IntegrableOn.lean, Analysis/SpecificLimits/Basic.lean, Topology/Algebra/Order/Field.lean)`
- `full read of simongmt/Poincare/SimonGMT/Chapter02/BV.lean; grep -rn bvVariationOn simongmt/Poincare (only Chapter02/BV.lean); grep -rln -E 'bvVariationOn_mono|variation.*mono|ContDiffBump|normed volume|mollif' simongmt/Poincare and snapshot project`
- `python3 -I dag.json listing of every node id/lean_name/status/depends_on; lean_name/lean_statement of every nodes/*/decomposition-v1.json; Submission.* references in depth-2/3 decompositions (no child cites an uncle declaration)`
- `grep -rl {bv_abs_variation_mono_set, bv_abs_variation_exists_kernel, bv_abs_variation_smoothed_abs, bv_variationOn_mono, bvVariationOn_mono} run dir; git grep over all 96 refs/heads+refs/remotes in GMT/Ch02/*.lean`
- `python3 -I gen_checks.py (verifier gmt-compare.py child_modules/contract_scope + lean_contract.validate_lean_statement) then lean NodeChallenge_00..02.lean against a scratch olean of GMT.Ch02.Submission`
- `lean Sanity.lean and Sanity2.lean (proofs of the 3 children + #print axioms); lean Assembly.lean (sibling frozen types + child types as hypotheses ⊢ frozen parent type; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-abs-variation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1/decomposition-review-receipt-v1.json`
- `/tmp/absvar-decomp-sLwtA8/checks/NodeChallenge_00.lean`
- `/tmp/absvar-decomp-sLwtA8/checks/NodeChallenge_01.lean`
- `/tmp/absvar-decomp-sLwtA8/checks/NodeChallenge_02.lean`
- `/tmp/absvar-decomp-sLwtA8/checks/Sanity.lean`
- `/tmp/absvar-decomp-sLwtA8/checks/Sanity2.lean`
- `/tmp/absvar-decomp-sLwtA8/checks/Assembly.lean`

Snapshot and contract:
- The manifest pins project commit 1b1689a and Mathlib 25730c7c.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean, and the workspace Submission.lean equals the Contract.

What SimonGMT provides (Chapter02/BV.lean):
- Definitions: bvVariationOn, euclideanDivergence, compactlySupportedSupNorm.
- Lemmas: support_euclideanDivergence_subset, norm_euclideanDivergence_le_of_lipschitz, measurable_euclideanDivergence, ofReal_integral_le_bvVariationOn, tendsto_integral_mul_of_lintegral_sub.

What is missing, so is a new obligation:
- No monotonicity of bvVariationOn in the domain.
- No general mollifier-kernel existence lemma in the frozen import closure. Chapter08's constancyMollifier is outside the closure and specialized.

Mathlib provides what the children need:
- setIntegral_eq_integral_of_forall_compl_eq_zero, which needs no measurability of the set.
- ContDiffBump.normed with contDiff_normed, nonneg_normed, support_normed_eq and integral_normed, plus the hasContDiffBump_of_innerProductSpace instance. These need the imports BumpFunction.Normed and BumpFunction.InnerProduct, which are outside the frozen closure but compile when added.
- ContDiff.sqrt, HasDerivAt.sqrt, HasDerivAt.comp_hasFDerivAt, and ContDiff.differentiable (n ≠ 0 form).
The parent assembly additionally uses HasCompactSupport.contDiff_convolution_left, IsCompact.exists_cthickening_subset_open, IsCompact.cthickening, mem_thickening_iff and enorm_integral_le_lintegral_enorm.

Lean checks against a scratch olean of GMT.Ch02.Submission:
- All three child types pass validate_lean_statement and compile as comparator-generated NodeChallenge modules in the replayed contract scope.
- Scratch proofs of the three children compile with axioms [propext, Classical.choice, Quot.sound].
- An assembly theorem takes the frozen types of bv_lipschitz_integration_by_parts, bv_mollifier_tendsto_L1, bv_mollifier_fderiv_lintegral_le and the three child types as hypotheses. It proves the exact frozen parent type, with the same axioms.

Collisions: the three proposed names occur nowhere in dag.json, in any node file, or in any of the 96 branch refs.
