# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.smooth_form_approx-a1.continuous_l1_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0(a), 0(b), 0(d), 1 (C_c approximation), 2 and 3 of the parent proof of regcomp_exists_smooth_unit_form_approx, with final tolerance ε instead of ε/4. The integrability of g, which the parent derives in step 1 from 0(c), is a hypothesis here. Uses the sibling lemma regcomp_covectorEuclideanNorm_seminorm_retract. Implementation note: Integrable.exists_hasCompactSupport_lintegral_sub_le lives in Mathlib.MeasureTheory.Function.ContinuousMapDense, which is not in the import closure of GMT.Ch07.Submission; the implementation must add this import, as the parent's implementation note prescribes. Notation: Λ^n := Covector (Euclid P) n with operator norm ‖·‖; |·|_E := covectorEuclideanNorm.

0. (Norm facts and the radial retraction.) By regcomp_covectorEuclideanNorm_seminorm_retract choose c > 0 with the following properties: (i) α ↦ |α|_E is continuous; (iii) |t•α|_E = |t|·|α|_E; (iv) |α|_E ≤ c‖α‖; (v) |(max 1 |v|_E)⁻¹ • v − b|_E ≤ |v − b|_E whenever |b|_E ≤ 1. Define π : Λ^n → Λ^n by π(v) := (max 1 |v|_E)⁻¹ • v. Then:
 – π is continuous, by (i), Continuous.max, Continuous.inv₀ (max 1 |v|_E ≥ 1 > 0) and Continuous.smul;
 – π(0) = 0 (smul_zero);
 – |π(v)|_E ≤ 1: by (iii) with the positive scalar (max 1 |v|_E)⁻¹, |π(v)|_E = (max 1 |v|_E)⁻¹·|v|_E ≤ 1 (inv_mul_le_iff₀, le_max_right);
 – |π(v) − b|_E ≤ |v − b|_E whenever |b|_E ≤ 1, which is (v).

1. (C_c approximation.) ν is finite, hence locally finite, on the σ-compact metric space Euclid P, so ν is regular (instance MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure); Euclid P is also R1 and locally compact. Apply Integrable.exists_hasCompactSupport_lintegral_sub_le to g with tolerance ofReal(ε/c), which is ≠ 0 since ε/c > 0. It gives a continuous g₀ : Euclid P → Λ^n with ∫⁻ ‖g(x) − g₀(x)‖ₑ dν ≤ ofReal(ε/c). Pointwise, by (iv) and ‖g₀(x) − g(x)‖ = ‖g(x) − g₀(x)‖, ofReal|g₀(x) − g(x)|_E ≤ ofReal(c‖g(x) − g₀(x)‖) = ofReal(c)·‖g(x) − g₀(x)‖ₑ (ENNReal.ofReal_mul, ofReal_norm). So by lintegral_mono and lintegral_const_mul' (ofReal c ≠ ∞),
 ∫⁻ ofReal|g₀ − g|_E dν ≤ ofReal(c)·∫⁻ ‖g − g₀‖ₑ dν ≤ ofReal(c)·ofReal(ε/c) = ofReal(ε).

2. (Cutoff.) Euclid P is locally compact, K is compact, O is open and K ⊆ O, so exists_compact_between gives a compact L with K ⊆ interior L and L ⊆ O. The closed set (interior L)ᶜ is disjoint from K, so Urysohn's lemma exists_continuous_one_zero_of_isCompact gives a continuous χ : Euclid P → ℝ with χ = 1 on K, χ = 0 on (interior L)ᶜ and 0 ≤ χ ≤ 1. Put g₁(x) := χ(x) • g₀(x). Then g₁ is continuous, and support g₁ ⊆ L: if x ∉ L then x ∉ interior L, so χ(x) = 0. For every x, g(x) = χ(x) • g(x): if x ∈ K then χ(x) = 1; if x ∉ K then g(x) = 0. Hence g₁(x) − g(x) = χ(x) • (g₀(x) − g(x)) (smul_sub), and by (iii) |g₁(x) − g(x)|_E = χ(x)·|g₀(x) − g(x)|_E ≤ |g₀(x) − g(x)|_E.

3. (Retraction.) Put f := π ∘ g₁. Then:
 – f is continuous (step 0 and continuity of g₁);
 – support f ⊆ support g₁ ⊆ L, because π(0) = 0;
 – L is compact, hence closed, so tsupport f = closure(support f) ⊆ L ⊆ O (closure_minimal);
 – tsupport f is a closed subset of the compact L, so f has compact support (IsCompact.of_isClosed_subset);
 – |f(z)|_E ≤ 1 for every z, by step 0;
 – by step 0 with b := g(x) (allowed, as |g(x)|_E ≤ 1) and step 2, |f(x) − g(x)|_E ≤ |g₁(x) − g(x)|_E ≤ |g₀(x) − g(x)|_E for every x.

4. (Estimate.) By step 3, monotonicity of ofReal and of the lower Lebesgue integral (ENNReal.ofReal_le_ofReal, lintegral_mono), and step 1,
 ∫⁻ ofReal|f(x) − g(x)|_E dν ≤ ∫⁻ ofReal|g₀(x) − g(x)|_E dν ≤ ofReal(ε).
Together with step 3, f has all the required properties. ∎

## Key steps

1. From regcomp_covectorEuclideanNorm_seminorm_retract: |·|_E is continuous, homogeneous and ≤ c‖·‖. The radial retraction π(v) = (max 1 |v|_E)⁻¹ • v is continuous, fixes 0, maps into the unit |·|_E-ball and is nonexpansive towards it.
2. ν is regular. C_c-density gives a continuous g₀ with ∫⁻ ‖g − g₀‖ₑ dν ≤ ofReal(ε/c), hence ∫⁻ ofReal|g₀ − g|_E dν ≤ ofReal ε.
3. Urysohn cutoff χ (1 on K, 0 off interior L, with L ⊆ O compact): g₁ = χ g₀ has support in L, and |g₁ − g|_E ≤ |g₀ − g|_E because g = χ g.
4. f = π ∘ g₁ is continuous, compactly supported in L ⊆ O, has |f|_E ≤ 1 and |f − g|_E ≤ |g₁ − g|_E; integrate.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Submission.lean (IDENTICAL)`
- `rg -n 'theorem Integrable.exists_hasCompactSupport_lintegral_sub_le' mathlib/Mathlib`
- `rg -n 'theorem Continuous.exists_contDiff_approx ' mathlib/Mathlib`
- `rg -n 'theorem dist_normed_convolution_le|theorem _root_.HasCompactSupport.contDiff_convolution_left' mathlib/Mathlib`
- `rg -n 'theorem support_convolution_subset|HasCompactSupport.convolution' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem opNorm_le_bound|theorem map_eq_zero_of_not_injective|lemma Integrable.of_bound' mathlib/Mathlib`
- `rg -n 'theorem exists_compact_between|theorem exists_continuous_one_zero_of_isCompact|exists_cthickening_subset_open|uniformContinuous_of_continuous' mathlib/Mathlib`
- `rg -n 'theorem norm_sub_sq_real|theorem real_inner_le_norm|theorem norm_apply_le|theorem EuclideanSpace.norm_eq|theorem basisFun_repr|protected def equiv' mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'theorem map_sum|theorem map_smul_univ' mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean; rg -n 'def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `rg -n 'theorem nonneg_normed|theorem contDiff_normed|theorem integral_normed|theorem support_normed_eq|theorem hasCompactSupport_normed' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -ln 'covectorEuclideanNorm' project/ ; rg -n 'radial|retraction|max 1' project/GMT (no reusable project lemma; definition lives in simongmt Chapter06/Mass.lean)`
- `grep -n 'covectorEuclideanNorm|massAdmissibleOn' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean; grep -n 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' .../Chapter06/Forms.lean`
- `python3 -I scans of dag.json for lean_name and normalized lean_statement collisions with the five proposed children (final: 278 nodes, none) and for related nodes (dor_ims_sua_*, rsd_mw_exists_testForm_approx, covectorEuclideanNorm_gram_bounds)`
- `grep of .swarm-worktrees/*/gmt-ch07/GMT/Ch07/*.lean for the five proposed names (no hits) and for extra imports / helper modules`
- `lake env lean /tmp/smooth-form-split/{Stmts,C13,C2,C4,C4conv,C5,Assembly,Full,Full2,Assembly2,Assembly2Base,Assembly2Exact}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-smoot-6b0404974b/parent-child-handoff.json`
- `/tmp/smooth-form-split/Full2.lean`
- `/tmp/smooth-form-split/Assembly2Exact.lean`
- `/tmp/smooth-form-split/C4conv.lean`
- `/tmp/smooth-form-split/review/children2.json`

Snapshot and contract. The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean. The snapshot project has no reusable lemma about covectorEuclideanNorm (only the Ch07 contract mentions it). The definition is in simongmt Chapter06/Mass.lean, which provides only _zero, _nonneg and _neg.

Mathlib support. The snapshot Mathlib supplies everything the children cite:
- Integrable.exists_hasCompactSupport_lintegral_sub_le (ContinuousMapDense.lean:211; needs NormedSpace ℝ E but no separability of E).
- The Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure instance (Regular.lean:1183).
- Continuous.exists_contDiff_approx, which also gives support g ⊆ support f (Geometry/Manifold/SmoothApprox.lean:132).
- Bump-convolution lemmas (BumpFunction/Convolution.lean:71, ContDiff/Convolution.lean:427, Convolution.lean:568/670).
- ContinuousAlternatingMap.opNorm_le_bound, map_eq_zero_of_not_injective, map_sum and ContinuousAlternatingMap.apply.
- ContinuousMultilinearMap.map_smul_univ.
- EuclideanSpace.norm_eq, equiv and basisFun_repr; PiLp.norm_apply_le; norm_sub_sq_real and real_inner_le_norm.
- exists_compact_between, exists_continuous_one_zero_of_isCompact, IsCompact.exists_cthickening_subset_open, HasCompactSupport.uniformContinuous_of_continuous and Integrable.of_bound.
CompleteSpace and NormedSpace instances for Covector (Euclid P) n resolve. ContinuousMapDense and SmoothApprox are outside the contract import closure; other worktrees do add imports.

Reuse and collisions. No comparator-accepted declaration with an identical type exists to reuse. The near-duplicates found mid-session (dor_ims_sua_coeff_norm_rep, dor_ims_sua_mollify_unit_field) are only decomposing; they were avoided by restating the two affected children. Final scans found no name or statement collisions and no hits in the worktrees.

Lean checks. The five children are fully proved in Full2.lean using only standard axioms. The frozen parent type is proved from them plus regcomp_covector_eval_orthonormal_le with only the contract import (Assembly2Exact.lean). An independent reviewer re-ran these checks and accepted the revised split.
