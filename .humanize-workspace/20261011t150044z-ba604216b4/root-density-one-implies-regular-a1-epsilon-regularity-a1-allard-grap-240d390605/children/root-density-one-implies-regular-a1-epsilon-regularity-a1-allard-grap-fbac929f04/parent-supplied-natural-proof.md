# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.radial_variation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.radial_variation-a1.radial_field_c1-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (the radial test field X(x) = φ(r/τ)(x − y), Simon Ch. 4, 3.2–3.3 with the cutoff γ(r) = φ(r/τ)).
Notation: r(x) := |x − y| (Euclidean norm of ℝ^P), X(x) := φ(r(x)/τ)·(x − y), K := B̄_{Aτ}(y) = {x : |x − y| ≤ Aτ}, B(y, τ) := {x : |x − y| < τ}.
1. (Support.) Let x ∈ ℝ^P with X(x) ≠ 0; then φ(r(x)/τ) ≠ 0. Suppose x ∉ K, i.e. r(x) > Aτ. Since τ > 0, r(x)/τ > A, so A ≤ r(x)/τ and the hypothesis gives φ(r(x)/τ) = 0, a contradiction. Hence {x : X(x) ≠ 0} ⊆ K. The closed ball K is a closed set (isClosed_closedBall), so the closure of {X ≠ 0}, which is tsupport X, is contained in K (closure_minimal). This proves (iii).
2. (Compact support.) ℝ^P is a finite-dimensional normed space, hence proper, so the closed ball K is compact (isCompact_closedBall). tsupport X is closed (isClosed_tsupport) and, by step 1, contained in K; a closed subset of a compact set is compact (IsCompact.of_isClosed_subset). Hence tsupport X is compact, i.e. X has compact support. This proves (ii).
3. (C¹ at the centre y.) Let z ∈ B(y, τ). Then r(z) < τ, so r(z)/τ < 1 because τ > 0; in particular r(z)/τ ≤ 1 and the hypothesis gives φ(r(z)/τ) = 1, so X(z) = 1·(z − y) = z − y. Since B(y, τ) is an open neighbourhood of y (τ > 0), X agrees on a neighbourhood of y with the affine map z ↦ z − y, which is C^∞ (identity minus a constant). A function that agrees on a neighbourhood of a point with a function that is C¹ at that point is itself C¹ at that point (ContDiffAt.congr_of_eventuallyEq). Hence X is C¹ at y.
4. (C¹ at a point x ≠ y.) Let x ≠ y. The map z ↦ z − y is C^∞ and its value at x is x − y ≠ 0. The Euclidean norm of the inner-product space ℝ^P is C^∞ at every nonzero vector (it is the square root of the C^∞ function |·|², which is positive there; Mathlib contDiffAt_norm), so by composition z ↦ r(z) = |z − y| is C^∞, in particular C¹, at x (ContDiffAt.norm). Division by the constant τ preserves this (ContDiffAt.div_const), and composing with the C¹ function φ gives that z ↦ φ(r(z)/τ) is C¹ at x (ContDiff.contDiffAt and ContDiffAt.comp). Finally X is the product (scalar times vector) of this C¹ scalar function with the C^∞ vector function z ↦ z − y, so X is C¹ at x (ContDiffAt.smul).
5. (Conclusion.) By steps 3 and 4, X is C¹ at every point of ℝ^P, so X is C¹ on ℝ^P (contDiff_iff_contDiffAt). This proves (i); (ii) and (iii) were proved in steps 2 and 1. ∎

## Key steps

1. If X(x) ≠ 0 then φ(|x − y|/τ) ≠ 0, so |x − y|/τ < A and |x − y| < Aτ; the closed ball is closed, so tsupport X ⊆ B̄_{Aτ}(y).
2. B̄_{Aτ}(y) is compact in ℝ^P, so the closed set tsupport X is compact.
3. On B(y, τ), |z − y|/τ < 1, so φ(|z − y|/τ) = 1 and X(z) = z − y; hence X is C¹ at y.
4. At x ≠ y the norm is smooth at x − y ≠ 0, so z ↦ φ(|z − y|/τ)(z − y) is C¹ at x by composition and product rules.
5. C¹ at every point gives ContDiff ℝ 1 X.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project; project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (IDENTICAL)`
- `rg -n 'doragm_rfv|radial_field' project (no match)`
- `rg -n 'theorem (hasStrictFDerivAt_norm|hasFDerivAt_norm|HasFDerivAt.norm|fderiv_norm|HasStrictFDerivAt.norm)\b|theorem hasStrictFDerivAt_norm_sq|theorem IsProj.trace|theorem trace_smulRight|theorem trace_comp_comm'|lemma hasFDerivAt_norm|theorem contDiffAt_norm' mathlib/Mathlib (no HasFDerivAt lemma for the unsquared norm; contDiffAt_norm, hasStrictFDerivAt_norm_sq, IsProj.trace, trace_smulRight, trace_comp_comm' found)`
- `rg -n 'lemma starProjection_apply_mem|theorem starProjection_eq_self_iff|norm_sq_eq_add_norm_sq_starProjection|theorem inner_starProjection_left_eq_right|theorem starProjection_inner_eq_zero|sub_starProjection_mem_orthogonal|theorem norm_sub_sq_eq_norm_sq_add_norm_sq' mathlib/Mathlib`
- `rg -n 'theorem integral_withDensity_eq_integral_toReal_smul|theorem integrableOn_iff_integrable_of_support_subset|integrableOn_of_bounded|theorem HasFDerivAt.sqrt|theorem HasFDerivAt.smul |theorem contDiff_iff_contDiffAt|theorem real_inner_smul_left|theorem HasFDerivAt.mul_const |theorem HasDerivAt.comp_hasFDerivAt|theorem norm_sub_sq_real|theorem Filter.EventuallyEq.fderiv_eq|theorem withDensity_absolutelyContinuous' mathlib/Mathlib`
- `rg -n 'theorem|lemma' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean | rg -i 'trace|radial|div|starProj'`
- `python3 -I scan of dag.json lean_statement fields for firstVariation|starProjection|LinearMap.trace|tangentialDivergence|approxTangentPlane and for R.measure finiteness (found accepted dsmc_firstVariation_eq_integral, dorag_aa_ae_finrank_approxTangentPlane, rsd_imrep_compact_measure_ne_top; precedent of cross-branch reuse in root.minimizing_implies_stationary-a1.support_null-a1)`
- `git show 6c199bd/db91248/702e708:GMT/Ch07/Submission.lean (accepted proofs of the reused declarations)`
- `python3 -I name-collision scan of doragm_rfv* over gmt-ch01..08 dag.json (no hit); git for-each-ref | grep rfv (no hit); git log --all -S'doragm_rfv' (empty)`
- `lake env lean /tmp/rfv-decomp/{Probe,Assembly,Child1,Child2,Full,FromJson}.lean with #print axioms`
- `verifier/lean_contract.py validate_lean_statement on the five child types (all valid)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rfv-decomp/Assembly.lean`
- `/tmp/rfv-decomp/Child1.lean`
- `/tmp/rfv-decomp/Child2.lean`
- `/tmp/rfv-decomp/FromJson.lean`

Snapshot provenance:
- The snapshot pins project b4d606d and Mathlib 25730c7c.
- Its GMT/Ch07/Contract.lean is byte-identical to the workspace Submission.lean, which is the compiler context of every child type.
- No doragm_rfv* or radial-field declaration exists in the project snapshot.

Mathlib at the pinned revision:
- It has no HasFDerivAt lemma for the unsquared norm. The trace child therefore derives it from hasStrictFDerivAt_norm_sq / HasFDerivAt.norm_sq and HasFDerivAt.sqrt (Sqrt.lean:109).
- Every other lemma the children's proofs cite exists in contract scope:
  - contDiffAt_norm (InnerProductSpace/Calculus.lean:154);
  - LinearMap.IsProj.trace (Trace.lean:327), trace_smulRight (Trace.lean:272) and trace_comp_comm' (Trace.lean:265);
  - Submodule.starProjection_apply_mem (Projection/Basic.lean:156), starProjection_eq_self_iff (:290) and starProjection_inner_eq_zero (:164);
  - norm_sub_sq_real (InnerProductSpace/Basic.lean:437) and real_inner_smul_left (:110);
  - HasFDerivAt.smul (FDeriv/Mul.lean:72) and HasFDerivAt.mul_const (:299);
  - HasDerivAt.comp_hasFDerivAt (Deriv/Comp.lean:171);
  - Filter.EventuallyEq.fderiv_eq (FDeriv/Congr.lean:260);
  - contDiff_iff_contDiffAt (ContDiff/Defs.lean:1103);
  - integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318);
  - integrableOn_iff_integrable_of_support_subset (IntegrableOn.lean:462) and Measure.integrableOn_of_bounded (:716);
  - withDensity_absolutelyContinuous (WithDensity.lean:146).

SimonGMT template:
- The pinned SimonGMT Chapter04/FirstVariation.lean proves the analogous squared-radius radial-field lemmas (contDiff_/tsupport_/hasCompactSupport_squaredRadialVectorField, trace_starProjection, trace_radialEndomorphism, tangentialDivergence_squaredRadialVectorField).
- These are for its own varifold structure, which the contract does not import, so the file served only as a template for the factorization.

Reuse and Lean checks:
- dag.json shows three accepted, dependency-free declarations whose frozen types are reused byte-identically: dsmc_firstVariation_eq_integral, dorag_aa_ae_finrank_approxTangentPlane and rsd_imrep_compact_measure_ne_top.
- Their accepted proofs, the two new child proofs and the parent assembly compile together from the exact lean_statement strings (/tmp/rfv-decomp/FromJson.lean), with axioms propext, Classical.choice and Quot.sound only.
- The new names occur in no DAG, ref or commit.
