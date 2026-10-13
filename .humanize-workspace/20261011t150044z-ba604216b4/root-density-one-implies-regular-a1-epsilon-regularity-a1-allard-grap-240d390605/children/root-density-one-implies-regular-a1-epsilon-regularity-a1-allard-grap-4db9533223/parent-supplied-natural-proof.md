# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.radial_variation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.radial_variation-a1.radial_field_trace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5 (trace p_x = dim T_xM) and 6 (divergence formula for the radial field, Simon Ch. 4, 3.2) of the parent proof, with the subspace Q in place of T_xM and dim Q in place of n.
Notation: p := Q.starProjection (the orthogonal projection of ℝ^P onto Q, an endomorphism of ℝ^P), d := dim Q, v := x − y, r := |v|, X(z) := φ(|z − y|/τ)·(z − y), DX(x) := fderiv ℝ X x, φ' := deriv φ, I := identity of ℝ^P, ⟨·,·⟩ the Euclidean inner product.
1. (Trace of p.) For every w ∈ ℝ^P, p(w) ∈ Q (Submodule.starProjection_apply_mem), and p(w) = w for every w ∈ Q (Submodule.starProjection_eq_self_iff). Hence p is a linear projection onto Q (LinearMap.IsProj Q p): with respect to the decomposition ℝ^P = Q ⊕ ker p it is id_Q ⊕ 0. Its trace is therefore dim Q (LinearMap.IsProj.trace; Q and ker p are finite-dimensional real vector spaces, hence free and finite). So trace p = d. (Equivalently: p = ι∘π with π the orthogonal projection onto Q and ι the inclusion, and trace(ι∘π) = trace(π∘ι) = trace(id_Q) = d by LinearMap.trace_comp_comm'.)
2. (Case x = y.) For z in the open ball B(y, τ) we have |z − y|/τ < 1 (τ > 0), so φ(|z − y|/τ) = 1 and X(z) = z − y. Thus X coincides with z ↦ z − y on a neighbourhood of y, so the two maps have the same derivative at y (Filter.EventuallyEq.fderiv_eq), namely DX(y) = I (the derivative of the identity minus a constant). Hence trace(p ∘ DX(y)) = trace p = d by step 1. On the right-hand side, |y − y| = 0, so |y − y|/τ = 0, φ(0) = 1 (since 0 ≤ 1), and the second summand contains the factor 0; the right-hand side equals d·1 + 0 = d. The identity holds at x = y.
3. (Case x ≠ y: derivative of the radius.) Now v ≠ 0 and r > 0. The function g(z) := |z − y|² has derivative h ↦ 2⟨v, h⟩ at x (derivative of the squared norm, HasFDerivAt.norm_sq, composed with z ↦ z − y whose derivative is I). Since g(x) = r² ≠ 0, the chain rule for the square root (HasFDerivAt.sqrt) shows that z ↦ √(g(z)) has derivative h ↦ (1/(2√(r²)))·2⟨v, h⟩ at x. As √(|z − y|²) = |z − y| for every z and √(r²) = r, the map z ↦ |z − y| has derivative h ↦ r⁻¹⟨v, h⟩ at x.
4. (Derivative of X at x ≠ y.) Multiplying by the constant τ⁻¹, z ↦ |z − y|/τ has derivative h ↦ τ⁻¹r⁻¹⟨v, h⟩ at x (HasFDerivAt.mul_const). Since φ is C¹, it is differentiable at r/τ with derivative φ'(r/τ); by the chain rule (HasDerivAt.comp_hasFDerivAt), c(z) := φ(|z − y|/τ) has derivative ℓ at x, where ℓ(h) := b⟨v, h⟩ and b := φ'(r/τ)·τ⁻¹·r⁻¹. By the product rule for a scalar function times a vector function (HasFDerivAt.smul), using that z ↦ z − y has derivative I and value v at x, X has derivative DX(x)h = c(x)·h + ℓ(h)·v = a·h + b⟨v, h⟩·v at x, where a := φ(r/τ). That is, DX(x) = a·I + (h ↦ ℓ(h)·v).
5. (Trace at x ≠ y.) Composing with p gives p ∘ DX(x) = a·p + (h ↦ ℓ(h)·p(v)). The trace is linear, and for a linear functional ℓ and a vector w the rank-one map h ↦ ℓ(h)·w has trace ℓ(w) (LinearMap.trace_smulRight). With step 1, trace(p ∘ DX(x)) = a·d + ℓ(p v) = d·φ(r/τ) + b·⟨v, p v⟩.
6. (Pythagoras.) The vector v − p v is orthogonal to Q and p v ∈ Q, so ⟨v − p v, p v⟩ = 0 (Submodule.starProjection_inner_eq_zero). Hence ⟨v, p v⟩ = ⟨p v, p v⟩ = |p v|². Expanding the square, |v − p v|² = |v|² − 2⟨v, p v⟩ + |p v|² = r² − ⟨v, p v⟩ (norm_sub_sq_real). Therefore ⟨v, p v⟩ = r² − |v − p v|².
7. (Algebra.) Since r ≠ 0, b·⟨v, p v⟩ = φ'(r/τ)·τ⁻¹·r⁻¹·(r² − |v − p v|²) = (r/τ)·φ'(r/τ)·(1 − |v − p v|²/r²). Substituting into step 5, trace(p ∘ DX(x)) = d·φ(r/τ) + (r/τ)·φ'(r/τ)·(1 − |(x − y) − p(x − y)|²/|x − y|²), which is the claim at x ≠ y. Steps 2 and 7 cover all x. ∎

## Key steps

1. p = Q.starProjection is a projection onto Q, so trace p = dim Q (LinearMap.IsProj.trace).
2. x = y: X(z) = z − y on B(y, τ), so DX(y) = I and both sides equal dim Q (φ(0) = 1, |y − y|/τ = 0).
3. x ≠ y: z ↦ |z − y| has derivative r⁻¹⟨v, ·⟩ (square-root chain rule), so DX(x) = φ(r/τ)I + φ'(r/τ)τ⁻¹r⁻¹⟨v, ·⟩v.
4. trace(p ∘ DX(x)) = dim Q·φ(r/τ) + φ'(r/τ)τ⁻¹r⁻¹⟨v, pv⟩ by linearity and the rank-one trace formula.
5. ⟨v, pv⟩ = r² − |v − pv|² by orthogonality of v − pv and pv; algebra with r ≠ 0 gives the formula.

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
