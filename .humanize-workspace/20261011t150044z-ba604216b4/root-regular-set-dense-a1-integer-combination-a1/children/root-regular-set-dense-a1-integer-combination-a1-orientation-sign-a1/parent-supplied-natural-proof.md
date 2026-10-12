# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.integer_combination-a1`
- Child DAG node: `root.regular_set_dense-a1.integer_combination-a1.orientation_sign-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the linear-algebra part of step 3 of the parent proof (orthonormal bases of Q differ by an orthogonal matrix of determinant ±1).

1. Unfolding the hypotheses: there are orthonormal families τ, τ' : Fin n → ℝ^P with span(range τ) = Q = span(range τ'), and signs ε, ε' ∈ {1, −1} with v(α) = ε·α(τ) and w(α) = ε'·α(τ') for every n-covector α (continuous alternating n-linear map ℝ^P → ℝ).

2. Each τ_i and τ'_i lies in Q, so τ, τ' may be regarded as families in the inner product space Q, where they are still orthonormal. Since τ is linearly independent and spans Q, dim Q = n; an orthonormal (hence linearly independent) family of n vectors in the n-dimensional space Q spans Q. Hence τ and τ' are orthonormal bases b and b' of Q indexed by Fin n.

3. Let d := det_b(b'), the determinant of the change-of-basis matrix from b to b'. Both bases are orthonormal, so this matrix is orthogonal and d ∈ {1, −1} (Mathlib OrthonormalBasis.det_to_matrix_orthonormalBasis_real).

4. Let α be an n-covector and α_Q its restriction to Q (α composed with the inclusion Q → ℝ^P in each slot), an alternating n-linear form on the n-dimensional space Q. Every such form is a multiple of det_b: α_Q = α_Q(b)·det_b (Mathlib AlternatingMap.eq_smul_basis_det). Evaluating at b' gives α(τ') = α_Q(b') = α_Q(b)·det_b(b') = d·α(τ). The number d does not depend on α.

5. Hence for every α: w(α) = ε'·α(τ') = ε'd·α(τ) = (εε'd)·(ε·α(τ)) = s·v(α), where s := εε'd ∈ {1, −1} (using ε² = 1). Therefore w = s·v, i.e. w = v if s = 1 and w = −v if s = −1. For n = 0 the same argument applies (τ = τ' is the empty family, Q = {0}, d = 1). ∎

## Key steps

1. Both orthonormal families spanning Q are orthonormal bases b, b' of Q.
2. det_b(b') = ±1 because the change-of-basis matrix is orthogonal.
3. For every n-covector α, α(τ') = det_b(b')·α(τ) since alternating n-forms on Q are multiples of det_b.
4. Therefore w = (εε'det_b(b'))·v with εε'det_b(b') ∈ {±1}.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean`
- `cat local-references/123e8435b4a2469b/manifest.json`
- `grep -n 'HasApproximateTangentSpaceAt|def CountablyRectifiable|^theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n '^def |^abbrev |^structure |^theorem ' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass,CurrentLocalEquality}.lean`
- `grep -n 'theorem ae_tendsto_measure_inter_div |theorem ae_tendsto_measure_inter_div_of_measurableSet' local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `grep -n 'euclideanHausdorffMeasure_smul₀|euclideanHausdorffMeasure_homothety_image|IsAddRightInvariant' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn 'det_to_matrix_orthonormalBasis_real' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'theorem AlternatingMap.eq_smul_basis_det' local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `grep -n 'theorem le_opNorm' local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `grep -n "span_eq_top_of_card_eq_finrank'|finrank_span_eq_card|measurableSet_eq_fun|ae_restrict_iff'|ae_restrict_of_ae_restrict_of_subset" in local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rln 'IMRep|IsIntegerMultiplicity' local-references/123e8435b4a2469b/project/GMT`
- `python3 listing of dag.json lean_name/lean_statement; grep -c rsdic dag.json; grep -rl rsdic GMT .humanize/.../nodes; grep -rl rsdic --include=*.lean simongmt`
- `python3 string comparison of the tangent_locality type with dag node root.regular_components_are_minimizing-a1.approx_tangent_locality-a1`
- `sed -n 750,760p chapter-06.txt; sed -n 86,145p chapter-03.txt; sed -n 296,316p chapter-03.txt; sed -n 900,928p chapter-01.txt`
- `lake env lean /tmp/rsdic-check/Axioms.lean (#check / #print axioms of cited lemmas)`
- `lake env lean /tmp/rsdic-check/Sign.lean (sorry-free proof of the orientation_sign type)`
- `lake env lean /tmp/rsdic-check/Final3.lean (7 frozen child types in the replayed contract scope + parent assembly + glue proofs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-approx-tangent-locality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/rsdic-check/Axioms.lean`
- `/tmp/rsdic-check/Sign.lean`
- `/tmp/rsdic-check/Final3.lean`
- `/tmp/rsdic-scripts/children.py`

The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No match for a reusable proof of Simon 6.3.2(1) for this contract's IMRep:
- GMT/Ch06/Contract.lean has its own unproved IsIntegerMultiplicity, in a module Ch07 does not import.
- SimonGMT has no IMRep.

Reusable facts found, all depending only on propext, Classical.choice and Quot.sound:
- SimonGMT Chapter03: HasApproximateTangentSpaceAt (Def. 1.4 with Bochner integrals over blowUpMap images), HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono, countablyRectifiable_iUnion.
- Mathlib: Besicovitch.ae_tendsto_measure_inter_div, Measure.euclideanHausdorffMeasure_smul₀, OrthonormalBasis.det_to_matrix_orthonormalBasis_real (PiL2.lean:992), AlternatingMap.eq_smul_basis_det, ContinuousAlternatingMap.le_opNorm, LinearIndependent.span_eq_top_of_card_eq_finrank', finrank_span_eq_card, StronglyMeasurable.measurableSet_eq_fun.

FiniteDimensional ℝ (MultiVector P n) is not an available instance, so the child proofs avoid it; strong measurability into a metrizable space suffices.

Names: the rsdic_ prefix occurs nowhere in dag.json, the node directories, GMT or SimonGMT. The tangent_locality type is string-identical to regcomp_approx_tangent_locality, which is still decomposing and so cannot be reused yet.

Lean checks:
- All seven frozen child types elaborate after import GMT.Ch07.Submission in the comparator's replayed contract scope.
- The frozen parent type is proved from combination_construction and combination_action.
- imrep_tangent_transfer is proved from tangent_locality, and overlap_orientation_sign from imrep_tangent_transfer and orientation_sign.
- These use only the standard axioms plus sorryAx from the child stubs.
- The orientation_sign type has a complete sorry-free proof using only standard axioms.
