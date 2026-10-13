# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.integer_combination-a1`
- Child DAG node: `root.regular_set_dense-a1.integer_combination-a1.combination_action-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof. Notation: μ := μHE[n]; for an IMRep R' = (M', θ', ξ') put F_{R'}(x) := 1_{M'}(x)θ'(x)ξ'(x) ∈ Λ_n(ℝ^P), so the hypothesis reads F_R = p₁F_{R₁} + p₂F_{R₂} μ-a.e. Fix a test form ω ∈ 𝒟ⁿ(U): ω is smooth, hence continuous, with compact support K := tsupport ω ⊆ U; put W := sup_x |ω(x)| < ∞ (operator norm on n-covectors), and note ω(x) = 0 for x ∉ K.

1. Norm bound. If v is a unit orientation of some Q, i.e. v(α) = ±α(τ) for an orthonormal τ, then |v(α)| = |α(τ)| ≤ |α|·∏_i|τ_i| = |α| for every n-covector α (operator norm bound of continuous alternating maps, Mathlib ContinuousAlternatingMap.le_opNorm).

2. Integrability. Let R' = (M', θ', ξ') be any IMRep in U. The function h(x) := θ'(x)ξ'(x)(ω(x)) is AEStronglyMeasurable for μ⌞M' (θ' is Borel; ξ' is AEStronglyMeasurable for μ⌞M'; ω is continuous; the evaluation map (L, α) ↦ L(α) is continuous). By the field orients and step 1, for μ⌞M'-a.e. x, |h(x)| ≤ θ'(x)|ω(x)| ≤ W θ'(x)1_K(x). The bound is integrable on M': its integral is W∫⁻_{M'∩K} θ' dμ < ∞ by locallyIntegrable_mult (K is compact and K ⊆ U). Hence h is integrable on M'.

3. Rewriting the action. For an IMRep R' as in step 2 and every x, F_{R'}(x)(ω(x)) = 1_{M'}(x)h(x). As M' is Borel, R'.action ω = ∫_{M'} h dμ = ∫_{ℝ^P} F_{R'}(x)(ω(x)) dμ(x), and x ↦ F_{R'}(x)(ω(x)) is μ-integrable by step 2.

4. Conclusion. Evaluating the hypothesis at ω(x): F_R(x)(ω(x)) = p₁F_{R₁}(x)(ω(x)) + p₂F_{R₂}(x)(ω(x)) for μ-a.e. x. Integrating over ℝ^P (integrals of a.e.-equal functions agree; linearity of the Bochner integral for the integrable functions x ↦ F_{R_i}(x)(ω(x)) of step 3) and using step 3 three times:
   R.action ω = ∫ F_R(ω) dμ = p₁∫ F_{R₁}(ω) dμ + p₂∫ F_{R₂}(ω) dμ = p₁ R₁.action ω + p₂ R₂.action ω. ∎

## Key steps

1. A unit orientation v satisfies |v(α)| ≤ |α|.
2. θ'ξ'(ω) is integrable on the carrier of every IMRep, dominated by sup|ω|·θ'1_{spt ω}.
3. R'.action ω = ∫ (1_{M'}θ'ξ')(x)(ω(x)) dHⁿ(x).
4. Integrate the a.e. identity evaluated at ω(x) and use linearity of the integral.

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
