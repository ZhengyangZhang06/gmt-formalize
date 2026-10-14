# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.integer_combination-a1`
- Child DAG node: `root.regular_set_dense-a1.integer_combination-a1.tangent_growth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof, i.e. Simon Ch. 3, Remark 1.5(3) (chapter-03.txt lines 91–95), with an explicit test function. Notation: μ := μHE[n]; B̄_r(z) is the closed ball; for ρ > 0, η_ρ(y) := ρ⁻¹(y − x) (SimonGMT blowUpMap x ρ), a homeomorphism of ℝ^P with inverse z ↦ x + ρz; ∫_S f dμ denotes the Bochner integral of f against μ⌞S.

1. Scaling. Let ρ > 0 and Z ⊆ ℝ^P. Then η_ρ(Z) = ρ⁻¹ • (Z − x), where Z − x := {z − x : z ∈ Z}. μ is translation invariant (μHE[n] is add-right-invariant on ℝ^P), so μ(Z − x) = μ(Z); and μ(c • W) = |c|ⁿ μ(W) for every c ≠ 0 and every W ⊆ ℝ^P (Mathlib Measure.euclideanHausdorffMeasure_smul₀). Hence μ(η_ρ(Z)) = ρ^{−n} μ(Z). Moreover, for R > 0, η_ρ(Z) ∩ B̄_R(0) = η_ρ(Z ∩ B̄_{Rρ}(x)), because |ρ⁻¹(z − x)| ≤ R ⟺ |z − x| ≤ Rρ. Therefore
   (1a) μ(η_ρ(Z) ∩ B̄_R(0)) = ρ^{−n} μ(Z ∩ B̄_{Rρ}(x)) for all Z ⊆ ℝ^P, ρ > 0, R > 0.
If Z is Borel then so is η_ρ(Z), η_ρ being a homeomorphism.

2. Test function. Put f(y) := max(0, min(1, 2 − |y|)). Then f is continuous, 0 ≤ f ≤ 1, f = 1 on B̄_1(0) and f = 0 outside B̄_2(0); since B̄_2(0) is compact (finite dimension), f ∈ C_c(ℝ^P, ℝ). In particular 1_{B̄_1(0)} ≤ f ≤ 1_{B̄_2(0)} pointwise.

3. Integrability. Let 0 < ρ ≤ r₀/2. By (1a) with R = 2, μ(η_ρ(D) ∩ B̄_2(0)) = ρ^{−n} μ(D ∩ B̄_{2ρ}(x)) ≤ ρ^{−n} μ(D ∩ B̄_{r₀}(x)) < ∞. Since |f| ≤ 1_{B̄_2(0)}, f is integrable with respect to μ⌞η_ρ(D). Also 1_{B̄_1(0)} is integrable with respect to μ⌞η_ρ(D), because μ(η_ρ(D) ∩ B̄_1(0)) ≤ μ(η_ρ(D) ∩ B̄_2(0)) < ∞.

4. Lower bound. For 0 < ρ ≤ r₀/2, monotonicity of the integral (steps 2 and 3) and (1a) with R = 1 give
   ∫_{η_ρ(D)} f dμ ≥ ∫_{η_ρ(D)} 1_{B̄_1(0)} dμ = μ(η_ρ(D) ∩ B̄_1(0)) = ρ^{−n} μ(D ∩ B̄_ρ(x)),
all quantities being finite real numbers (μ(D ∩ B̄_ρ(x)) ≤ μ(D ∩ B̄_{r₀}(x)) < ∞).

5. Limit. By the hypothesis HasApproximateTangentSpaceAt n D x Q applied to f ∈ C_c(ℝ^P, ℝ), ∫_{η_ρ(D)} f dμ → L := ∫_Q f dμ ∈ ℝ as ρ ↓ 0. Choose r₁ with 0 < r₁ ≤ r₀/2 such that ∫_{η_ρ(D)} f dμ ≤ L + 1 for all 0 < ρ < r₁.

6. Conclusion. Put C := L + 1. For 0 < ρ < r₁, steps 4 and 5 give ρ^{−n} μ(D ∩ B̄_ρ(x)) ≤ C; multiplying by ρⁿ > 0, the finite quantity μ(D ∩ B̄_ρ(x)) is at most Cρⁿ, i.e. μ(D ∩ B̄_ρ(x)) ≤ ENNReal.ofReal(Cρⁿ). For n = 0 every step holds verbatim (ρ⁰ = 1). ∎

## Key steps

1. Scaling: Hⁿ(η_{x,ρ}(Z) ∩ B̄_R(0)) = ρ^{−n}Hⁿ(Z ∩ B̄_{Rρ}(x)) by translation invariance and euclideanHausdorffMeasure_smul₀.
2. Test function f = max(0, min(1, 2 − |y|)) ∈ C_c with 1_{B̄_1(0)} ≤ f ≤ 1_{B̄_2(0)}, integrable on η_{x,ρ}(D) for ρ ≤ r₀/2.
3. ρ^{−n}Hⁿ(D ∩ B̄_ρ(x)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ → ∫_Q f dHⁿ =: L.
4. Hence Hⁿ(D ∩ B̄_ρ(x)) ≤ (L + 1)ρⁿ for all small ρ > 0.

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
