# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.dim_zero-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.dim_zero-a1.carrier_finite-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof ("Local finiteness: for compact K ⊆ U, #(M ∩ K) ≤ Σ_{q∈M∩K} θ(q) = ∫_{M∩K} θ dH⁰ < ∞ (θ ≥ 1 on M), so M ∩ K is finite"), with the details supplied.

Notation: M := R.carrier, θ := R.mult, H⁰ := μHE[0]. All measures are on the Borel σ-algebra of ℝ^P = Euclid P.

1. H⁰ gives mass 1 to every point. Indeed μHE[0] = μH[0] (Mathlib Measure.euclideanHausdorffMeasure_zero) and μH[0]{x} = 1 (Mathlib Measure.hausdorffMeasure_zero_singleton). Hence H⁰{x} = 1 for every x ∈ ℝ^P.
2. M ∩ K is Borel. M is Borel (field measurableSet_carrier). K is compact in the Hausdorff space ℝ^P, hence closed, hence Borel.
3. H⁰(M ∩ K) < ∞.
   - For x ∈ M ∩ K the field mult_pos gives 0 < θ(x) in ℕ, hence 1 ≤ θ(x) as elements of [0, ∞].
   - Because M ∩ K is measurable, H⁰(M ∩ K) = ∫⁻_{M∩K} 1 dH⁰ ≤ ∫⁻_{M∩K} θ dH⁰. This uses Mathlib setLIntegral_one and setLIntegral_mono'; the inequality holds pointwise on M ∩ K.
   - The right-hand side is ≠ ∞ by the field locallyIntegrable_mult, applied to the compact set K ⊆ U.
4. Suppose, for contradiction, that M ∩ K is infinite.
   - By step 3 there is N ∈ ℕ with H⁰(M ∩ K) < N (ENNReal.exists_nat_gt).
   - An infinite set has finite subsets of every cardinality (Set.Infinite.exists_subset_card_eq). So there is a finite set F ⊆ M ∩ K with exactly N elements.
5. Singletons are Borel, so H⁰(F) = Σ_{x∈F} H⁰{x} (Mathlib sum_measure_singleton). By step 1 this sum is Σ_{x∈F} 1 = N.
6. By monotonicity of H⁰, N = H⁰(F) ≤ H⁰(M ∩ K) < N, which is impossible. Hence M ∩ K is finite.

## Key steps

1. H⁰ = μHE[0] = μH[0] gives every point mass 1.
2. θ ≥ 1 on M yields H⁰(M ∩ K) ≤ ∫_{M∩K} θ dH⁰ < ∞ by local integrability on the compact K ⊆ U.
3. An infinite M ∩ K would contain an N-point subset of H⁰-measure N for some N > H⁰(M ∩ K), a contradiction.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (both identical; snapshot project b4d606d, mathlib 25730c7c)`
- `rg -n 'structure GeometricCurrentOn|GeometricCurrentOn.ext|instance .*Zero|zero_apply|TestFormOnConverges|abbrev TestFormOn' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `rg -n 'GeometricCurrentOn.VanishesOn|GeometricCurrentOn.zeroRegion|GeometricCurrentOn.support|restrictDomain' simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `rg -n 'massAdmissibleOn|GeometricCurrentOn.massOn|le_massOn|covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `rg -n 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `rg -n 'pointCurrent|Dirac' simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `rg -n 'def CountablyRectifiable|CountablyRectifiable.mono|def blowUpMap|def HasApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'euclideanHausdorffMeasure_zero' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; rg -n 'hausdorffMeasure_zero_singleton' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'sum_measure_singleton|Infinite.exists_subset_card_eq|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|IntegrableOn.of_forall_sdiff_eq_zero|integrableOn_singleton_iff|integrableOn_finite_biUnion|theorem setIntegral_union|theorem integral_singleton|theorem restrict_singleton|theorem restrict_union|dirac_withDensity|withDensity_add_measure|iteratedFDeriv_zero_eq_comp|TendstoUniformlyOn.tendsto_at|set_biUnion_coe' mathlib/Mathlib`
- `lean_name inventory: rg over runs/20261011T150044Z-ba604216b4 (dag.json, all node JSON/markdown), GMT/Ch07/Submission.lean and git log --all -S for dtc_dim_zero_carrier_finite, dtc_approxTangent_sdiff_singleton, dtc_dim_zero_erase_point, dtc_point_current (no match)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the four child types`
- `lake build GMT.Ch07.Submission in /tmp/dz-decomp-7f3a/proj; lake env lean Check/Assembly.lean, Check/ChildA.lean, Check/ChildB.lean, Check/ChildC.lean, Check/ChildD.lean, Check/All.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-dim-zero-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-mass-eq-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-zero-dim-minimizing-trivial-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-finite-of-dim-zero-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Dirac/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dz-decomp-7f3a/proj/Check/Assembly.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/ChildA.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/ChildB.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/ChildC.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/ChildD.lean`
- `/tmp/dz-decomp-7f3a/proj/Check/All.lean`
- `/tmp/dz-decomp-7f3a/scripts/stmts.py`

The snapshot contract and submission (project b4d606d, mathlib 25730c7c) are byte-identical to the workspace copies.

The frozen objects the children use come from SimonGMT:
- GeometricCurrentOn, its ext and Zero instance, and TestFormOnConverges (Chapter06/Currents.lean).
- VanishesOn, zeroRegion and support (Chapter06/CurrentLocalEquality.lean).
- massAdmissibleOn and massOn (Chapter06/Mass.lean).
- CountablyRectifiable.mono, blowUpMap and HasApproximateTangentSpaceAt (Chapter03/Rectifiable.lean).

The library's only point current is the algebraic whole-space degree-0 `pointCurrent` in Chapter06/Product.lean. It has no domain, continuity or support lemma, so the child dtc_point_current is needed.

The library has no lemma on deleting a point from a carrier, on 0-dimensional local finiteness, or on locality of approximate tangent spaces under point deletion. These are the remaining three children.

Mathlib supplies the required facts: μHE[0] = μH[0] with μH[0]{x} = 1, sum_measure_singleton, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, IntegrableOn.of_forall_sdiff_eq_zero, integrableOn_singleton(_iff), integrableOn_finite_biUnion, setIntegral_union, integral_singleton, Measure.restrict_union, Measure.restrict_singleton, withDensity_add_measure, dirac_withDensity, and iteratedFDeriv_zero_eq_comp. Set.diff_subset is deprecated in favour of sdiff_subset.

Verification results:
- All four child types elaborate in the comparator scope and pass validate_lean_statement.
- All four children were proved in the scratch project using only propext, Classical.choice and Quot.sound.
- The parent's frozen type is proved from the exact child strings plus the stubbed resolved sibling dtc_mass_eq_measure.
- None of the four names occurs anywhere else in the run or in the repository.
