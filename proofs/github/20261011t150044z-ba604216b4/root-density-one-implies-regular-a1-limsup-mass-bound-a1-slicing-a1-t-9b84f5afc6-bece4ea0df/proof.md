# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.testform_dense-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6(a) of the parent proof ("Such a family exists by separability of C¹_c on each compact piece of an exhaustion"), which makes precise Simon's "by considering a countable dense set of ω ∈ 𝒟ⁿ(U)" in the proof of Ch. 6, 4.5(2) (chapter-06.txt lines 1318–1322). Notation: Λ^k := Covector (ℝ^P) k with its operator norm, a finite-dimensional normed space; ‖η‖_∞ := sup_{x∈ℝ^P} ‖η(x)‖.

1. Exhaustion of U. If U = ∅, then 𝒟ⁿ(U) = {0} (tsupport ω ⊆ ∅ forces ω = 0), and D := {0}, K := ∅, ω_k := 0 work. Assume U ≠ ∅.
 - For i ≥ 1 let K_i := {x ∈ ℝ^P : |x| ≤ i and dist(x, ℝ^P ∖ U) ≥ 1/i}. If U = ℝ^P, read the distance condition as void, so K_i is the closed ball B̄_i(0).
 - K_i is closed and bounded, hence compact, and K_i ⊆ U.
 - K_i ⊆ int K_{i+1}: the open set {x : |x| < i + 1, dist(x, ℝ^P ∖ U) > 1/(i+1)} contains K_i and is contained in K_{i+1}.
 - ⋃_i K_i = U, because for x ∈ U, dist(x, ℝ^P ∖ U) > 0 (U is open).
 - Consequently every compact C ⊆ U lies in some K_i: the increasing open sets int K_{i+1} cover C, so finitely many do, hence one does.

2. The pieces X_i. Let X_i := {ω ∈ 𝒟ⁿ(U) : tsupport ω ⊆ K_i}. Each X_i contains 0.
 - For ω ∈ X_i, ω vanishes on the open set ℝ^P ∖ tsupport ω, so dω vanishes there too. Hence tsupport dω ⊆ tsupport ω ⊆ K_i.
 - Equip X_i with the metric d_i(ω, η) := ‖ω − η‖_∞ + ‖dω − dη‖_∞. This is finite because ω − η and dω − dη are continuous and vanish off the compact K_i.

3. Isometric embedding into a separable space.
 - Let Y_i := C(K_i, Λⁿ) × C(K_i, Λ^{n+1}), with the metric given by the sum of the two uniform metrics. Since K_i is a compact metric space and Λⁿ, Λ^{n+1} are finite-dimensional, each C(K_i, Λ^k) is a separable metric space. In Mathlib: ContinuousMap.instSeparableSpace or ContinuousMap.instSecondCountableTopology for a compact second-countable domain, from Mathlib.Topology.ContinuousMap.SecondCountableSpace, which must be added to the imports. On compact domains the compact-open topology coincides with uniform convergence. Hence Y_i is a separable metric space.
 - Define Φ_i : X_i → Y_i by Φ_i(ω) := (ω|_{K_i}, (dω)|_{K_i}).
 - For ω, η ∈ X_i, both ω − η and dω − dη vanish outside K_i, so their sup over ℝ^P equals their sup over K_i. Thus Φ_i is an isometry from (X_i, d_i) onto its image.

4. Countable dense subsets. Every subset of a separable metric space is separable. So Φ_i(X_i) has a countable dense subset, and pulling back along the isometry Φ_i gives a countable D_i ⊆ X_i with: for every ω ∈ X_i and every k ∈ ℕ there is η ∈ D_i with d_i(η, ω) < 1/(k+1).

5. The family D. Put D := ⋃_{i≥1} D_i. It is countable, as a countable union of countable sets, and D ⊆ 𝒟ⁿ(U).

6. Approximation. Let ω ∈ 𝒟ⁿ(U).
 - ω is a test form, so tsupport ω is compact, and tsupport ω ⊆ U. By step 1, tsupport ω ⊆ K_i for some i, so ω ∈ X_i.
 - For each k choose ω_k ∈ D_i ⊆ D with d_i(ω_k, ω) < 1/(k+1) (step 4). Put K := K_i: it is compact, K ⊆ U, tsupport ω ⊆ K, and tsupport ω_k ⊆ K for all k.
 - Then ‖ω_k − ω‖_∞ < 1/(k+1) and ‖dω_k − dω‖_∞ < 1/(k+1). So ω_k → ω and dω_k → dω uniformly on ℝ^P; in Lean this is Metric.tendstoUniformly_iff, with dist = norm of the difference in Λ^k. ∎

## Key steps

1. Compact exhaustion K_i of U with K_i ⊆ int K_{i+1}; every compact subset of U lies in some K_i.
2. Test forms supported in K_i embed isometrically, via ω ↦ (ω|K_i, dω|K_i), into the separable metric space C(K_i, Λⁿ) × C(K_i, Λ^{n+1}).
3. Choose a countable dense D_i in each piece X_i and put D = ⋃ D_i.
4. Given ω, pick K_i ⊇ tsupport ω and ω_k ∈ D_i within 1/(k+1); since all supports lie in K_i, ω_k → ω and dω_k → dω uniformly on ℝ^P.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -rn -i 'slice|coarea|co-area|countable dense|SeparableSpace' local-references/123e8435b4a2469b/project/GMT --include=*.lean`
- `grep -n 'def |theorem |abbrev ' simongmt Chapter03/{Differential,Rectifiable}.lean, Chapter02/{Lipschitz,WhitneyExtension,CoareaLinear,CoareaProjection,CoareaLinearAlgebra}.lean, Chapter06/{Forms,Currents,Mass}.lean`
- `grep -rn 'ae_hasDerivAt_integral|ae_tendsto_average' snapshot mathlib Mathlib/MeasureTheory`
- `grep -rn 'SecondCountableTopology C(|SeparableSpace C(' snapshot mathlib Mathlib`
- `grep -rn 'exists_measurable_superset_of_null|integral_lineDeriv_mul_eq|tendsto_slope_zero_left|hasDerivAt_iff_tendsto_slope_left_right|tendsto_integral_filter_of_dominated_convergence' snapshot mathlib Mathlib`
- `dag.json scans: lean_name collision check for dor_lmbs_* (679 nodes, none); regex 'countable dense|separab|TendstoUniformly' and 'co-?area|Lebesgue point|mollif|tangential gradient|approxTangentPlane|Rademacher' over node statements; children of root.compactness_of_minimizing_currents-a1.slicing-a1`
- `git grep dor_lmbs_ over all local branches (no match); git show <accepted branches>:GMT/Ch07/Submission.lean | grep -c '^import' (extra Mathlib imports are used by accepted nodes)`
- `python3 -I: verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the three statements; lake env lean on the three generated challenge files`
- `lake env lean /tmp/dor-slicing-decomp/Assembly.lean (#print axioms parent_from_children)`
- `lake env lean /tmp/dor-slicing-decomp/Inst.lean (TendstoUniformly on Covector = norm-uniform; default volume; intervalIntegral = Ioc integral; empty IMRep exists)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v6.json`
- `/tmp/dor-slicing-decomp/Assembly.lean`
- `/tmp/dor-slicing-decomp/Inst.lean`
- `/tmp/dor-slicing-decomp/challenges/slice_family_Challenge.lean`
- `/tmp/dor-slicing-decomp/challenges/testform_dense_Challenge.lean`
- `/tmp/dor-slicing-decomp/challenges/pointwise_identity_Challenge.lean`

Snapshot: project b4d606d, mathlib 25730c7c; simongmt is pinned at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No current slicing, rectifiable co-area formula or countable dense family of test forms exists as a proved declaration:
- The snapshot's GMT/Ch02 and GMT/Ch06 contracts state CoareaFormula, C1Sard, IsSlice and SlicingTheorem, but only as unproven specs under sorry.
- SimonGMT has only linear and projection co-area, Rademacher, Whitney C¹ extension, and CountablyRectifiable/HasApproximateTangentSpaceAt.
- SimonGMT's tangentialGradient uses the ambient fderiv, so it is unusable for Lipschitz f on lower-dimensional sets. This is why no child statement mentions a tangential gradient.
- The compactness-branch slicing node cmc_slice_mass_bounds is about measure-represented currents without integer-multiplicity slices, and its children are not accepted, so none is reused.

Mathlib supplies these lemmas for the child proofs:
- LocallyIntegrable.ae_hasDerivAt_integral (needs an extra import);
- ContinuousMap.instSeparableSpace (needs an extra import);
- LipschitzWith.integral_lineDeriv_mul_eq;
- exists_measurable_superset_of_null;
- HasDerivAt.tendsto_slope_zero_left;
- tendsto_integral_filter_of_dominated_convergence.
Accepted nodes already add Mathlib imports to Submission.lean.

Lean checks:
- All three child types pass validate_lean_statement and elaborate in the exact comparator scope.
- A conditional assembly of the exact frozen parent type from the children, tangent_locality, borel_restriction and (C1) compiles. It depends only on propext, Classical.choice, Quot.sound and the stubs' sorryAx.
- TendstoUniformly on Covector is norm-uniform convergence, and the empty IMRep exists.
- No proposed name collides with any DAG node or branch.
