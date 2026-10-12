# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_mass_bounds-a1.repr_bound-a1`
- Child DAG node: `root.compactness_mass_bounds-a1.repr_bound-a1.coord_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 1(i).

1. By definition covectorEuclideanNorm α = √S, where S := Σ_{I : Fin n → Fin P} a_I. Here a_I := (α(b_{I(0)}, …, b_{I(n−1)}))² if I is strictly increasing and a_I := 0 otherwise, with b_i := EuclideanSpace.basisFun (Fin P) ℝ i. Every a_I is ≥ 0, being a square or 0.
2. For every i, EuclideanSpace.basisFun (Fin P) ℝ i = EuclideanSpace.single i 1 (EuclideanSpace.basisFun_apply).
3. Put I₀ := (j ↦ β j) : Fin n → Fin P. Since β is an order embedding, I₀ is strictly increasing (OrderEmbedding.strictMono). By Steps 1–2, a_{I₀} = (α(e_{β(0)}, …, e_{β(n−1)}))² = c², where c := euclideanCovectorCoordinate α β = α(fun j ↦ EuclideanSpace.single (β j) 1) by definition.
4. All summands of S are nonnegative, so one summand is at most the sum: c² = a_{I₀} ≤ S (Finset.single_le_sum over Finset.univ).
5. Hence |c| = √(c²) ≤ √S = covectorEuclideanNorm α, by Real.sqrt_sq_eq_abs and the monotonicity of √ (Real.sqrt_le_sqrt). ∎

(Edge cases: for n = 0 the unique empty tuple is strictly increasing and the argument is unchanged. If n > P, then SimonMultiIndex n P is empty and the statement is vacuous.)

## Key steps

1. Unfold |α| = √S, where S sums [I strictly increasing]·α(b_I)² over all I : Fin n → Fin P; every summand is ≥ 0.
2. I₀ := (j ↦ β j) is strictly increasing and basisFun i = single i 1, so the I₀-summand equals α(e_β)².
3. A single nonnegative summand is ≤ the sum, so |α(e_β)| = √(α(e_β)²) ≤ √S = |α|.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch06/{Contract,Submission}.lean (both ea3ee0ddd08be5db60dced2b002e9f60fd87091910069abcfcbd7e34db89853d)`
- `rg -n 'theorem exists_open_between_and_isCompact_closure' mathlib/Mathlib`
- `rg -n 'theorem exists_contDiff_support_eq_eq_one_iff' mathlib/Mathlib`
- `rg -n '^theorem Integrable.bdd_mul\b' mathlib/Mathlib`
- `rg -n 'theorem integrableOn_iff_integrable_of_support_subset|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem IntegrableOn.congr_fun\b' mathlib/Mathlib`
- `rg -n 'theorem EuclideanSpace.norm_eq|theorem EuclideanSpace.basisFun_apply' mathlib/Mathlib`
- `rg -n 'covectorEuclideanNorm|euclideanCovectorCoordinate' simongmt/Poincare`
- `rg -n 'covectorEuclideanNorm_add|covectorEuclideanNorm_le|abs_euclideanCovectorCoordinate|euclideanCovectorCoordinate_le|integrableOn_coeff|IntegrableOn.*euclideanNVectorCoordinate' project simongmt/Poincare (no match)`
- `#check exists_contDiff_support_eq_eq_one_iff / Integrable.bdd_mul / integral_finsetSum / integrable_finsetSum / ContinuousAlternatingMap.apply / WithLp.toLp after import GMT.Ch06.Submission`
- `python3 -I: dag.json lean_name scan and nodes/*/decomposition-v*.json scan for the four proposed names (no collision)`
- `python3 -I: verifier lean_contract.validate_lean_statement and gmt-compare.contract_scope/child_modules (mode contract) for the 4 child statements`
- `lake env lean Scratch/AB.lean, Scratch/C1.lean, Scratch/C2P.lean, Gen/*__NodeChallenge.lean, Scratch/Sol_0..4.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-repr-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1/decomposition-v1.json`
- `/tmp/rb_decomp_XjqsL7/Scratch/AB.lean`
- `/tmp/rb_decomp_XjqsL7/Scratch/C1.lean`
- `/tmp/rb_decomp_XjqsL7/Scratch/C2P.lean`
- `/tmp/rb_decomp_sol_P93Ver/GMT/Ch06/Submission.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The frozen Contract and Submission are byte-identical (sha256 ea3ee0dd…).

SimonGMT provides:
- covectorEuclideanNorm, with only the lemmas _zero, _nonneg and _neg;
- euclideanCovectorCoordinate, euclideanNVectorCoordinate and wedgeCovectors;
- TestFormOn, whose membership is (ContDiff ℝ ∞ ∧ HasCompactSupport) ∧ tsupport ⊆ U.
It has no coordinate bound, triangle inequality or coefficient-integrability lemma (rg: no match in the project or in SimonGMT).

The pinned Mathlib provides, all usable after `import GMT.Ch06.Submission`:
- exists_open_between_and_isCompact_closure (Topology/Separation/Regular.lean:364);
- exists_contDiff_support_eq_eq_one_iff (Geometry/Manifold/PartitionOfUnity.lean:789);
- Integrable.bdd_mul (L1Space/Integrable.lean:1067);
- IntegrableOn.congr_fun and integrableOn_iff_integrable_of_support_subset (Integral/IntegrableOn.lean);
- setIntegral_eq_integral_of_forall_compl_eq_zero (Bochner/Set.lean:486);
- EuclideanSpace.norm_eq (PiL2.lean:145);
- integral_finsetSum and integrable_finsetSum.

In scratch builds of the frozen project:
- all 4 child statements validate and elaborate as comparator NodeChallenge modules;
- each child is proved with axioms [propext, Classical.choice, Quot.sound];
- the selected frozen type follows from the 4 children plus the frozen sibling types of mass_bound, mollify and covector_expansion, with the same axioms.

The proposed cmb_rb_ names are unreserved.
