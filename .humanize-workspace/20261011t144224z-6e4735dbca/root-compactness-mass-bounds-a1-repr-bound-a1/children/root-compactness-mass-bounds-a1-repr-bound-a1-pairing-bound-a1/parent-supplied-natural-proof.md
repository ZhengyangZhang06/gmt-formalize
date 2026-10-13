# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_mass_bounds-a1.repr_bound-a1`
- Child DAG node: `root.compactness_mass_bounds-a1.repr_bound-a1.pairing_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 5 (integrability and basic estimate), with the coefficient functions of v taken on K.

Sibling used: coord_bound (cmb_rb_abs_euclideanCovectorCoordinate_le).

Notation:
- c_β(x) := euclideanCovectorCoordinate (θ x) β = θ(x)(e_{β(0)}, …, e_{β(n−1)}), with e_i = EuclideanSpace.single i 1;
- v^β(x) := euclideanNVectorCoordinate (v x) β;
- μ_K := μ.restrict K, so that 'μ-integrable on K' means μ_K-integrable and ∫_K means ∫ … ∂μ_K.

1. (Coefficient bounds.) For all β and x, |c_β(x)| ≤ |θ(x)| ≤ D, by the sibling coord_bound applied to θ(x) and β, and the hypothesis.
2. (Continuity.) For fixed β, the map α ↦ α(e_{β(0)}, …, e_{β(n−1)}) is a continuous linear map Covector (Eucl P) n → ℝ (ContinuousAlternatingMap.apply ℝ (Eucl P) ℝ (fun j ↦ EuclideanSpace.single (β j) 1)). So c_β, its composition with the continuous θ, is continuous. Hence c_β is AEStronglyMeasurable for μ_K (Continuous.aestronglyMeasurable; ℝ^P is second countable and carries its Borel σ-algebra).
3. (Integrability on K.) By hypothesis each v^β is μ_K-integrable. A bounded a.e.-strongly measurable factor times an integrable function is integrable (Integrable.bdd_mul, using Steps 1–2 with bound D). So each c_β·v^β is μ_K-integrable, and so is the finite sum f (integrable_finsetSum). That is, f is μ-integrable on K.
4. (Vanishing off K.) If x ∉ K then θ(x) = 0. The zero alternating map evaluates to 0, so c_β(x) = 0 for every β and f(x) = 0. Hence support f ⊆ K.
- f is μ-integrable (integrableOn_iff_integrable_of_support_subset); this is the first conclusion.
- ∫ f dμ = ∫_K f dμ (setIntegral_eq_integral_of_forall_compl_eq_zero).
5. (Pointwise bound.) For every x, |f(x)| ≤ Σ_β |c_β(x)|·|v^β(x)| ≤ Σ_β D·|v^β(x)|. This uses Finset.abs_sum_le_sum_abs, |ab| = |a|·|b|, Step 1 and |v^β(x)| ≥ 0. Each x ↦ D·|v^β(x)| is μ_K-integrable (Integrable.abs, Integrable.const_mul), hence so is their finite sum.
6. (Integral estimate.) The following chain uses abs_integral_le_integral_abs, integral_mono (with the integrability from Steps 3 and 5 and the pointwise bound of Step 5), integral_finsetSum, integral_const_mul and Finset.mul_sum:
|∫ f dμ| = |∫_K f dμ| ≤ ∫_K |f| dμ ≤ ∫_K Σ_β D·|v^β| dμ = Σ_β D·∫_K |v^β| dμ = D · Σ_β ∫_K |v^β| dμ.
This is the second conclusion. ∎

(If D < 0 the hypothesis |θ(x)| ≤ D cannot hold, since covectorEuclideanNorm is nonnegative. The argument above never needs D ≥ 0.)

## Key steps

1. |θ(x)(e_β)| ≤ |θ(x)| ≤ D by coord_bound.
2. x ↦ θ(x)(e_β) is continuous (evaluation is a continuous linear map), hence a.e.-strongly measurable.
3. Integrable.bdd_mul and finite sums: f is μ-integrable on K.
4. f = 0 off K, so f is μ-integrable and ∫ f dμ = ∫_K f dμ.
5. |∫_K f| ≤ ∫_K Σ_β D|v^β| = D · Σ_β ∫_K |v^β| dμ.

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
