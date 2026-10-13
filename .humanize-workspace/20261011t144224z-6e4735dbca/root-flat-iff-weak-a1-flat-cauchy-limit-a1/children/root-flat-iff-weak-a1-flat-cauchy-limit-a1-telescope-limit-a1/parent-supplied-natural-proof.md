# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.flat_cauchy_limit-a1`
- Child DAG node: `root.flat_iff_weak-a1.flat_cauchy_limit-a1.telescope_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 6, proof of 7.2, last paragraph: “by 3.13 we can define integer multiplicity R^(ℓ), S^(ℓ) by the M-absolutely convergent series R^(ℓ) = Σ_{r=ℓ}^∞ R_r, S^(ℓ) = Σ_{r=ℓ}^∞ S_r; … and (from (5)) T − T_{j_ℓ} = ∂R^(ℓ) + S^(ℓ)”.

This is Step 4 of the parent proof, isolated:
- T_r plays the role of T_{j_r};
- the increments are written in the order T_r − T_{r+1} = ∂R_r + S_r, so the conclusion reads T_ℓ − T = ∂X + Y with no sign change;
- X and Y play the roles of R^(ℓ) and S^(ℓ).
Only the pointwise series identities (c) and (d) are used; integrality and mass play no role.

1. (Boundary as evaluation at dω.) Fix ω ∈ D^n(U) and put dω := exteriorDerivativeTestOn U n ω ∈ D^{n+1}(U).
   By definition of the boundary, ∂Z(ω) = Z(dω) for every Z ∈ D_{n+1}(U) (`GeometricCurrentOn.boundary_apply`).
   Hence hypothesis (a) at r reads T_r(ω) − T_{r+1}(ω) = R_r(dω) + S_r(ω), and the goal is T_ℓ(ω) − T(ω) = X(dω) + Y(ω).

2. (Telescoping.) For every N ∈ ℕ,
   T_ℓ(ω) − T_{ℓ+N}(ω) = Σ_{k=0}^{N−1} (R_{ℓ+k}(dω) + S_{ℓ+k}(ω)).
   Induction on N. For N = 0 both sides are 0. If the identity holds for N, then
   T_ℓ(ω) − T_{ℓ+N+1}(ω) = (T_ℓ(ω) − T_{ℓ+N}(ω)) + (T_{ℓ+N}(ω) − T_{ℓ+N+1}(ω))
                         = Σ_{k=0}^{N−1} (R_{ℓ+k}(dω) + S_{ℓ+k}(ω)) + (R_{ℓ+N}(dω) + S_{ℓ+N}(ω)),
   by the induction hypothesis and step 1 with r = ℓ + N. This is the sum up to k = N.
   (Lean: `Finset.sum_range_succ`, rewrite with the induction hypothesis and (a), then `ring`.)

3. (Limit of the left side.) The map N ↦ ℓ + N tends to ∞, since ℓ + N ≥ N. (Lean: `tendsto_atTop_mono (fun N => Nat.le_add_left N ℓ) tendsto_id`.)
   So by hypothesis (b) at ω, T_{ℓ+N}(ω) → T(ω) as N → ∞.
   Hence T_ℓ(ω) − T_{ℓ+N}(ω) → T_ℓ(ω) − T(ω).

4. (Limit of the right side.) By (c) at η := dω and (d) at ω, the real series Σ_k R_{ℓ+k}(dω) and Σ_k S_{ℓ+k}(ω) have sums X(dω) and Y(ω).
   Hence Σ_k (R_{ℓ+k}(dω) + S_{ℓ+k}(ω)) has sum X(dω) + Y(ω) (`HasSum.add`).
   The partial sums Σ_{k=0}^{N−1} of a series over ℕ with a sum converge to that sum (`HasSum.tendsto_sum_nat`).
   So the right side of step 2 tends to X(dω) + Y(ω) as N → ∞.

5. (Uniqueness of limits.) By step 2, the sequences in steps 3 and 4 coincide for every N. Limits of a sequence in the Hausdorff space ℝ along atTop are unique (`tendsto_nhds_unique`).
   Therefore T_ℓ(ω) − T(ω) = X(dω) + Y(ω), which equals ∂X(ω) + Y(ω) by step 1.

6. (Conclusion.) Since ω ∈ D^n(U) was arbitrary, T_ℓ(ω) − T(ω) = ∂X(ω) + Y(ω) for all ω ∈ D^n(U). ∎

## Key steps

1. Rewrite ∂Z(ω) = Z(dω) with dω = exteriorDerivativeTestOn U n ω (GeometricCurrentOn.boundary_apply).
2. Telescoping by induction on N: T_ℓ(ω) − T_{ℓ+N}(ω) = Σ_{k<N} (R_{ℓ+k}(dω) + S_{ℓ+k}(ω)).
3. The left side tends to T_ℓ(ω) − T(ω) by weak convergence along ℓ + N → ∞.
4. The right side tends to X(dω) + Y(ω) by HasSum.add and HasSum.tendsto_sum_nat.
5. Uniqueness of limits in ℝ gives T_ℓ(ω) − T(ω) = ∂X(ω) + Y(ω).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -uu -n 'IsIntegerMultiplicity|flatDistance|WeaklyConvergesOn|fiw_|telescop|nested' project/GMT`
- `grep -rn 'theorem extraction_of_frequently_atTop|theorem extraction_forall_of_frequently|theorem extraction_forall_of_eventually' mathlib/Mathlib/Order/Filter/`
- `rg -uu -n 'theorem Infinite\.exists_gt|theorem strictMono_nat_of_lt_succ|theorem tendsto_nhds_unique |theorem tendsto_atTop_mono |protected theorem tsum_add |protected theorem tsum_mul_left|theorem one_sub_inv_two' mathlib/Mathlib`
- `rg -uu -n 'ENNReal\.tsum_geometric|theorem HasProd\.tendsto_prod_nat|theorem HasProd\.mul ' mathlib/Mathlib`
- `grep -n 'def WeaklyConvergesOn|theorem GeometricCurrentOn.boundary_apply|def exteriorDerivativeTestOn|theorem GeometricCurrentOn.massOn_mono|def GeometricCurrentOn.mass' SimonGMT Chapter06/Currents.lean Chapter06/Mass.lean`
- `python3 listing of dag.json lean_names/depends_on and nodes/*/decomposition-v*.json lean_names (no fiw_fcl_* reserved; deformation_im_completeness not type-identical, not reused)`
- `grep -n 'depends_on' /runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/runtime.py (child depends_on built only from sibling keys)`
- `sed -n 2028,2140p book/chapter-06.txt (statement and proof of 7.2, (5), 3.13 series R^(ℓ), S^(ℓ))`
- `python3 gen_challenges.py: lean_contract.validate_lean_statement + gmt-compare.child_modules(mode=contract) -> Scratch/Ch_fiw_fcl_*.lean; lake env lean (only the expected sorry warning)`
- `lake env lean Scratch/FclExact.lean (#print axioms exact_assembly, exact_childA, exact_childB: [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Interval/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Monotone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Tendsto.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-flat-cauchy-limit-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/fcl_check_o5r2Ns/Scratch/Ch_fiw_fcl_nested_subseq.lean`
- `/tmp/fcl_check_o5r2Ns/Scratch/Ch_fiw_fcl_telescope_limit.lean`
- `/tmp/fcl_check_o5r2Ns/Scratch/FclProofs.lean`
- `/tmp/fcl_check_o5r2Ns/Scratch/FclExact.lean`

The snapshot pins the frozen Ch06 contract (project d8d46c95, Mathlib 25730c7c). WeaklyConvergesOn is pointwise convergence on test forms. GeometricCurrentOn.boundary_apply gives ∂T(ω) = T(exteriorDerivativeTestOn U n ω), and mass = massOn U, with massOn_mono available.

Neither the project nor SimonGMT has a telescoping or subsequence-extraction lemma for currents. Mathlib's extraction_of_frequently_atTop and extraction_forall_of_frequently extract only along single-index predicates, not consecutive pairs drawn from nested infinite sets. That pairwise extraction is therefore a new child (fiw_fcl_nested_subseq).

Mathlib supplies every tool the children and the assembly need: Set.Infinite.exists_gt, strictMono_nat_of_lt_succ, HasSum.tendsto_sum_nat (from HasProd.tendsto_prod_nat), HasSum.add (from HasProd.mul), tendsto_atTop_mono, tendsto_nhds_unique, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric and ENNReal.one_sub_inv_two.

The only similar DAG statement is deformation_im_completeness, which has a different type and is not reused. No fiw_fcl_* name is reserved.

In the scratch build:
- both child types elaborate in the exact comparator challenge text;
- both children are proved;
- the exact frozen parent type follows from (childA) → (childB) → (frozen fiw_im_series), kernel-checked with axioms [propext, Classical.choice, Quot.sound].
