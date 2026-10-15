# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.flat_cauchy_limit-a1`
- Child DAG node: `root.flat_iff_weak-a1.flat_cauchy_limit-a1.nested_subseq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 6, proof of 7.2: “apply (1) with ε = 1, 1/2, 1/4 etc. to extract a subsequence {T_{j_r}}_{r=1,2,…} from {T_j} such that d_W̃(T_{j_{r+1}}, T_{j_r}) < 2^{−r}”.

This is the combinatorial content of Steps 1–2 of the parent proof, abstracted to an arbitrary relation Q(r, i, j). In the parent, Q(r, i, j) says that T_i − T_j = ∂R + S with R, S integer multiplicity and M(R) + M(S) < 2^{−r}. No property of Q beyond the hypothesis is used.

1. (Choice function.) By the hypothesis and the axiom of choice, fix for every r ∈ ℕ and every infinite J ⊆ ℕ a set F(r, J) with:
   - F(r, J) ⊆ J;
   - F(r, J) is infinite;
   - Q(r, i, j) holds for all i, j ∈ F(r, J).
   (Lean: `choose F hFsub hFinf hFQ using h`, with F : (r : ℕ) → (J : Set ℕ) → J.Infinite → Set ℕ.)

2. (Nested infinite sets.) Define J_0 := ℕ and J_{r+1} := F(r, J_r).
   Simultaneously, by induction on r, every J_r is infinite: J_0 = ℕ is infinite, and if J_r is infinite then F(r, J_r) is defined and infinite by step 1. So the recursion is well defined.
   (Lean: a sequence in the subtype {J : Set ℕ // J.Infinite}, defined by `Nat.rec ⟨univ, infinite_univ⟩ (fun r J => ⟨F r J.1 J.2, hFinf r J.1 J.2⟩)`.)
   By step 1, for every r ∈ ℕ:
   (a) J_{r+1} ⊆ J_r;
   (b) Q(r, i, j) holds for all i, j ∈ J_{r+1}.

3. (Unboundedness.) If A ⊆ ℕ is infinite, then for every m ∈ ℕ there is x ∈ A with m < x. Otherwise A ⊆ {0, 1, …, m} would be finite. (Lean: `Set.Infinite.exists_gt`.)
   Apply this to the infinite sets J_{r+1}. Fix, for all r, m ∈ ℕ, an element g(r, m) ∈ J_{r+1} with m < g(r, m).

4. (Definition of φ.) Define recursively φ(0) := g(0, 0) and φ(r+1) := g(r+1, φ(r)).
   By step 3, φ(0) ∈ J_1 and φ(r+1) ∈ J_{r+2}; that is, φ(r) ∈ J_{r+1} for every r ∈ ℕ (case distinction r = 0 or r = s+1).
   Moreover φ(r) < g(r+1, φ(r)) = φ(r+1) for every r ∈ ℕ.

5. (Strict monotonicity.) Since φ(r) < φ(r+1) for every r, φ is strictly increasing. Indeed, for r < s, induction on s gives φ(r) < φ(s): if s = r + 1 this is step 4, and φ(r) < φ(s) implies φ(r) < φ(s) < φ(s+1). (Lean: `strictMono_nat_of_lt_succ`.)

6. (Consecutive pairs.) Fix r ∈ ℕ.
   - By step 4, φ(r) ∈ J_{r+1} and φ(r+1) ∈ J_{r+2}.
   - By step 2(a) applied at r + 1, J_{r+2} ⊆ J_{r+1}, so φ(r+1) ∈ J_{r+1}.
   - Hence both φ(r) and φ(r+1) lie in J_{r+1} = F(r, J_r), and step 2(b) gives Q(r, φ(r), φ(r+1)).

7. (Conclusion.) φ is strictly increasing by step 5, and Q(r, φ(r), φ(r+1)) holds for every r ∈ ℕ by step 6. ∎

## Key steps

1. Choose F(r, J) ⊆ J infinite such that Q(r, ·, ·) holds on all pairs from F(r, J).
2. Define the nested infinite sets J_0 = ℕ and J_{r+1} = F(r, J_r), so that J_{r+1} ⊆ J_r and Q(r, ·, ·) holds on J_{r+1}.
3. Recursively pick φ(0) ∈ J_1 and φ(r+1) ∈ J_{r+2} with φ(r+1) > φ(r), using Set.Infinite.exists_gt.
4. φ is StrictMono by strictMono_nat_of_lt_succ.
5. φ(r) and φ(r+1) both lie in J_{r+1}, hence Q(r, φ(r), φ(r+1)).

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
