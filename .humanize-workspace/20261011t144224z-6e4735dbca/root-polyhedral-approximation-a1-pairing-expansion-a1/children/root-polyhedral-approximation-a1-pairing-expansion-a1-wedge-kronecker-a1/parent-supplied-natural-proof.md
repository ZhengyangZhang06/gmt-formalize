# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.pairing_expansion-a1`
- Child DAG node: `root.polyhedral_approximation-a1.pairing_expansion-a1.wedge_kronecker-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 of the parent-supplied proof (dx^I on increasing basis tuples), with details filled in.

Notation. E := ℝ^P = EuclideanSpace ℝ (Fin P). For k ∈ Fin P, e_k := EuclideanSpace.single k 1 and proj_k := EuclideanSpace.proj k, so proj_k(y) = y_k for y ∈ E. By definition, euclideanCovectorCoordinate ω J = ω(fun j => e_{J(j)}) for ω ∈ Covector E n and J ∈ SimonMultiIndex n P. Fix I ∈ SimonMultiIndex n P. It is an order embedding Fin n ↪o Fin P, hence injective. Put dx^I := wedgeCovectors n (fun j => proj_{I(j)}).

1. (Matrix entries.) For a, b ∈ Fin P, proj_a(e_b) = (EuclideanSpace.single b 1)(a), which is 1 if a = b and 0 otherwise (PiLp.single_apply). Hence, for J ∈ SimonMultiIndex n P and i, j ∈ Fin n, proj_{I(i)}(e_{J(j)}) is 1 if I(i) = J(j) and 0 otherwise.
2. (Determinant formula.) Let J ∈ SimonMultiIndex n P. By wedgeCovectors_apply_det (SimonGMT; Simon 6.1.1), euclideanCovectorCoordinate dx^I J = dx^I(fun j => e_{J(j)}) = det M_J, where M_J := Matrix.of (fun i j => proj_{I(i)}(e_{J(j)})). By Step 1, (M_J)_{ij} is 1 if I(i) = J(j) and 0 otherwise.
3. (Case J = I.) (M_I)_{ij} = 1 iff I(i) = I(j) iff i = j, because I is injective (OrderEmbedding.injective). So M_I is the identity matrix entrywise (Matrix.one_apply), and det M_I = 1 (Matrix.det_one). By Step 2, euclideanCovectorCoordinate dx^I I = 1. This is the first conjunct.
4. (Some row index is missing from J.) Let J ∈ SimonMultiIndex n P with J ≠ I. We claim some i ∈ Fin n satisfies I(i) ≠ J(j) for every j ∈ Fin n. Suppose not. Then every I(i) equals some J(j), so Set.range I ⊆ Set.range J. Since I and J are injective, Set.ncard (Set.range I) = Nat.card (Fin n) = Set.ncard (Set.range J) (Set.ncard_range_of_injective). A subset of a finite set with at least as many elements equals that set (Set.eq_of_subset_of_ncard_le; Set.range J is finite), so Set.range I = Set.range J. Two order embeddings of the well-order Fin n with the same range are equal (OrderEmbedding.range_inj_of_wellFoundedLT), so I = J. This contradicts J ≠ I.
5. (Case J ≠ I.) Take i as in Step 4. By Step 1, (M_J)_{ij} = 0 for every j ∈ Fin n, so row i of M_J is zero and det M_J = 0 (Matrix.det_eq_zero_of_row_eq_zero). By Step 2, euclideanCovectorCoordinate dx^I J = 0. Since J ≠ I was arbitrary, this is the second conjunct.
6. (Uniformity.) No case split on n or P is needed. For n = 0, M_I is the empty matrix. It equals the identity, so det M_I = 1. SimonMultiIndex 0 P has exactly one element, so the second conjunct is vacuous. For n > P, SimonMultiIndex n P is empty, so the statement is vacuous. ∎

## Key steps

1. proj_{I(i)}(e_{J(j)}) is 1 if I(i) = J(j) and 0 otherwise (PiLp.single_apply), and euclideanCovectorCoordinate dx^I J is the determinant of this matrix (wedgeCovectors_apply_det).
2. J = I: the matrix is the identity because I is injective, so the coordinate is det 1 = 1.
3. J ≠ I: if range I ⊆ range J, equal cardinalities and OrderEmbedding.range_inj_of_wellFoundedLT would force I = J, so some I(i) lies outside range J.
4. Row i of the matrix is then zero, so the coordinate is 0 (Matrix.det_eq_zero_of_row_eq_zero).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean against local-references/197bdd4b88278494/project/GMT/Ch06/ (both byte-identical)`
- `grep -rn 'abbrev Covector|abbrev NVector|abbrev SimonMultiIndex|def wedgeCovectors|theorem wedgeCovectors_apply_det|def euclideanCovectorCoordinate|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT`
- `rg -n 'ext_alternating' mathlib/Mathlib; rg -n 'theorem map_perm' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `rg -n 'range_inj' mathlib/Mathlib/Order (OrderEmbedding.range_inj deprecated 2026-08-13 -> OrderEmbedding.range_inj_of_wellFoundedLT)`
- `rg -n 'def sort|theorem monotone_sort' mathlib/Mathlib/Data/Fin/Tuple/Sort.lean; rg -n 'theorem Monotone.strictMono_of_injective' mathlib/Mathlib/Order; rg -n 'def ofStrictMono' mathlib/Mathlib/Order/Hom/Basic.lean`
- `rg -n 'theorem det_eq_zero_of_row_eq_zero|theorem det_one' mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `rg -n 'toAlternatingMap_injective|theorem sum_apply|theorem smul_apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `rg -n 'proj|single_apply|basisFun_apply' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean; rg -n 'lemma single_apply' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean (EuclideanSpace.single_apply deprecated -> PiLp.single_apply)`
- `rg -n 'eq_of_subset_of_ncard_le|ncard_range_of_injective' mathlib/Mathlib/Data/Set/Card.lean; rg -n 'eq_of_subset_of_card_le|card_image_of_injective' mathlib/Mathlib/Data/Finset/Card.lean`
- `rg -n 'RelEmbedding.instFintype' mathlib/Mathlib/Data/Fintype/Pi.lean`
- `python3 scan of dag.json lean_statement fields and nodes/*/decomposition-v*.json subproblems for 'euclideanCovectorCoordinate|wedgeCovectors|covectorEuclideanNorm'`
- `grep -rl 'polyhedral_approx_pairing_wedge_kronecker|polyhedral_approx_pairing_covector_ext|polyhedral_approx_pairing_coordinate_bound' dag.json nodes/ project/ simongmt/ (no match)`
- `grep -n 'dx\^|1\.5|1\.6|1\.7' book/chapter-06.txt (Simon 6.1.1-1.2, 1.5-1.7)`
- `python3 -I gmt-compare.contract_scope(Contract.lean, 'GMT.Ch06.main_theorem'); lean_contract.validate_lean_statement on the three child types`
- `lake build GMT.Ch06.Submission (scratch /tmp/pe_decomp_check_1996, frozen d8d46c9, pinned packages)`
- `lake env lean Scratch/Probe.lean (#synth DecidableEq (SimonMultiIndex 2 3) fails; #synth Fintype (SimonMultiIndex 2 3) = RelEmbedding.instFintype)`
- `lake env lean Scratch/Final.lean; lake env lean Scratch/ThreeWay.lean (child proofs, comparator-format targets, selected frozen type as _root_.HumanizeNodeComparator.target from the three children; #print axioms = [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Hom/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Monotone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Hom/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fintype/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-pairing-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-pairing-expansion-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-covector-expansion-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1-covector-expansion-a1/parent-supplied-natural-proof.md`
- `/tmp/pe_decomp_check_1996/Scratch/Probe.lean`
- `/tmp/pe_decomp_check_1996/Scratch/Final.lean`
- `/tmp/pe_decomp_check_1996/Scratch/ThreeWay.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract and a byte-identical Submission with no Submission.* declarations.

SimonGMT supplies the definitions the children use: Covector; NVector; SimonMultiIndex := Fin n ↪o Fin p; wedgeCovectors with wedgeCovectors_apply_det (Simon 6.1.1); euclideanCovectorCoordinate, defined as c(fun j => EuclideanSpace.single (I j) 1); and covectorEuclideanNorm, the square root of a sum over StrictMono J : Fin n → Fin P of squared basisFun evaluations. SimonGMT has no Kronecker-duality, increasing-coordinate extensionality or coordinate-bound lemma.

The pinned Mathlib provides every tool cited in the child proofs: Module.Basis.ext_alternating, AlternatingMap.map_perm, Tuple.sort/Tuple.monotone_sort, Monotone.strictMono_of_injective, OrderEmbedding.ofStrictMono, OrderEmbedding.range_inj_of_wellFoundedLT, Set.ncard_range_of_injective, Set.eq_of_subset_of_ncard_le, Matrix.one_apply/det_one/det_eq_zero_of_row_eq_zero, ContinuousAlternatingMap.toAlternatingMap_injective, PiLp.single_apply and EuclideanSpace.basisFun_apply. The proofs cite OrderEmbedding.range_inj_of_wellFoundedLT and PiLp.single_apply instead of the deprecated aliases OrderEmbedding.range_inj and EuclideanSpace.single_apply.

SimonMultiIndex has a Fintype instance (RelEmbedding.instFintype) but no DecidableEq instance, so the Kronecker child is stated as an explicit conjunction.

The DAG holds two unaccepted nodes, cmb_covector_eq_sum_coord_smul_wedge and slicing_ru_covector_expansion, whose statement equals the expansion step of this proof. That step therefore stays inline in the parent, and no accepted declaration exists to reuse. No DAG or node file reserves polyhedral_approx_pairing_{wedge_kronecker, covector_ext, coordinate_bound} or states their types.

In the scratch build of the frozen project, all three child types pass validate_lean_statement and elaborate in the comparator child scope. Complete Lean proofs of all three children compile. The selected frozen type compiles from only these children as _root_.HumanizeNodeComparator.target, with axioms [propext, Classical.choice, Quot.sound].

Simon's chapter-06.txt §1 (1.1–1.2, 1.5–1.7) states the expansion ω = Σ ω_α dx^α with ω_α = ω(e_{i1},…,e_{in}) as 'one easily checks'. The children supply exactly those checks.
