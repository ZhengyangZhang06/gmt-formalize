# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.pairing_expansion-a1`
- Child DAG node: `root.polyhedral_approximation-a1.pairing_expansion-a1.coordinate_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 5 (coordinate bound) of the parent-supplied proof, with details filled in.

Notation. E := ℝ^P = EuclideanSpace ℝ (Fin P). For k ∈ Fin P, e_k := EuclideanSpace.single k 1. Write c_I := euclideanCovectorCoordinate c I = c(fun i => e_{I(i)}).

1. (Unfolding the norm.) By definition, covectorEuclideanNorm c = √S, where S := Σ_{J : Fin n → Fin P} t_J is a sum over the finite type of all maps J : Fin n → Fin P. Here t_J := (c(fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)))² if J is StrictMono, and t_J := 0 otherwise.
2. (Nonnegativity.) Each t_J is either a square or 0, so t_J ≥ 0 for every J.
3. (The term of I.) The underlying map ⇑I : Fin n → Fin P of the order embedding I is StrictMono (OrderEmbedding.strictMono). Also EuclideanSpace.basisFun (Fin P) ℝ (I i) = EuclideanSpace.single (I i) 1 = e_{I(i)} for every i (EuclideanSpace.basisFun_apply). Hence t_{⇑I} = (c(fun i => e_{I(i)}))² = c_I².
4. (One term is at most the sum.) A single term of a finite sum of nonnegative terms is at most the whole sum (Finset.single_le_sum, using Step 2 and ⇑I ∈ Finset.univ). Therefore c_I² = t_{⇑I} ≤ S.
5. (Square roots.) The real square root is monotone (Real.sqrt_le_sqrt), and √(x²) = |x| (Real.sqrt_sq_eq_abs). Hence |c_I| = √(c_I²) ≤ √S = covectorEuclideanNorm c. ∎

## Key steps

1. covectorEuclideanNorm c = √S, where S = Σ_{J : Fin n → Fin P} t_J is a finite sum of nonnegative terms (squares or 0).
2. For J = ⇑I, which is StrictMono, t_J = c_I², using EuclideanSpace.basisFun_apply to identify basisFun (I i) with e_{I(i)}.
3. c_I² ≤ S by Finset.single_le_sum.
4. |c_I| = √(c_I²) ≤ √S by Real.sqrt_sq_eq_abs and Real.sqrt_le_sqrt.

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
