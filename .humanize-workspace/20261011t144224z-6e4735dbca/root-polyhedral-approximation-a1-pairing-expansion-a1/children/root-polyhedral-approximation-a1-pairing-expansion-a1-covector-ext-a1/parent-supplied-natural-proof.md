# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.pairing_expansion-a1`
- Child DAG node: `root.polyhedral_approximation-a1.pairing_expansion-a1.covector_ext-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 (sorting injective tuples) and the extensionality bullet of Step 3 of the parent-supplied proof, with details filled in.

Notation. E := ℝ^P = EuclideanSpace ℝ (Fin P). For k ∈ Fin P, e_k := EuclideanSpace.single k 1. Let b := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis be the standard basis of E; b k = e_k by EuclideanSpace.basisFun_apply. By definition, euclideanCovectorCoordinate γ I = γ(fun j => e_{I(j)}). Let f := α.toAlternatingMap and g := β.toAlternatingMap be the underlying alternating maps; they take the same values as α and β.

1. (Reduction to alternating maps.) A continuous alternating map is determined by its underlying alternating map (ContinuousAlternatingMap.toAlternatingMap_injective). So it suffices to prove f = g.
2. (Reduction to injective basis tuples.) By Module.Basis.ext_alternating for the basis b, it suffices to prove f(fun i => b(v i)) = g(fun i => b(v i)) for every injective v : Fin n → Fin P. Fix such an injective v.
3. (Sorting.) Let σ := Tuple.sort v, a permutation of Fin n. By Tuple.monotone_sort, v ∘ σ is monotone. It is also injective, as a composition of the injective maps σ and v, so it is strictly monotone (Monotone.strictMono_of_injective). Let I := OrderEmbedding.ofStrictMono (v ∘ σ) ∈ SimonMultiIndex n P, so I(j) = v(σ(j)) for all j ∈ Fin n. Since σ is a bijection, range I = range v. Thus I is the increasing enumeration of range v, the multi-index I_J of the parent proof's Step 2.
4. (Tuple identity.) (fun i => b(v i)) = (fun j => e_{I(j)}) ∘ σ⁻¹. Indeed, for each i ∈ Fin n, e_{I(σ⁻¹(i))} = e_{v(σ(σ⁻¹(i)))} = e_{v(i)} = b(v i).
5. (Sign rule.) Let h be an alternating map on E with arguments indexed by Fin n, u a tuple and τ a permutation of Fin n. Then h(u ∘ τ) = sign(τ) • h(u) (AlternatingMap.map_perm). Apply this with u := (fun j => e_{I(j)}) and τ := σ⁻¹, and use Step 4. For γ ∈ {α, β} this gives γ(fun i => b(v i)) = sign(σ⁻¹) • γ(fun j => e_{I(j)}) = sign(σ⁻¹) • euclideanCovectorCoordinate γ I.
6. (Conclusion.) By hypothesis, euclideanCovectorCoordinate α I = euclideanCovectorCoordinate β I. By Step 5, f(fun i => b(v i)) = sign(σ⁻¹) • euclideanCovectorCoordinate α I = sign(σ⁻¹) • euclideanCovectorCoordinate β I = g(fun i => b(v i)). Since v was an arbitrary injective tuple, Step 2 gives f = g, and Step 1 gives α = β.
7. (Uniformity.) No case split is needed. For n = 0 the only v is the empty tuple, which is injective, and I is the empty embedding. For n > P there is no injective v : Fin n → Fin P, so the condition in Step 2 holds vacuously and α = β (both are 0). ∎

## Key steps

1. Reduce to underlying alternating maps (ContinuousAlternatingMap.toAlternatingMap_injective), then to injective basis tuples (Module.Basis.ext_alternating with the standard basis b, b k = e_k).
2. Sort an injective v: σ := Tuple.sort v makes v ∘ σ monotone and injective, hence strictly increasing; this defines I := OrderEmbedding.ofStrictMono (v ∘ σ) ∈ SimonMultiIndex n P.
3. Since (b ∘ v) = e_I ∘ σ⁻¹, AlternatingMap.map_perm gives γ(b ∘ v) = sign(σ⁻¹) • euclideanCovectorCoordinate γ I for γ = α and γ = β.
4. The coordinate hypothesis gives agreement on every injective basis tuple, hence α = β.

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
