# Parent-supplied natural-language proof

- Parent DAG node: `root.isoperimetric-a1`
- Child DAG node: `root.isoperimetric-a1.covector_eval_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 of the parent proof bounds |⟨ω(x), ξ(x)⟩| using |ξ(x)| = 1 for ξ(x) = ±τ_1 ∧ ⋯ ∧ τ_n with τ orthonormal. Only finiteness of the mass is needed there, so any constant suffices; this lemma supplies the elementary bound with constant P^n (no Cauchy–Binet identity is needed).

Notation. e_a := EuclideanSpace.basisFun (Fin P) ℝ a = EuclideanSpace.single a 1 for a ∈ Fin P; for f : Fin n → Fin P write e_f := (e_{f(1)}, …, e_{f(n)}) and α(e_f) for α applied to this tuple. N(α) := covectorEuclideanNorm α = sqrt(Σ_{I : Fin n → Fin P} (if I is strictly increasing then α(e_I)² else 0)) ≥ 0.

1. Claim: |α(e_f)| ≤ N(α) for every f : Fin n → Fin P.
 (a) If f is not injective, choose i ≠ i' with f(i) = f(i'). The tuple e_f has equal entries in the distinct positions i and i', and α is alternating, so α(e_f) = 0 ≤ N(α) (`ContinuousAlternatingMap.map_eq_zero_of_eq`).
 (b) If f is injective, let σ := Tuple.sort f, a permutation of Fin n such that f ∘ σ is monotone (`Tuple.monotone_sort`). The map I := f ∘ σ is monotone and injective, hence strictly increasing. Since e_I = e_f ∘ σ and α is alternating, α(e_f ∘ σ) = sign(σ) · α(e_f) (`AlternatingMap.map_perm` applied to α.toAlternatingMap), so |α(e_f)| = |α(e_I)|. As I is strictly increasing, α(e_I)² is one of the nonnegative summands whose sum is N(α)², so α(e_I)² ≤ N(α)² and |α(e_I)| = sqrt(α(e_I)²) ≤ N(α).
2. Expansion. For each j, τ_j = Σ_{a ∈ Fin P} τ_j(a) • e_a (expansion in the standard orthonormal basis). By multilinearity of α (expansion of a multilinear map applied to sums and extraction of scalars: `ContinuousMultilinearMap.map_sum` and `map_smul_univ` applied to α.toContinuousMultilinearMap):
 α(τ_1, …, τ_n) = Σ_{f : Fin n → Fin P} (Π_{j ∈ Fin n} τ_j(f(j))) · α(e_f).
3. For every j and a, |τ_j(a)| ≤ ‖τ_j‖ ≤ 1 (a coordinate of a Euclidean vector is bounded by its norm, `PiLp.norm_apply_le`). Hence |Π_j τ_j(f(j))| = Π_j |τ_j(f(j))| ≤ 1 for every f (a product of numbers in [0, 1], `Finset.prod_le_one₀`).
4. By the triangle inequality and steps 1 and 3, |α(τ_1, …, τ_n)| ≤ Σ_f |Π_j τ_j(f(j))| · |α(e_f)| ≤ Σ_f N(α) = card(Fin n → Fin P) · N(α) = P^n · N(α). (For n = 0 the sum has the single empty f, the product is 1 and the bound reads |α()| ≤ N(α).)

## Key steps

1. |α(e_f)| ≤ covectorEuclideanNorm α for every f : Fin n → Fin P: zero if f is not injective; otherwise sort f by a permutation σ and use α(e_f ∘ σ) = sign σ · α(e_f).
2. Expand α(τ) multilinearly in the standard basis: a sum over the P^n maps f of (Π_j τ_j(f j)) α(e_f).
3. Each coefficient satisfies |Π_j τ_j(f j)| ≤ 1 because |τ_j(a)| ≤ ‖τ_j‖ ≤ 1.
4. Summing gives |α(τ)| ≤ P^n · covectorEuclideanNorm α.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `grep -rn "euclideanHausdorffMeasure" Mathlib (snapshot mathlib) -> Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n -i "cauchy.?binet|det_mul_eq_sum" Mathlib/LinearAlgebra/Matrix (no match)`
- `grep -rn -i -l "binet" Mathlib/LinearAlgebra Mathlib/Analysis/InnerProductSpace (only LinearAlgebra/CrossProduct.lean remark)`
- `grep -n "theorem exists_isSubordinate|theorem exists_contDiff_tsupport_subset" Mathlib/Geometry/Manifold/PartitionOfUnity.lean Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `grep -n "^theorem" Mathlib/Geometry/Manifold/PartitionOfUnity.lean | grep -i "zero_one|one_nhds|exists_contMDiff"`
- `grep -n "volume_preserving" Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `grep -n "theorem map_perm|theorem map_eq_zero_of_eq|theorem map_sum" Mathlib/Topology/Algebra/Module/Alternating/Basic.lean Mathlib/LinearAlgebra/Alternating/Basic.lean Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean Mathlib/LinearAlgebra/Multilinear/Basic.lean`
- `grep -n "def sort|theorem monotone_sort" Mathlib/Data/Fin/Tuple/Sort.lean`
- `read SimonGMT Chapter06 Mass.lean, Currents.lean, CurrentLocalEquality.lean, Forms.lean, FormsDuality.lean (pinned simongmt package used by the snapshot project)`
- `sed -n 1925,2000p book/chapter-06.txt (printed 6.1 proof)`
- `python3 -I: gmt-compare.py contract_scope(Contract.lean, GMT.Ch06.main_theorem) and lean_contract.validate_lean_statement on the 5 child statements`
- `python3 -I: dag.json lean_name collision check (26 nodes, no collision with isoperimetric_* names)`
- `lake build GMT.Ch06.Submission (scratch /tmp/iso_a1_decomp_check, frozen d8d46c9, pinned packages)`
- `lake env lean Scratch/IsoStmts.lean (5 statements elaborate in comparator scope)`
- `lake env lean Scratch/IsoAsm0.lean; Scratch/IsoAsm1.lean (rw m+1+(ℓ+1)=m+2+ℓ; IsoperimetricTheorem from DeformationTheorem + 3 children; #print axioms)`
- `lake env lean Scratch/IsoC3.lean (finite_mass from vanish_off_support + covector_eval_bound; #print axioms)`
- `lake build GMT.IsoFakeSub; lake env lean Scratch/NodeChallenge{0..4}.lean Scratch/NodeSolution{0..4}.lean; Scratch/IsoParentByName.lean`
- `lake env lean Scratch/ReviewAll.lean (independent reviewer: all 5 child statements proved, iso_full : DeformationTheorem → IsoperimetricTheorem; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/CrossProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1/parent-child-handoff.json`
- `/tmp/iso_a1_decomp_check/Scratch/IsoStmts.lean`
- `/tmp/iso_a1_decomp_check/Scratch/IsoAsm1.lean`
- `/tmp/iso_a1_decomp_check/Scratch/IsoC3.lean`
- `/tmp/iso_a1_decomp_check/GMT/IsoFakeSub.lean`
- `/tmp/iso_a1_decomp_check/Scratch/IsoParentByName.lean`
- `/tmp/iso_a1_decomp_check/Scratch/ReviewAll.lean`

Snapshot findings (project d8d46c95, Mathlib 25730c7c). The frozen Contract defines IsoperimetricTheorem, DeformationTheorem, IsLatticeChain, latticeFace and latticeFaceAction as used. SimonGMT supplies covectorEuclideanNorm, massAdmissibleOn, massOn and le_massOn (Mass.lean); VanishesOn, zeroRegion, support = U \ zeroRegion and isOpen_zeroRegion (CurrentLocalEquality.lean); GeometricCurrentOn.ext and the zero current (Currents.lean); and simpleNVector and wedgeCovectors_apply_det (FormsDuality.lean). Mathlib normalises μHE[d] on EuclideanSpace ℝ (Fin d) and provides Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, so a ρ-lattice k-face has μHE[k]-measure ρ^k. Mathlib also provides SmoothPartitionOfUnity.exists_isSubordinate, exists_contMDiffMap_one_nhds_of_subset_interior, PiLp.volume_preserving_ofLp, AlternatingMap.map_perm, ContinuousAlternatingMap.map_eq_zero_of_eq, multilinear map_sum, and Tuple.sort with monotone_sort. There is no Cauchy–Binet theorem in Mathlib (no match), so the covector child uses the elementary constant P^n. Kernel checks in a scratch copy of the frozen project: all five child statements elaborate in the comparator scope and pass validation; NodeSolution `exact Submission.<name>` typechecks; IsoperimetricTheorem follows from DeformationTheorem plus finite_mass, zero_mass_iff and lattice_mass_lower_bound; finite_mass follows from vanish_off_support and covector_eval_bound; and the independent reviewer's ReviewAll.lean proves all five exact statements. All checks use only propext, Classical.choice and Quot.sound. No lean_name collides with the 26 DAG nodes.
