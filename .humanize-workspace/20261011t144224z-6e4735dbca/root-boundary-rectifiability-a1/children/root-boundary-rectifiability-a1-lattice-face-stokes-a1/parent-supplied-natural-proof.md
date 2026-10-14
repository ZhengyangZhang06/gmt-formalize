# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1`
- Child DAG node: `root.boundary_rectifiability-a1.lattice_face_stokes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (P4) of the parent proof, “By Stokes' theorem on a cube (Fubini and the fundamental theorem of calculus), ∂[[F]] = Σ_{i}(−1)^{i−1}([[F_i⁺]] − [[F_i⁻]])”, written with the exact face indexing and orientation of the frozen `latticeFace`, `latticeFaceAction` (indices i = 0,…,m, so the sign is (−1)^i).

Notation. F = (z, α) ∈ `LatticeFaceIndex (m+1) P`: z ∈ ℤ^P, α : Fin(m+1) ↪o Fin P strictly increasing. Write ε_j := e_{α(j)} (`EuclideanSpace.single (α j) 1`), ρz := Σ_l ρz_l e_l. |F| := `latticeFace ρ F` = {x : ρz_{α(j)} ≤ x_{α(j)} ≤ ρ(z_{α(j)}+1) for all j, x_l = ρz_l for l ∉ range α}. [[F]](η) := `latticeFaceAction ρ F η` = ∫_{|F|} η(x)(ε₀,…,ε_m) dH^{m+1}(x). For i ∈ Fin(m+1) let α_i := α ∘ succAbove_i (`(Fin.succAboveOrderEmb i).trans α`, strictly increasing), G_i⁺ := (z + e_{α(i)}, α_i) and G_i⁻ := (z, α_i) ∈ `LatticeFaceIndex m P` (in Lean z + e_{α(i)} is `F.1 + Pi.single (F.2 i) 1`).

Proof.
1. (Parametrizations.) For d ∈ ℕ, w ∈ ℤ^P and a strictly increasing γ : Fin d → Fin P let A_{w,γ} : ℝ^d → ℝ^P, A_{w,γ}(s) := ρw + Σ_j s_j e_{γ(j)}. Since the e_{γ(j)} are orthonormal, A_{w,γ} is an isometry, and latticeFace ρ (w,γ) = A_{w,γ}([0,ρ]^d) (for x in the face put s_j := x_{γ(j)} − ρw_{γ(j)}).
2. (Measures.) Hᵈ = `μHE[d]` is invariant under isometries and equals Lebesgue measure on ℝ^d (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`); hence the push-forward of Lebesgue measure under A_{w,γ} is Hᵈ⌞range(A_{w,γ}) (`Isometry.map_euclideanHausdorffMeasure`), and for every continuous g, ∫_{latticeFace ρ (w,γ)} g dHᵈ = ∫_{[0,ρ]^d} g(A_{w,γ}(s)) ds. (For d = 0, ℝ⁰ is a point carrying the unit Dirac mass, the face is the point ρw, and both sides equal g(ρw).)
3. (Exterior derivative.) ω is smooth, so by `exteriorDerivative_apply` (Mathlib `extDeriv_apply`), for every x: dω(x)(ε₀,…,ε_m) = Σ_{i=0}^m (−1)^i D_{ε_i}h_i(x), where h_i(y) := ω(y)(removeNth_i(ε)) = ω(y)(e_{α_i(0)},…,e_{α_i(m−1)}) and D_{ε_i}h_i(x) = (d/dt)h_i(x + tε_i)|_{t=0}. Note that h_i is exactly the integrand of [[G_i^±]](ω).
4. (Fubini and FTC.) With A := A_{z,α}: ∫_{|F|}D_{ε_i}h_i dH^{m+1} = ∫_{[0,ρ]^{m+1}} ∂_{s_i}(h_i∘A)(s) ds (step 2 and the chain rule: ∂_{s_i}(h_i∘A)(s) = Dh_i(A(s))ε_i). Write s = (s_i, s′) with s′ ∈ [0,ρ]^m the remaining coordinates in increasing order (s′_j = s_{succAbove_i(j)}). h_i∘A is C¹, so by Fubini and the fundamental theorem of calculus on [0,ρ] (ρ > 0): ∫_{[0,ρ]^{m+1}}∂_{s_i}(h_i∘A) ds = ∫_{[0,ρ]^m}[h_i(A(ρ,s′)) − h_i(A(0,s′))] ds′.
5. (Identification of the faces.) A(ρ, s′) = ρ(z + e_{α(i)}) + Σ_j s′_j e_{α_i(j)} = A_{z+e_{α(i)},α_i}(s′) and A(0, s′) = A_{z,α_i}(s′). Indeed latticeFace ρ G_i⁺ is the face of |F| on which x_{α(i)} = ρ(z_{α(i)} + 1): the coordinate α(i) is not in range α_i, and (z + e_{α(i)})_l = z_l for l ≠ α(i); similarly latticeFace ρ G_i⁻ is the face x_{α(i)} = ρz_{α(i)}. By step 2 (d = m), ∫_{[0,ρ]^m}h_i(A_{z+e_{α(i)},α_i}(s′))ds′ = [[G_i⁺]](ω) and ∫_{[0,ρ]^m}h_i(A_{z,α_i}(s′))ds′ = [[G_i⁻]](ω).
6. (Conclusion.) Integrating step 3 over |F| and using steps 4–5: [[F]](dω) = Σ_{i=0}^m (−1)^i([[G_i⁺]](ω) − [[G_i⁻]](ω)), which is the asserted identity (all integrands are continuous on compact faces, hence integrable; the case m = 0 is the fundamental theorem of calculus on the segment |F|, with [[G_0^±]](ω) = ω(endpoint)(∅)).

## Key steps

1. Each lattice face is the image of a cube [0,ρ]^d under an isometric affine map, so Hᵈ on the face is Lebesgue measure on the parameter cube.
2. dω(x)(e_{α(0)},…,e_{α(m)}) = Σ_i (−1)^i ∂_{α(i)}[ω(·)(e_{α∘succAbove_i})](x) (Mathlib extDeriv_apply).
3. Fubini and the fundamental theorem of calculus in the α(i)-direction turn ∫_F ∂_{α(i)}h_i into the difference of the integrals over the opposite faces x_{α(i)} = ρ(z_{α(i)}+1) and x_{α(i)} = ρz_{α(i)}.
4. These faces are latticeFace ρ (z + e_{α(i)}, α∘succAbove_i) and latticeFace ρ (z, α∘succAbove_i), whose integrands are the h_i.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def |^structure |^abbrev ' project/GMT/Ch06/Contract.lean`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (byte-identical)`
- `python3 gmt-compare.py contract_scope / child_modules replay (open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end)`
- `rg -n 'theorem extDeriv_apply' mathlib/Mathlib`
- `rg -n 'theorem Isometry.map_euclideanHausdorffMeasure|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero' mathlib/Mathlib`
- `rg -n 'theorem hausdorffMeasure_image_le' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'def succAboveOrderEmb' mathlib/Mathlib/Order/Fin/Basic.lean`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `rg -n 'theorem exists_isSubordinate' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `rg -n 'structure ContDiffBump' mathlib/Mathlib`
- `rg -n 'theorem norm_fderiv_le_of_lipschitz' mathlib/Mathlib`
- `rg -n 'eq_smul_basis_det' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `rg -n 'theorem le_restrict_apply|theorem restrict_congr_set|theorem restrict_restrict' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `rg -il 'cauchy.?binet|CauchyBinet' mathlib/Mathlib (no match)`
- `rg -il 'poincare inequality|Poincaré inequality' mathlib/Mathlib (no match)`
- `grep -n 'theorem|def' simongmt Chapter02/BV.lean (IsLocallyBV and lower semicontinuity only; no BV Poincaré or trace inequality)`
- `inspect simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,FormsDuality,Forms,AffineCurrentPushforward}.lean and Chapter03/Rectifiable.lean (GeometricCurrentOn, boundary, massOn, covectorEuclideanNorm, restrictDomain, testFormOnInclusion, simpleNVector, wedgeCovectors_apply_det, exteriorDerivative_apply, blowUpMap, HasWeightedApproximateTangentSpaceAt, CountablyRectifiable)`
- `lake build GMT.Ch06.Submission (scratch /tmp/br_decomp at frozen commit d8d46c9, pinned shared packages)`
- `lake env lean Scratch/FinalCheck.lean (10 frozen child statements, parent assembly, finite_mass_boundary_im from its dependencies; #print axioms)`
- `lake env lean Scratch/ComparatorChallenges.lean (NodeChallenge modules generated by gmt-compare.py child_modules for all 10 statements; 0 errors)`
- `lake build Scratch.AProof (Scratch/TLProof.lean, Scratch/AProof.lean: tangent_locality and restrict_domain_im fully proved; #print axioms)`
- `python3 scan of dag.json lean_name values (no collision with br_* names)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/br_decomp/Scratch/FinalCheck.lean`
- `/tmp/br_decomp/Scratch/ComparatorChallenges.lean`
- `/tmp/br_decomp/Scratch/TLProof.lean`
- `/tmp/br_decomp/Scratch/AProof.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Submission.lean is byte-identical to it. Mathlib provides extDeriv_apply (sign (−1)^i with removeNth), isometry invariance of μHE and its identification with Lebesgue measure, Lipschitz image bounds for Hausdorff measure, Fin.succAboveOrderEmb, the open-set fundamental lemma IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (any measure, local integrability only), smooth partitions of unity, ContDiffBump cut-offs, norm_fderiv_le_of_lipschitz and AlternatingMap.eq_smul_basis_det. There is no Cauchy–Binet and no BV Poincaré inequality in Mathlib (no match), and SimonGMT's BV.lean has no Poincaré or trace inequality; hence the children avoid Cauchy–Binet (dual-covector evaluation, operator-norm bounds) and prove the needed BV estimates on boxes directly. SimonGMT supplies restrictDomain, testFormOnInclusion, exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset, boundary_boundary, WeaklyConvergesOn.boundary, massOn_mono, wedgeCovectors_apply_det and countablyRectifiable_iUnion. In a scratch build of the frozen commit, all ten child statements elaborate in the comparator's exact child scope (modules generated by gmt-compare.py); the parent BoundaryRectifiability typechecks from restrict_domain_im, local_to_global_im, finite_mass_boundary_im, localization and the three sibling theorems; finite_mass_boundary_im typechecks from zero_dim_weak_limit, lattice_boundary_im and lattice_approximation; tangent_locality and restrict_domain_im are fully proved with axioms [propext, Classical.choice, Quot.sound]. No br_* name is reserved in the DAG. These checks do not certify the remaining analytic children.
