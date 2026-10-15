# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1`
- Child DAG node: `root.boundary_rectifiability-a1.restrict_domain_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (P3) of the parent proof, second half (“Y ∈ D_k(ℝ^P) restricts to Y|_U ∈ D_k(U), and if Y = τ(M,θ,ξ) then Y|_U = τ(M∩U,θ,ξ) is integer multiplicity; the weighted tangent space at x ∈ U only depends on M, θ near x”), stated for a general open W ⊆ U. This argument has been kernel-checked against the frozen definitions using the sibling lemma tangent_locality.

Notation. H := Hᵏ = `μHE[k]`; Y|_W := `Y.restrictDomain hWU`, Y|_W(ω) = Y(ω) for ω ∈ Dᵏ(W), where ω is regarded as an element of Dᵏ(U) with the same underlying form (`testFormOnInclusion`).

1. (Data.) Since Y is integer multiplicity, Y(ω) = ∫_M θ⟨ω,ξ⟩ dH for all ω ∈ Dᵏ(U), where `IsRectifiableTriple U k M θ ξ` holds and θ(x) ∈ ℕ for x ∈ M. Put M′ := M ∩ W. We show Y|_W = τ(M′, θ, ξ) and that (M′, θ, ξ) is an integer multiplicity triple on W.
2. (Action.) Let ω ∈ Dᵏ(W). If x ∉ W then x ∉ tsupport ω ⊆ W, so ω(x) = 0 and θ(x)⟨ω(x), ξ(x)⟩ = θ(x)ξ(x)(0) = 0. As W is open (Borel), H⌞(M ∩ W) = (H⌞M)⌞W (`Measure.restrict_restrict`), and the integral against (H⌞M)⌞W of a function vanishing off W equals its integral against H⌞M. Hence Y|_W(ω) = Y(ω) = ∫_M θ⟨ω,ξ⟩dH = ∫_{M∩W} θ⟨ω,ξ⟩dH = τ(M′,θ,ξ)(ω).
3. (Triple conditions on W.) (a) M′ ⊆ W. (b) M′ is H-null-measurable: M is, and W is Borel. (c) M′ ⊆ M, so M′ is countably k-rectifiable (`CountablyRectifiable.mono`). (d) For x ∈ M′ ⊆ M: θ(x) > 0 and θ(x) ∈ ℕ. (e) If K ⊆ W is compact then K ⊆ U, so θ is H-integrable on M ∩ K and therefore on the subset M′ ∩ K. (f) ξ is a.e. strongly measurable for H⌞M and H⌞M′ ≤ H⌞M, so it is a.e. strongly measurable for H⌞M′.
4. (Orientation.) Because H⌞M′ ≤ H⌞M, the orientation property of (M,θ,ξ) holds for H⌞M′-a.e. x; and H⌞M′-a.e. x lies in M′ (M′ is null-measurable; `ae_restrict_mem₀`). Fix such an x: x ∈ M ∩ W, and there is an orthonormal τ = (τ₁,…,τ_k) with `HasWeightedApproximateTangentSpaceAt k M θ x (span τ)` and ξ(x) = ±simpleNVector τ. Apply the sibling lemma tangent_locality with (M, θ), (M′, θ′) := (M ∩ W, θ), V := W (open, x ∈ W): its hypotheses hold because (M Δ (M∩W)) ∩ W = (M ∖ W) ∩ W = ∅ has H-measure 0, θ = θ everywhere, and θ(x) = θ(x). Hence `HasWeightedApproximateTangentSpaceAt k (M ∩ W) θ x (span τ)`, and τ, ξ(x) witness the orientation property of (M′, θ, ξ) at x.
5. (Conclusion.) By 2–4, Y|_W = τ(M ∩ W, θ, ξ) with an integer multiplicity triple on W, i.e. `IsIntegerMultiplicity (Y.restrictDomain hWU)`.

## Key steps

1. Write Y = τ(M,θ,ξ) and set M′ := M ∩ W.
2. For test forms supported in W the τ-integrand vanishes off W, so Y|_W = τ(M ∩ W, θ, ξ).
3. Measurability, rectifiability, positivity, integrality and local integrability pass to the subset M ∩ W (compact subsets of W are compact subsets of U).
4. The orientation property passes to H⌞(M∩W)-a.e. point by tangent_locality with V := W, since (M Δ (M∩W)) ∩ W = ∅.

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
