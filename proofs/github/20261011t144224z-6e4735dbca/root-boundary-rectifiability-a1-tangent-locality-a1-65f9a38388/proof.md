# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1`
- Child DAG node: `root.boundary_rectifiability-a1.tangent_locality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the locality step (P5)(iv)/(P3) of the parent proof (“the weighted approximate tangent space at x only depends on M, θ near x, modulo Hᵏ-null sets; for small r the blow-up integrals only see x + r·spt f ⊆ V, and Hᵏ(η_{x,r}Z) = r^{−k}Hᵏ(Z) = 0 for null Z”), written out against the frozen definition `HasWeightedApproximateTangentSpaceAt` (Simon Ch. 3, 1.7). This argument has been kernel-checked against the frozen definitions (axioms propext, Classical.choice, Quot.sound only).

Notation. H := Hᵏ = `μHE[k]` on ℝ^P. For r > 0, η_r(y) := r⁻¹(y − x) (`blowUpMap x r`). By definition, `HasWeightedApproximateTangentSpaceAt k M θ x L` means: dim L = k (`finrank ℝ L = k`), and for every f ∈ C_c(ℝ^P;ℝ), I_{M,θ}(r) := ∫_{η_r(M)} f(y)θ(x + ry) dH(y) → θ(x)∫_L f dH as r ↓ 0 (limit along 𝓝[>]0).

1. (Null sets under blow-up.) If r > 0 and H(Z) = 0 then H(η_r(Z)) = 0. Indeed |η_r(a) − η_r(b)| = r⁻¹|a − b|, so η_r is Lipschitz with constant r⁻¹ and μH[k](η_r(Z)) ≤ r^{−k}μH[k](Z) (Mathlib `LipschitzWith.hausdorffMeasure_image_le`). Moreover H = c_k·μH[k] with c_k ∈ (0,∞) (`euclideanHausdorffMeasure_def`, `addHaarScalarFactor_volume_hausdorffMeasure_ne_zero`), so H(Z) = 0 ⇒ μH[k](Z) = 0 ⇒ μH[k](η_r(Z)) = 0 ⇒ H(η_r(Z)) = 0.
2. (Elementary facts on η_r.) For r > 0, η_r is a bijection of ℝ^P with inverse y ↦ x + ry. Hence η_r(A ∩ B) = η_r(A) ∩ η_r(B), η_r(A ∖ B) = η_r(A) ∖ η_r(B) for all A, B, and η_r(V) = {y : x + ry ∈ V} is open (preimage of the open V under a continuous map).
3. (Reduction.) The dimension conditions for (M,θ) and (M′,θ′) are the same condition on L. Fix f ∈ C_c(ℝ^P;ℝ). Choose R > 0 with f(y) = 0 whenever |y| ≥ R (tsupport f is compact, hence bounded), and δ > 0 with B_δ(x) ⊆ V (V open, x ∈ V). We prove I_{M,θ}(r) = I_{M′,θ′}(r) for every r ∈ (0, δ/R). Since (0, δ/R) ∈ 𝓝[>]0, the two functions of r agree eventually as r ↓ 0, so I_{M′,θ′}(r) has the same limit θ(x)∫_L f dH, which equals θ′(x)∫_L f dH because θ(x) = θ′(x). This gives `HasWeightedApproximateTangentSpaceAt k M′ θ′ x L`.
4. (Integrands vanish off η_r(V).) Let r ∈ (0, δ/R), g : ℝ^P → ℝ arbitrary, F_g(y) := f(y)g(x + ry). If y ∉ η_r(V) then x + ry ∉ V ⊇ B_δ(x), so r|y| ≥ δ, hence |y| ≥ δ/r > R, f(y) = 0 and F_g(y) = 0.
5. (Step A: cutting by V.) For every S ⊆ ℝ^P and every g: ∫_{η_r(S)} F_g dH = ∫_{η_r(S∩V)} F_g dH. Indeed η_r(S ∩ V) = η_r(S) ∩ η_r(V) (step 2); since η_r(V) is open (measurable), H⌞(η_r(V) ∩ η_r(S)) = (H⌞η_r(S))⌞η_r(V) (`Measure.restrict_restrict`); and the integral of F_g with respect to (H⌞η_r(S))⌞η_r(V) equals its integral with respect to H⌞η_r(S), because F_g vanishes off η_r(V) (step 4; `setIntegral_eq_integral_of_forall_compl_eq_zero`).
6. (Step C: replacing θ by θ′.) ∫_{η_r(M∩V)} F_θ dH = ∫_{η_r(M∩V)} F_{θ′} dH. By hypothesis (H⌞(M∩V)){z : θ(z) ≠ θ′(z)} = 0, so there is a Borel set N ⊇ {z : θ(z) ≠ θ′(z)} with (H⌞(M∩V))(N) = H(N ∩ (M∩V)) = 0 (`exists_measurable_superset_of_null`, `Measure.restrict_apply`). Let N′ := {y : x + ry ∈ N}, a Borel set. Then {y : F_θ(y) ≠ F_{θ′}(y)} ⊆ N′, and N′ ∩ η_r(M∩V) ⊆ η_r(N ∩ (M∩V)) (if y = η_r(z) with z ∈ M ∩ V and x + ry = z ∈ N). By step 1 the right side is H-null, so (H⌞η_r(M∩V))(N′) = H(N′ ∩ η_r(M∩V)) = 0; thus F_θ = F_{θ′} (H⌞η_r(M∩V))-a.e. and the integrals agree (`integral_congr_ae`).
7. (Step B: replacing M by M′.) η_r(M∩V) and η_r(M′∩V) are H-a.e. equal sets: by step 2 their differences are η_r((M∩V)∖(M′∩V)) and η_r((M′∩V)∖(M∩V)), both contained in η_r((M Δ M′) ∩ V), which is H-null by the hypothesis H((M Δ M′) ∩ V) = 0 and step 1. Hence H⌞η_r(M∩V) = H⌞η_r(M′∩V) (`ae_eq_set`, `Measure.restrict_congr_set`).
8. (Conclusion.) For r ∈ (0, δ/R): I_{M,θ}(r) = ∫_{η_r(M∩V)}F_θ dH (step 5) = ∫_{η_r(M∩V)}F_{θ′} dH (step 6) = ∫_{η_r(M′∩V)}F_{θ′} dH (step 7) = I_{M′,θ′}(r) (step 5 applied to M′, θ′). By step 3 the lemma is proved. No measurability of M, M′, θ, θ′ is used.

## Key steps

1. Blow-up maps η_r(y) = r⁻¹(y − x) are Lipschitz, so they map Hᵏ-null sets to Hᵏ-null sets.
2. Choose R with spt f ⊆ B_R(0) and δ with B_δ(x) ⊆ V; for r < δ/R the blow-up integrands vanish off the open set η_r(V).
3. Hence each blow-up integral over η_r(S) equals the one over η_r(S ∩ V).
4. On η_r(M ∩ V) the weights θ(x+r·) and θ′(x+r·) agree a.e., and η_r(M∩V), η_r(M′∩V) are a.e. equal.
5. The blow-up integrals of (M,θ) and (M′,θ′) coincide for all small r and θ(x) = θ′(x), so the limits and hence the weighted tangent spaces agree.

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
