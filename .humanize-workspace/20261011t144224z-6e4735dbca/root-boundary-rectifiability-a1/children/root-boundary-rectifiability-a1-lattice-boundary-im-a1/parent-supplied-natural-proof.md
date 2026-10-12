# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1`
- Child DAG node: `root.boundary_rectifiability-a1.lattice_boundary_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (P4) of the parent proof: “For β : 𝓛_k(ρ) → ℤ, Σβ_F[[F]] is integer multiplicity (disjoint relative interiors, Hᵏ-null relative boundaries, local finiteness). By Stokes' theorem on a cube ∂[[F]] = Σ ±[[faces]]. Hence the boundary of an integer lattice k-chain is an integer lattice (k−1)-chain, hence integer multiplicity.” Written out for the frozen `IsLatticeChain`, `latticeFace`, `latticeFaceAction`, using the sibling lattice_face_stokes.

Notation. H^d = `μHE[d]`. For d ∈ ℕ and G = (w,γ) ∈ `LatticeFaceIndex d P` put |G| := `latticeFace ρ G` and [[G]](η) := `latticeFaceAction ρ G η` = ∫_{|G|}η(x)(e_{γ(0)},…,e_{γ(d−1)})dH^d. The relative interior is G° := {x : ρw_{γ(j)} < x_{γ(j)} < ρ(w_{γ(j)}+1) ∀j, x_l = ρw_l for l ∉ range γ}.

Facts on lattice faces (ρ > 0, d fixed).
(L1) Distinct indices have disjoint relative interiors; more precisely, if x ∈ G° and x ∈ |G′| with G′ = (w′,γ′) of the same dimension d, then G′ = G. Proof: for x ∈ G°, the set of coordinates l with x_l ∉ ρℤ is exactly range γ. If x ∈ |G′| then x_l ∈ ρℤ for l ∉ range γ′, so range γ ⊆ range γ′, and both have d elements, so γ = γ′ (strictly increasing enumerations of the same set). Then w′_l = x_l/ρ = w_l for l ∉ range γ, and for l = γ(j), x_l/ρ ∈ (w_l, w_l+1) ∩ [w′_l, w′_l+1] with x_l/ρ ∉ ℤ forces w′_l = w_l.
(L2) H^d(|G| ∖ G°) = 0: |G| ∖ G° lies in the finitely many affine planes {x_{γ(j)} = ρw_{γ(j)}} ∩ (ρw + span e_γ), {x_{γ(j)} = ρ(w_{γ(j)}+1)} ∩ (ρw + span e_γ), which are (d−1)-dimensional, hence H^d-null (isometric to ℝ^{d−1}×{0} ⊆ ℝ^d, Lebesgue-null). For d = 0, |G| = G° is a point.
(L3) Local finiteness: a bounded set meets only finitely many faces |G| (|G| ⊆ ρ(w + [0,1]^P), so a set inside [−R,R]^P meets |G| only if −R/ρ − 1 ≤ w_l ≤ R/ρ for all l; finitely many γ).
(L4) If x ∈ G° there is δ > 0 such that B_δ(x) ∩ |G′| = ∅ for every d-dimensional G′ ≠ G, and B_δ(x) ∩ (ρw + span e_γ) ⊆ G°. Proof: by (L3) only finitely many |G′| meet B₁(x); each is closed and, by (L1), does not contain x; take δ below their distances to x and below the distance from x to the relative boundary of the box G°.

Proof.
1. (The chain.) By hypothesis Pc(η) = Σ'_F β_F[[F]](η) for every η ∈ D^{m+1}(ℝ^P). [[F]](η) = 0 unless |F| meets tsupport η (the integrand vanishes on |F| otherwise), and by (L3) only finitely many F have |F| ∩ tsupport η ≠ ∅; so the sum is a finite sum.
2. (Stokes.) Let ω ∈ D^m(ℝ^P). Since tsupport dω ⊆ tsupport ω, ∂Pc(ω) = Pc(dω) = Σ_{F∈𝓕_ω}β_F[[F]](dω), where 𝓕_ω := {F : |F| ∩ tsupport ω ≠ ∅} is finite. By the sibling lattice_face_stokes (ω is smooth), [[F]](dω) = Σ_{i=0}^m(−1)^i([[G_i⁺(F)]](ω) − [[G_i⁻(F)]](ω)) with G_i⁺(F) = (z + e_{α(i)}, α∘succAbove_i), G_i⁻(F) = (z, α∘succAbove_i) for F = (z,α).
3. (Regrouping.) For an m-face index G define γ_G := Σ σ(−1)^iβ_F over all triples (F, i, σ) with σ ∈ {+1,−1} and G_i^σ(F) = G. This is a finite sum of integers: if G = (w,γ′) and G_i^σ(F) = G, then α∘succAbove_i = γ′, so range α = range γ′ ∪ {a} for some a ∉ range γ′ (at most P choices; a determines α and i), and z = w (σ = −) or z = w − e_a (σ = +). So γ_G ∈ ℤ. Since |G_i^σ(F)| ⊆ |F|, every triple with G_i^σ(F) = G and |G| ∩ tsupport ω ≠ ∅ has F ∈ 𝓕_ω, and terms with |G_i^σ(F)| ∩ tsupport ω = ∅ vanish. Rearranging the finite double sum of step 2 gives ∂Pc(ω) = Σ_{G∈𝓖_ω}γ_G[[G]](ω), 𝓖_ω := {G : |G| ∩ tsupport ω ≠ ∅} (finite by (L3)).
4. (The triple.) Let M := ⋃{G° : γ_G ≠ 0} (m-face indices G). For x ∈ G° with γ_G ≠ 0 (G unique by (L1)) put θ(x) := |γ_G| and ξ(x) := sign(γ_G)·simpleNVector(e_{γ′(0)},…,e_{γ′(m−1)}) where G = (w,γ′); put θ := 0, ξ := 0 off M.
5. (Representation.) For ω ∈ D^m(ℝ^P): the integrand θ⟨ω,ξ⟩ vanishes off tsupport ω, M ∩ tsupport ω is contained in the finite disjoint union of the G°, G ∈ 𝓖_ω, γ_G ≠ 0, and on G°, θ⟨ω(x),ξ(x)⟩ = |γ_G|sign(γ_G)ω(x)(e_{γ′}) = γ_G ω(x)(e_{γ′}). By (L2), ∫_{G°} = ∫_{|G|}. Hence ∫_M θ⟨ω,ξ⟩dH^m = Σ_{G∈𝓖_ω}γ_G[[G]](ω) = ∂Pc(ω).
6. (Triple conditions on ℝ^P.) (a) M ⊆ ℝ^P = univ. (b) Each G° is Borel and `LatticeFaceIndex m P` is countable, so M is Borel, hence null-measurable. (c) Each G° ⊆ range A_G with A_G(s) := ρw + Σ_j s_je_{γ′(j)}, an isometry ℝ^m → ℝ^P (Lipschitz); M is contained in the countable union of these ranges, so M is countably m-rectifiable (M₀ := ∅; enumerate the countably many maps, padding with a constant map). (d) θ = |γ_G| ∈ {1,2,…} on M. (e) For compact K, M ∩ K is covered by finitely many G° (L3), on each of which θ is constant and H^m(G°) ≤ H^m(|G|) = ρ^m < ∞; θ is Borel (piecewise constant on countably many Borel pieces); so θ is integrable on M ∩ K. (f) ξ is Borel (piecewise constant on countably many Borel pieces, finite-dimensional target), hence a.e. strongly measurable. (g) Orientation at every x ∈ M: let x ∈ G°, G = (w,γ′), γ_G ≠ 0, τ := (e_{γ′(0)},…,e_{γ′(m−1)}) (orthonormal) and L := span τ (dim m). By (L4) choose δ > 0 with M ∩ B_δ(x) = (x + L) ∩ B_δ(x) ⊆ G° (other relative interiors lie in other closed faces; x + L = ρw + span e_{γ′}), on which θ ≡ |γ_G| = θ(x). Let f ∈ C_c(ℝ^P;ℝ) vanish outside B_R(0). For 0 < r < δ/R: η_{x,r}(M) ∩ B_R(0) = η_{x,r}(M ∩ B_{rR}(x)) = η_{x,r}((x+L) ∩ B_{rR}(x)) = L ∩ B_R(0), and θ(x + ry) = θ(x) for y in this set, so ∫_{η_{x,r}(M)}f(y)θ(x+ry)dH^m(y) = θ(x)∫_L f dH^m. Hence `HasWeightedApproximateTangentSpaceAt m M θ x L`, and ξ(x) = ±simpleNVector τ. (For m = 0: L = {0}, τ empty, G° a lattice point, and the same computation applies.)
7. (Conclusion.) θ is natural-valued on M, so by 5 and 6, ∂Pc = τ(M,θ,ξ) is integer multiplicity. (If `LatticeFaceIndex (m+1) P` is empty, i.e. P < m+1, then Pc = 0, all γ_G = 0, M = ∅, and the argument gives ∂Pc = 0 = τ(∅,0,0).)

## Key steps

1. For each test form only finitely many lattice faces meet its support, so the lattice chain sums are finite.
2. By lattice_face_stokes, ∂Pc(ω) = Σ_F β_F Σ_i (−1)^i([[G_i⁺(F)]](ω) − [[G_i⁻(F)]](ω)); regrouping gives ∂Pc = Σ_G γ_G[[G]] with finitely many integer contributions per m-face.
3. Relative interiors of distinct faces are disjoint, relative boundaries are H^m-null and faces are locally finite.
4. M := ⋃{G° : γ_G ≠ 0}, θ := |γ_G|, ξ := sign(γ_G)e_{γ′} is an integer multiplicity triple; at relative interior points the weighted tangent space is the face plane.

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
