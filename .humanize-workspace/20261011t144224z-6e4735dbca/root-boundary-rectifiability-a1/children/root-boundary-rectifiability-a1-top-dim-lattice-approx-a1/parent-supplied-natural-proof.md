# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1`
- Child DAG node: `root.boundary_rectifiability-a1.top_dim_lattice_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (P7), second case (P = n, book k = 0), of the parent proof, i.e. the printed steps (27)–(37) of the proof of 5.1 with Q = X (the retraction is the identity because L_n = ℝⁿ): X = θ[[ℝⁿ]] with integer-valued θ, (31) integer medians β_F on the cubes F ∈ 𝓛_n(ρ), (32)/(34) M(X − P) ≤ cρM(∂X), (37) M(∂P) ≤ cM(∂X). The two estimates that the book imports from Ch. 2 (2.7 and 2.9) are proved directly below: the L¹ estimate by a localized translation inequality (an elementary proof of 2.7 for boxes with medians), and (37) by comparing the medians of adjacent cubes, which needs the same inequality on two-cube boxes instead of the trace estimate 2.8/2.9.

Notation. n := m + 1, ℝⁿ = `Eucl n` with basis e₀,…,e_{n−1}; Lⁿ = Hⁿ = `μHE[n]` (`EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). The only strictly increasing map Fin n → Fin n is the identity, so the n-faces of 𝓛_n(ρ) are the closed cubes C_z := ρ(z + [0,1]ⁿ), z ∈ ℤⁿ, with index (z, id), and [[C_z]](ω) = ∫_{C_z}ω̂ dLⁿ where ω̂(x) := ω(x)(e₀,…,e_{n−1}). For an n-covector α on ℝⁿ the Euclidean coefficient norm is |α| = |α(e₀,…,e_{n−1})| (one increasing multi-index). For a form ω, ‖ω‖ := sup_x|ω(x)|.

1. (Density; (27)–(28).) X = τ(M,θ,ξ) with M ⊆ ℝⁿ, θ ∈ {1,2,…} on M, θ integrable on M ∩ K for compact K, and for a.e. x ∈ M, ξ(x) = ±simpleNVector τ with τ = (τ₀,…,τ_{n−1}) orthonormal in ℝⁿ. For such τ and every n-covector α, α(τ₀,…,τ_{n−1}) = det[τ]·α(e₀,…,e_{n−1}) (alternating n-forms on ℝⁿ are multiples of the determinant; Mathlib `AlternatingMap.eq_smul_basis_det`), and det[τ] = ±1 (det[τ]² = det([τ]ᵀ[τ]) = det Id). Let Δ be the n-covector with Δ(v) = det[v]; then ξ(x)(α) = s(x)α(e₀,…,e_{n−1}) with s(x) := ξ(x)(Δ) ∈ {±1} for a.e. x ∈ M. Define u₀(x) := θ(x)s(x) if x ∈ M and s(x) ∈ {±1}, u₀(x) := 0 otherwise. u₀ is integer-valued and a.e. measurable (M is null-measurable, θ is a.e. measurable on each M ∩ K by local integrability, and s is a.e. measurable because ξ is a.e. strongly measurable and evaluation at Δ is continuous linear), and |u₀| ≤ θ1_M is locally integrable. Let ũ be a Borel function with ũ = u₀ a.e. and put u := ũ·1_{ũ⁻¹(ℤ)}: u is Borel, integer-valued everywhere, u = u₀ a.e. (u₀ is integer-valued), and |u| ≤ θ1_M a.e. All integrals below are unchanged by this choice of representative, and
 (E1) X(ω) = ∫ u ω̂ dLⁿ for every ω ∈ Dⁿ(ℝⁿ).
2. (L¹-duality lemma.) For V ⊆ ℝⁿ open and w locally integrable on V: ∫_V|w| = sup{∫wφ : φ smooth, compact support in V, |φ| ≤ 1}. “≥” is clear. “≤”: for compact K ⊆ V choose ε₀ > 0 with K_{2ε₀} := {dist(·,K) ≤ 2ε₀} ⊆ V and let φ_ε := ϱ_ε∗(sign(w)1_K) (ϱ_ε a standard mollifier, ε < ε₀): φ_ε is smooth, supported in K_{ε₀}, |φ_ε| ≤ 1, φ_ε → sign(w)1_K in L¹ and a.e. along a sequence ε_j → 0; by dominated convergence (|wφ_ε| ≤ |w|1_{K_{ε₀}}) ∫wφ_{ε_j} → ∫_K|w|. Let K exhaust V (monotone convergence).
3. (Finite mass.) For φ smooth with compact support, |φ| ≤ 1, the form ω := φΔ satisfies |ω(x)| = |φ(x)| ≤ 1 and X(ω) = ∫uφ ≤ M(X); by step 2, ∫|u| ≤ M(X) < ∞.
4. (Variation.) For open V put |Du|(V) := sup{∫u div g dLⁿ : g ∈ C_c^∞(V;ℝⁿ), |g(x)| ≤ 1 ∀x} ∈ [0,∞]. Claim: |Du|(V) ≤ M_V(∂X); in particular |Du|(ℝⁿ) ≤ M(∂X) < ∞. Given g, let ω_g be the (n−1)-form with ω_g(x)(e∘succAbove_i) = (−1)^i g_i(x) for i = 0,…,n−1 (e.g. ω_g := Σ_i(−1)^i g_i κ_i, κ_i the wedge of the coordinate functionals x_j, j ≠ i, in increasing order, so that κ_i(e∘succAbove_j) = δ_{ij} by `wedgeCovectors_apply_det`). ω_g is smooth with compact support in V, and |ω_g(x)| = |g(x)| ≤ 1 because the strictly increasing (n−1)-tuples are exactly the succAbove_i. By `exteriorDerivative_apply`, dω_g(x)(e₀,…,e_{n−1}) = Σ_i(−1)^i∂_i[(−1)^ig_i](x) = div g(x). So ∂X(ω_g) = X(dω_g) = ∫u div g (E1), and ω_g is mass-admissible for V, whence ∫u div g ≤ M_V(∂X).
5. (Bounded overlap.) If V₁,…,V_N are open and every point lies in at most c of them, then Σ_j|Du|(V_j) ≤ c|Du|(ℝⁿ): for admissible g_j (for V_j), g := c⁻¹Σ_jg_j is admissible for ℝⁿ (at each point at most c of the g_j are nonzero, each of norm ≤ 1), so Σ_j∫u div g_j = c∫u div g ≤ c|Du|(ℝⁿ); take suprema in each g_j. For countable families apply this to every finite subfamily.
6. (Localized translation inequality.) For V open convex and h ∈ ℝⁿ: ∫_{V∩(V−h)}|u(x+h) − u(x)|dx ≤ |h||Du|(V). Proof (h ≠ 0): let φ be smooth with compact support in V ∩ (V − h), |φ| ≤ 1, and G(y) := h∫₀¹φ(y − th)dt. G is smooth, |G| ≤ |h|, and its support lies in ⋃_{t∈[0,1]}(spt φ + th) ⊆ V (for p ∈ spt φ both p and p + h lie in V, hence so does the segment, V convex), a compact set. div G(y) = ∫₀¹Dφ(y−th)h dt = φ(y) − φ(y−h). By translation invariance, ∫(u(x+h) − u(x))φ(x)dx = ∫u(y)(φ(y−h) − φ(y))dy = ∫u div(−G) ≤ |h||Du|(V) (−G/|h| is admissible for V). Take the supremum over φ and use step 2 on V ∩ (V − h).
7. (Boxes.) For an open box B with side lengths ℓ₁,…,ℓ_n, volume |B| and diameter d_B: ∫_B∫_B|u(x) − u(y)|dxdy ≤ 2ⁿ|B|d_B|Du|(B). Proof: substituting y = x + h (Tonelli), the left side is ∫_{B−B}∫_{B∩(B−h)}|u(x+h) − u(x)|dxdh ≤ ∫_{∏(−ℓ_i,ℓ_i)}|h||Du|(B)dh ≤ 2ⁿ|B|d_B|Du|(B) by step 6 (B is convex, |h| ≤ d_B on B − B).
8. (Integer medians; (31).) For a cube C = C_z let β_C := max{j ∈ ℤ : Lⁿ({u ≥ j} ∩ C) ≥ ρⁿ/2} (the set is nonempty and bounded above because u ∈ L¹(C) and Lⁿ({u ≥ j} ∩ C) → ρⁿ as j → −∞, → 0 as j → ∞). Then Lⁿ({u ≥ β_C} ∩ C) ≥ ρⁿ/2 and, u being integer-valued, Lⁿ({u ≤ β_C} ∩ C) = ρⁿ − Lⁿ({u ≥ β_C+1} ∩ C) > ρⁿ/2. Median inequality: for every a ∈ ℝ, |β_C − a|ρⁿ ≤ 2∫_C|u − a| (if β_C ≥ a, |u − a| ≥ β_C − a on {u ≥ β_C} ∩ C; if β_C < a, |u − a| ≥ a − β_C on {u ≤ β_C} ∩ C). With a = 0: β_C ≠ 0 implies ∫_C|u| ≥ ρⁿ/2, so by step 3 only finitely many β_C are nonzero.
9. (Poincaré with medians; (32).) ∫_C|u − β_C| ≤ 3·2ⁿ√n ρ|Du|(C̊): for every y ∈ C̊, ∫_C|u − β_C| ≤ ∫_C|u − u(y)| + ρⁿ|β_C − u(y)| ≤ 3∫_C|u − u(y)| (step 8 with a = u(y)); average over y ∈ C̊ and apply step 7 to B = C̊ (|B| = ρⁿ, d_B = √nρ; ∂C is Lⁿ-null).
10. (Adjacent cubes.) If C′ = C + ρe_i and B := int(C ∪ C′) (an open box with sides 2ρ, ρ,…,ρ, |B| = 2ρⁿ, d_B = √(n+3)ρ), then |β_C − β_{C′}|ρ^{n−1} ≤ 2^{n+1}√(n+3)|Du|(B): for y ∈ B, |β_C − β_{C′}| ≤ |β_C − u(y)| + |u(y) − β_{C′}| ≤ 2ρ^{−n}∫_B|u − u(y)| (step 8 twice; C ∪ C′ ∖ B is null); average over y ∈ B and use step 7.
11. (The chain.) For ρ > 0 let β(z, id) := β_{C_z} (an integer function on `LatticeFaceIndex n n`, finitely supported by step 8) and Pc(ω) := Σ_zβ_{C_z}∫_{C_z}ω̂ (a finite sum). Pc is linear and |Pc(ω)| ≤ (Σ_z|β_{C_z}|ρⁿ)‖ω‖, so Pc is sequentially continuous on Dⁿ(ℝⁿ) (convergence of test forms implies uniform convergence); thus Pc ∈ Dₙ(ℝⁿ) and `IsLatticeChain ρ β Pc` (the tsum has finitely many nonzero terms).
12. (Mass of X − Pc; (34).) For ω ∈ Dⁿ(ℝⁿ): the cubes cover ℝⁿ and overlap in null sets, and uω̂ is integrable, so X(ω) − Pc(ω) = Σ_z∫_{C_z}(u − β_{C_z})ω̂, hence |X(ω) − Pc(ω)| ≤ ‖ω‖Σ_z∫_{C_z}|u − β_{C_z}| ≤ 3·2ⁿ√nρ‖ω‖Σ_z|Du|(C̊_z) ≤ 3·2ⁿ√nρ M(∂X)‖ω‖ (steps 9, 5 with c = 1 — the open cubes are disjoint — and 4).
13. (Boundary mass; (37).) For ω ∈ D^{n−1}(ℝⁿ), by the sibling lattice_face_stokes with P = n, ∂Pc(ω) = Pc(dω) = Σ_zβ_{C_z}Σ_{i}(−1)^i([[(z+e_i, succAbove_i)]](ω) − [[(z, succAbove_i)]](ω)). Every (n−1)-face index has the form (w, succAbove_i) (the strictly increasing maps Fin(n−1) → Fin n are the succAbove_i), and it arises with sign + from z = w − e_i and with sign − from z = w; so ∂Pc(ω) = Σ_{w,i}(−1)^i(β_{C_{w−e_i}} − β_{C_w})[[(w,succAbove_i)]](ω), a finite sum. Each |[[G]](ω)| ≤ H^{n−1}(|G|)·sup_x|ω(x)(e_{succAbove_i})| ≤ ρ^{n−1}‖ω‖ (the value on an increasing basis tuple is bounded by the coefficient norm). By step 10, |∂Pc(ω)| ≤ ‖ω‖2^{n+1}√(n+3)Σ_{w,i}|Du|(B_{w,i}), B_{w,i} := int(C_{w−e_i} ∪ C_w). Each point of ℝⁿ lies in at most 2n of the boxes B_{w,i} (a point interior to a cube C_v lies only in the 2n boxes containing C_v; a point in the relative interior of a common face lies only in the box of its two cubes; other points lie in none), so by steps 5 and 4, M(∂Pc) ≤ C_n M(∂X) with C_n := n2^{n+2}√(n+3).
14. (Conclusion.) Let ρ_k := 1/(k+1) > 0 and let β_k, Pk be the integer coefficients and chain of step 11 for ρ = ρ_k. Then `IsLatticeChain ρ_k β_k Pk`; for every ω ∈ Dⁿ(ℝⁿ), |X(ω) − Pk(ω)| ≤ 3·2ⁿ√nρ_kM(∂X)‖ω‖ → 0, i.e. Pk ⇀ X; and sup_kM(∂Pk) ≤ C_nM(∂X) < ∞.

## Key steps

1. An integer multiplicity n-current in ℝⁿ is X(ω) = ∫u ω(e₀,…,e_{n−1}) with u integer-valued and L¹ (since ξ = ±det-normalized and M(X) < ∞).
2. The variation |Du|(V) (sup of ∫u div g over |g| ≤ 1) is bounded by M_V(∂X), via the forms ω_g with dω_g = div g.
3. Localized translation inequality ∫_{V∩(V−h)}|u(·+h) − u| ≤ |h||Du|(V) on convex V, hence ∫_B∫_B|u(x)−u(y)| ≤ 2ⁿ|B|d_B|Du|(B) on boxes.
4. Integer medians β_C on the cubes of 𝓛_n(ρ): ∫_C|u − β_C| ≤ cρ|Du|(C̊) and |β_C − β_{C′}|ρ^{n−1} ≤ c|Du|(int(C∪C′)) for adjacent cubes.
5. P = Σβ_C[[C]]: M(X − P) ≤ cρM(∂X) and, by lattice_face_stokes and bounded overlap, M(∂P) ≤ cM(∂X); take ρ_k = 1/(k+1).

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
