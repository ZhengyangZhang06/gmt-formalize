# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.slice_imreps-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent Steps 0, 4(b) (second and third bullets), 4(d), 5, 6, 7, 8 and 10; Simon Ch. 6, Lemma 4.1, Remark 4.2, 4.3, Definition 4.4 and the proof of Lemma 4.5(1). Notation: Hᵏ = μHE[k], μ_T := RT.measure = θH^{n+1}⌞M, τ(R)(ω) := R.action ω.

0. Preliminaries.
 (a) θ ≥ 1 on M and ∫_{M∩K} θ dH^{n+1} < ∞ for compact K ⊆ U (locallyIntegrable_mult). For Borel W, μ_T(W) = ∫_{M∩W} θ dH^{n+1} (withDensity_apply).
 (b) For H^{n+1}-a.e. x ∈ M, ξ(x) is a unit orientation of T_xM (field `orients` and uniqueness of approximate tangent spaces, HasApproximateTangentSpaceAt.unique). A unit orientation ζ of any subspace satisfies |ζ(α)| ≤ ‖α‖, so ‖ζ‖ ≤ 1.
 (c) Let ξ₀ := RT.aestronglyMeasurable_orient.mk, a strongly measurable map with ξ₀ = ξ H^{n+1}-a.e. on M.
 [Formalization note: MultiVector P k has a Borel σ-algebra, but SecondCountableTopology/FiniteDimensional instances are not synthesized automatically. So build every multivector-valued map below as a strongly measurable map, by composing strongly measurable maps with continuous maps (Continuous.comp_stronglyMeasurable, StronglyMeasurable.prodMk, StronglyMeasurable.piecewise / indicator on measurable sets). Real-, ℝ^P- and [0,∞]-valued strongly measurable maps are measurable (.measurable).]
 [Lean construction hints:
 - Write RT.aestronglyMeasurable_orient.mk RT.orient (mk takes the function explicitly).
 - Norms of MultiVector-valued maps may need explicit types, e.g. StronglyMeasurable.norm (β := MultiVector P (n+1)).
 - Nested continuous-linear-map types over Covector may fail instance synthesis. So build α ↦ v♭∧α as a continuous linear map with LinearMap.mkContinuous, or via ContinuousAlternatingMap.alternatizeUncurryFinCLM. Get the bound from norm_alternatizeUncurryFin_le, and get joint continuity in (v, α) and (ζ, v) from isBoundedBilinearMap_comp, isBoundedBilinearMap_smulRight and isBoundedBilinearMap_apply.]
 (d) Compact exhaustion: K_1 ⊆ K_2 ⊆ … compact with K_i ⊆ int K_{i+1} and ⋃_i K_i = U. Every compact K ⊆ U lies in some K_i.

1. Transfer of null sets to slices. Let Z be Borel with H^{n+1}(M ∩ Z) = 0. By (G3) with φ = 1_Z, ∫_ℝ Hⁿ(M_t ∩ Z) dt = ∫_M |g|1_Z dH^{n+1} = 0. As the integrand is a.e.-measurable, Hⁿ(M_t ∩ Z) = 0 for a.e. t (lintegral_eq_zero_iff').
 Let Z₀ be a Borel set with H^{n+1}(M ∩ Z₀) = 0 containing every x ∈ M at which one of the following fails: ξ(x) = ξ₀(x); ξ(x) is a unit orientation of T_xM; ‖ξ₀(x)‖ ≤ 1; g(x) ∈ T_xM. Such a set exists by (G2), 0(b), 0(c) and exists_measurable_superset_of_null applied to μHE[n+1]⌞M. Only the statement “∀ᵐ t, t ∈ G₁” below is used; G₁ need not be measurable.

2. Good levels (parent Steps 4(b), 4(d)). Let G₁ be the set of t ∈ ℝ with ∫_{M_t∩K_i} θ dHⁿ < ∞ for every i and Hⁿ(M_t ∩ Z₀) = 0.
 - By (G3) with φ = θ1_{K_i} (Borel) and (G1), ∫_ℝ ∫_{M_t∩K_i} θ dHⁿ dt = ∫_{M∩K_i} |g|θ dH^{n+1} ≤ L∫_{M∩K_i} θ < ∞. So for each i, ∫_{M_t∩K_i} θ < ∞ for a.e. t.
 - With step 1 and a countable intersection, a.e. t ∈ ℝ lies in G₁.
 - For t ∈ G₁ and compact K ⊆ U, take K ⊆ K_i. Then ∫_{M_t∩K} θ dHⁿ < ∞, and since θ ≥ 1, Hⁿ(M_t ∩ K) < ∞.

3. Orientation of the slices (parent Step 5; Simon 4.3).
 - For x ∈ M with g(x) ≠ 0 let ν(x) := g(x)/|g(x)| and ξ̃(x) := ξ₀(x) ∘ (α ↦ ν(x)♭∧α). This is a continuous linear functional on n-covectors, the composition of ξ₀(x) with the continuous linear map α ↦ alternatizeUncurryFin((innerSL ℝ ν(x)).smulRight α).
 - Otherwise let ξ̃(x) := 0.
 - ξ̃ is strongly measurable. It is the indicator of the measurable set M ∩ {g ≠ 0} applied to x ↦ Ξ(ξ₀(x), ν(x)), where Ξ(ζ, v) := ζ ∘L (α ↦ v♭∧α) is continuous on MultiVector P (n+1) × ℝ^P, ξ₀ is strongly measurable, and ν = g/|g| is measurable into ℝ^P, hence strongly measurable.
 - Linearity of v ↦ v♭∧α gives |g(x)|·ξ̃(x)(α) = ξ₀(x)(g(x)♭∧α) for x ∈ M with g(x) ≠ 0. If g(x) = 0 then g(x)♭∧α = 0.
 Claim: for t ∈ G₁ and Hⁿ-a.e. x ∈ M_t, M_t has approximate tangent space Q_x := T_xM ∩ g(x)^⊥ at x, and ξ̃(x) is a unit orientation of Q_x.
 - The first part is (G4b), which applies by step 2.
 - For x ∈ M_t ∖ Z₀, which is Hⁿ-a.e. x ∈ M_t since t ∈ G₁: ξ₀(x) = ξ(x) is a unit orientation of T_xM and ν(x) ∈ T_xM is a unit vector. The sibling wedge_orientation (Lean dor_lmbsf_interior_product_orientation, with ζ := ξ₀(x), ζ' := ξ̃(x), Q := T_xM, ν := ν(x)) shows that ξ̃(x) is a unit orientation of T_xM ⊓ (ℝ∙ν(x))ᗮ = Q_x, as ℝ∙ν(x) = ℝ∙g(x).

4. The family (parent Step 6). For t ∈ G₁ let R_t := (M_t, θ, ξ̃). It is an IMRep U n:
 - M_t is Borel (M and g Borel, f continuous), M_t ⊆ M ⊆ U, and M_t is countably n-rectifiable by (G4a);
 - θ is measurable and θ > 0 on M_t ⊆ M;
 - ∫_{M_t∩K} θ dHⁿ < ∞ for compact K ⊆ U (step 2);
 - ξ̃ is strongly measurable (step 3), hence a.e. strongly measurable for Hⁿ⌞M_t;
 - `orients` holds by step 3.
 For t ∉ G₁ let R_t be the empty triple (carrier ∅, mult 1, orient 0). It satisfies all fields vacuously: ∅ is countably n-rectifiable, and integrals and a.e. statements over ∅ are trivial. Define Rs t := R_t; membership in G₁ is decided classically.
 (1) holds: M_t ⊆ f⁻¹(t) and ∅ ⊆ f⁻¹(t).
 For t ∈ G₁ and Borel W: μ_{R_t}(W) = ∫_{M_t∩W} θ dHⁿ and τ(R_t)(ω) = ∫_{M_t} θ ξ̃(ω) dHⁿ. For t ∉ G₁ both are 0.

5. (2) (Simon 4.5(1)). Let W be Borel. By (G3) with φ = θ1_W, t ↦ ∫_{M_t∩W} θ dHⁿ is a.e.-measurable. It agrees with t ↦ μ_{R_t}(W) on the full-measure set G₁, so the latter is a.e.-measurable, and, using (G1),
 ∫_ℝ μ_{R_t}(W) dt = ∫_ℝ ∫_{M_t} θ1_W dHⁿ dt = ∫_M |g|θ1_W dH^{n+1} ≤ L∫_{M∩W} θ dH^{n+1} = Lμ_T(W).

6. (3) (parent Step 8). Fix ω ∈ 𝒟ⁿ(U), K := tsupport ω (compact ⊆ U), c := sup_x ‖ω(x)‖, and q := θ·ξ̃(ω), a Borel function (strongly measurable and real-valued).
 - Bound. For t ∈ G₁, |q| ≤ cθ1_K Hⁿ-a.e. on M_t (step 3 and 0(b)). So q is Hⁿ⌞M_t-integrable and τ(R_t)(ω) = ∫_{M_t} q⁺ dHⁿ − ∫_{M_t} q⁻ dHⁿ, both finite.
 - Measurability. By (G3) applied to the Borel functions q⁺, q⁻ ≥ 0, both terms are a.e.-measurable in t. Hence s ↦ τ(R_s)(ω) is a.e. strongly measurable; it is 0 off G₁.
 - Integrability. By step 5 with W = K, ∫_ℝ |τ(R_s)(ω)| ds ≤ c∫_ℝ μ_{R_s}(K) ds ≤ cLμ_T(K) < ∞.

7. (4') (parent Step 10; Simon 4.2). Fix ω, a < b, K, c as in step 6 and q̃ := θ·ξ̃(ω)·1_{a<f<b}, a Borel function.
 - Bound off the slices. On (M ∖ Z₀) ∩ {g ≠ 0}, |ξ̃(x)(α)| ≤ ‖ξ₀(x)‖·‖ν(x)♭∧α‖ ≤ (n+1)‖α‖, using ‖ξ₀(x)‖ ≤ 1 and ‖v♭∧α‖ ≤ (n+1)|v|‖α‖ from the alternating-sum formula. So |g||q̃| ≤ (n+1)cLθ1_K H^{n+1}-a.e. on M, which is integrable.
 - Bound on the slices. For t ∈ G₁, |q̃| ≤ cθ1_K Hⁿ-a.e. on M_t (step 6).
 - Co-area. Apply (G3) to q̃⁺ and q̃⁻ and subtract the two finite identities:
 ∫_M |g| q̃ dH^{n+1} = ∫_ℝ (∫_{M_t} q̃⁺ dHⁿ − ∫_{M_t} q̃⁻ dHⁿ) dt = ∫_ℝ ∫_{M_t} q̃ dHⁿ dt.
 - Right side. For t ∈ G₁, f ≡ t on M_t, so ∫_{M_t} q̃ dHⁿ = 1_{(a,b)}(t)·τ(R_t)(ω). Hence the right side is ∫_{(a,b)} τ(R_t)(ω) dt = ∫_a^b τ(R_s)(ω) ds: the interval integral is over (a, b] (intervalIntegral.integral_of_le), which differs from (a, b) by a null set (integral_Ioc_eq_integral_Ioo), and the integrand is integrable by (3). The real integrals are obtained from the lintegrals by integral_eq_lintegral_pos_part_sub_lintegral_neg_part / integral_toReal.
 - Left side. For x ∈ M ∖ Z₀ with g(x) ≠ 0: |g(x)|ξ̃(x)(ω(x)) = ξ₀(x)(g(x)♭∧ω(x)) = ξ(x)(g(x)♭∧ω(x)). Where g(x) = 0, both |g|q̃ and θξ(g♭∧ω) vanish. Therefore ∫_M |g|q̃ dH^{n+1} = ∫_{M∩{a<f<b}} θ ξ(g♭∧ω) dH^{n+1}.
 Together these give (4'). ∎

## Key steps

1. Null sets of H^{n+1}⌞M meet a.e. slice in an Hⁿ-null set, by (G3) with φ = 1_Z.
2. Good levels G₁ (full measure): locally θHⁿ-finite slices avoiding the Borel bad set Z₀.
3. ξ̃ = ξ₀(ν♭∧·) with ν = g/|g| is strongly measurable (ξ₀ = RT.aestronglyMeasurable_orient.mk). By (G4b) and wedge_orientation it orients T_xM ∩ g^⊥, the approximate tangent space of M_t, Hⁿ-a.e. for t ∈ G₁.
4. R_t = (M_t, θ, ξ̃) for t ∈ G₁ and the empty triple otherwise; this gives (1).
5. (2) from (G3) with φ = θ1_W and |g| ≤ L.
6. (3): |τ(R_s)(ω)| ≤ sup‖ω‖·μ_{R_s}(tsupport ω); measurability from (G3) applied to q^±.
7. (4'): co-area with the signed integrand θξ̃(ω)1_{a<f<b}, f ≡ t on M_t, and |g|ξ̃(ω) = ξ(g♭∧ω).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `python3 -I transitive import scan of the Contract's Poincare.SimonGMT imports (public import ...)`
- `grep -n '^theorem |^def ' simongmt Chapter03/Rectifiable.lean, Chapter02/{AreaFormula,WeightedArea,AreaCritical,AreaLipschitz,AreaDomain,CoareaProjection,CoareaLinear,WhitneyExtension,WhitneyJet,Lipschitz}.lean, Chapter03/{SubmanifoldCover,DisjointCover,Differential}.lean, Chapter06/{Forms,Currents}.lean`
- `grep -rn 'HasApproximateTangentSpaceAt.unique|exists_contDiff_one_extension_of_whitney|HasWhitneyC1Compatibility|area_image_criticalSet_eq_zero|integral_area_formula_of_injective_derivative|weighted_area_formula_of_injective_derivative|map_withDensity_areaJacobian_eq|integrableOn_image_iff_integrableOn_areaJacobian_smul|exists_isClosed_continuousOn_of_measurable|countablyRectifiable_iUnion' simongmt`
- `grep -rn 'ae_tendsto_measure_inter_div_of_measurableSet|LipschitzWith.integral_lineDeriv_mul_eq|Lp.dense_hasCompactSupport_contDiff|tendsto_tsum_of_dominated_convergence|alternatizeUncurryFin_apply|AlternatingMap.eq_smul_basis_det|det_to_matrix_orthonormalBasis_real|volume_preserving_piFinSuccAbove|PiLp.volume_preserving_ofLp|Measurable.lintegral_prod_right|exists_cthickening_subset_open|tendstoUniformlyOn_of_ae_tendsto|euclideanHausdorffMeasure_eq_volume|norm_alternatizeUncurryFin_le' mathlib`
- `#check probes in contract scope: ContinuousAlternatingMap.alternatizeUncurryFin, innerSL, ContinuousLinearMap.smulRight, (ℝ ∙ v)ᗮ, ‖v‖ₑ, GeometricCurrentOn.boundary, exists_measurable_superset_of_null`
- `dag.json scans: regex 'co-?area|area formula|Rademacher|tangential gradient|C¹ approx|Lusin|Jacobian|implicit function' over node statements; lean_name collision check for dor_lmbsf_* (1022 nodes, none)`
- `git grep dor_lmbsf_ over all local branches (no match)`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the 12 statements; lake env lean /tmp/dor-sf-decomp/v2/All.lean (#print axioms DorSf.parent_from_children)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dor-sf-decomp/v2/All.lean`

Snapshot: project b4d606d, mathlib 25730c7c, simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and the snapshot mathlib matches the package tree.

No existing declaration states a rectifiable co-area formula, a tangential gradient of a Lipschitz function, a slice family or the Lipschitz-cut-off Leibniz limit. Related nodes in other branches are unaccepted, reserved and have different types:
- codim1_rdo_c1_approximation;
- codim1_rdo_c1_piece_approxTangent;
- codim1_lur_rectifiable_area_formula;
- dimred_cs_sos_spine_coarea.
So all 12 children get fresh dor_lmbsf_ names.

Reusable library facts for the child proofs:
- SimonGMT Chapter02: injective area formulas in lintegral, Bochner and measure form (WeightedArea, AreaFormula); critical images null (AreaCritical); Whitney C¹ extension (WhitneyExtension/WhitneyJet); Rademacher and Lipschitz images (Lipschitz).
- SimonGMT Chapter01.Lusin.
- SimonGMT Chapter03: HasApproximateTangentSpaceAt.unique, countablyRectifiable_iUnion.
- Mathlib: Besicovitch density theorem, LipschitzWith.integral_lineDeriv_mul_eq, Lp.dense_hasCompactSupport_contDiff, Tannery's theorem, alternatizeUncurryFin_apply, volume-preserving coordinate splits.
- Some of these need extra imports, which are listed in the child proofs.

Lean checks:
- All 12 child types pass validate_lean_statement and elaborate in the exact comparator scope.
- The Lean assembly of the exact frozen parent type from tangential_gradient, slice_imreps and lipschitz_leibniz compiles with only propext, Classical.choice and Quot.sound.
- Interface checks (chart_pieces → piece lemmas; Besicovitch → density_directions) compile.
- MultiVector lacks SecondCountable/FiniteDimensional instance synthesis, so the child proofs use StronglyMeasurable compositions.
