# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1`
- Child DAG node: `root.integrality_weak_limits-a1.patching-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (fixed for this proof). ℝ^P := Eucl P with standard orthonormal basis e_1,…,e_P. Hᵏ := μHE[k], the normalized k-dimensional Hausdorff measure (a positive constant multiple of μH[k]; it equals Lebesgue measure on a k-dimensional Euclidean space, and μHE[0] = μH[0] is the counting measure). D_k(U) := GeometricCurrentOn U k; D^k(U) := TestFormOn U k (C^∞ k-forms on ℝ^P with compact tsupport contained in U). I(k,P) := the strictly increasing maps {1,…,k} → {1,…,P}; for I ∈ I(k,P), e_I := (e_{I(1)},…,e_{I(k)}) and dx^I is the constant k-covector with dx^I(e_J) = δ_{IJ} (J ∈ I(k,P)); every k-covector is α = Σ_I α(e_I) dx^I. |α| := covectorEuclideanNorm α = (Σ_I α(e_I)²)^{1/2} (the norm used in the definition of mass), and ‖ω‖ := sup_x |ω(x)| for a form ω. For a k-vector w (an element of NVector = the dual of the k-covectors) put w^I := w(dx^I) and |w|_* := (Σ_I (w^I)²)^{1/2}; then w(α) = Σ_I α(e_I) w^I, so |w(α)| ≤ |α| |w|_* (Cauchy–Schwarz). M_W(X) := X.massOn W, M(X) := X.mass = M_U(X), spt X := X.support, X_j ⇀ X := WeaklyConvergesOn, ∂ := boundary. τ(M,θ,ξ)(ω) := tauAction = ∫_M θ ⟨ω,ξ⟩ dHᵏ with ⟨ω,ξ⟩(x) := ξ(x)(ω(x)); "i.m." := IsIntegerMultiplicity; "X⌞A" denotes a current S with IsRestriction X A S; W ⊂⊂ U := CompactlyContainedOpen W U. B_r(x), B̄_r(x) denote open and closed balls.

Source: the patching lemma of the parent proof, (P4), used to globalize Step 4 (Simon Remark 8.3(1)); copied and filled in.

Facts used (with proofs).
(a) For a rectifiable triple (M,θ,ξ) (IsRectifiableTriple U k M θ ξ): |ξ(x)|_* = 1 for Hᵏ-a.e. x ∈ M. Indeed, a.e. ξ(x) = ±simpleNVector τ with τ orthonormal, whose coefficients are (simpleNVector τ)^I = dx^I(τ_1,…,τ_k) = det(τ_I) (the k×k minor of the P×k matrix of τ with rows I), and Σ_I det(τ_I)² = det(τᵀτ) = 1 by the Cauchy–Binet formula.
(b) For such a triple, the coefficient measures ν^I := θ ξ^I Hᵏ⌞M (I ∈ I(k,P)) are signed Borel measures on U of locally finite total variation (θ is integrable on M ∩ K for compact K ⊆ U and |ξ^I| ≤ |ξ|_* = 1 a.e. on M), and for every test form ω = Σ_I ω_I dx^I (ω_I := ω(·)(e_I) ∈ C_c^∞(U)) we have τ(M,θ,ξ)(ω) = Σ_I ∫ ω_I dν^I.
(c) (Uniqueness of vector measures.) Let O ⊆ U be open and ν, ν′ be ℝ^{I(k,P)}-valued Borel measures on O whose coefficients have locally finite total variation. If Σ_I ∫ω_I dν^I = Σ_I ∫ω_I dν′^I for all smooth k-forms ω with compact tsupport in O, then ν = ν′ on Borel subsets of O. Proof: testing with ω = φ dx^I (φ ∈ C_c^∞(O)) gives ∫φ dν^I = ∫φ dν′^I; every φ ∈ C_c(O) is a uniform limit of mollifications φ_ε ∈ C_c^∞(O) with supports in a fixed compact subset of O, so by dominated convergence the identity holds for φ ∈ C_c(O); then the positive locally finite Borel measures (ν^I)⁺ + (ν′^I)⁻ and (ν′^I)⁺ + (ν^I)⁻ on O have the same integrals against C_c(O), hence coincide (Riesz uniqueness for locally finite Borel measures on the locally compact σ-compact metric space O; Simon Ch. 1, 4.12/4.14; Mathlib `Measure.ext_of_integral_eq_on_compactlySupported`), i.e. ν^I = ν′^I.
(d) (Total variation.) If ν = gξλ with λ a positive measure, g ≥ 0 locally λ-integrable and |ξ|_* = 1 λ-a.e., then the total variation measure of ν with respect to |·|_* is gλ (|ν|(B) = ∫_B g|ξ|_* dλ).

Proof.
1. (Countable cover.) U is second countable, so countably many of the sets V_x cover U (Lindelöf): U = ⋃_{i≥1} V_i with V_i := V_{x_i}; let Y_i := Y_{x_i} and write Y_i = τ(M_i,θ_i,ξ_i) with IsRectifiableTriple U k M_i θ_i ξ_i and θ_i ∈ {1,2,…} on M_i (definition of i.m.).
2. (Compatibility.) Fix i, i′ and O := V_i ∩ V_{i′}. For every test form ω with tsupport ω ⊆ O we have Y_i(ω) = X(ω) = Y_{i′}(ω). By (b), (c) the vector measures θ_iξ_iHᵏ⌞M_i and θ_{i′}ξ_{i′}Hᵏ⌞M_{i′} coincide on Borel subsets of O, and by (a), (d) so do their total variations: θ_iHᵏ⌞M_i = θ_{i′}Hᵏ⌞M_{i′} on O. Let λ := Hᵏ⌞((M_i ∪ M_{i′}) ∩ O). λ is σ-finite: as θ_i ≥ 1 on M_i, Hᵏ(M_i ∩ K) ≤ ∫_{M_i∩K} θ_i dHᵏ < ∞ for compact K ⊆ U, similarly for M_{i′}, and O is a countable union of compact sets. The functions 1_{M_i}θ_i and 1_{M_{i′}}θ_{i′} are densities with respect to λ of the same measure, so they agree λ-a.e. (Radon–Nikodym uniqueness for σ-finite λ; Mathlib `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`). Since θ_i > 0 on M_i and θ_{i′} > 0 on M_{i′}: Hᵏ((M_i Δ M_{i′}) ∩ O) = 0 and θ_i = θ_{i′} Hᵏ-a.e. on M_i ∩ M_{i′} ∩ O. In the same way the coefficient densities 1_{M_i}θ_iξ_i^I and 1_{M_{i′}}θ_{i′}ξ_{i′}^I agree λ-a.e., hence ξ_i = ξ_{i′} Hᵏ-a.e. on M_i ∩ M_{i′} ∩ O.
3. (Construction.) Let D_i := V_i ∖ ⋃_{j<i} V_j: pairwise disjoint Borel sets with ⋃_i D_i = U and D_i ⊆ V_i. Put M := ⋃_i (M_i ∩ D_i), and for x ∈ D_i set θ(x) := θ_i(x), ξ(x) := ξ_i(x); outside U put θ := 1, ξ := 0. Then for x ∈ M ∩ D_i we have x ∈ M_i and θ(x) = θ_i(x) ∈ {1,2,…}.
4. (Local agreement.) For each i: Hᵏ((M Δ M_i) ∩ V_i) = 0, and 1_Mθ = 1_{M_i}θ_i, 1_Mθξ = 1_{M_i}θ_iξ_i Hᵏ-a.e. on V_i. Indeed V_i = ⋃_j (V_i ∩ D_j), on V_i ∩ D_j the triple (M,θ,ξ) equals (M_j,θ_j,ξ_j), and by step 2 (with O = V_i ∩ V_j ⊇ V_i ∩ D_j) the latter agrees Hᵏ-a.e. with (M_i,θ_i,ξ_i) there.
5. (Representation.) Let ω ∈ D^k(U). Its tsupport is a compact subset of U, covered by finitely many V_i, say V_1,…,V_l after relabeling; choose a smooth partition of unity χ_1,…,χ_l with χ_i ∈ C_c^∞(V_i) and Σ_iχ_i = 1 on a neighbourhood of tsupport ω. Then ω = Σ_i χ_iω, tsupport(χ_iω) ⊆ V_i, so
   X(ω) = Σ_i X(χ_iω) = Σ_i Y_i(χ_iω) = Σ_i ∫_{M_i} θ_i χ_i ⟨ω,ξ_i⟩ dHᵏ = Σ_i ∫_M θ χ_i ⟨ω,ξ⟩ dHᵏ = ∫_M θ ⟨ω,ξ⟩ dHᵏ,
   using step 4 on V_i ⊇ spt χ_i in the fourth equality (all integrands are integrable by step 6 below). Hence X(ω) = τ(M,θ,ξ)(ω) for every ω ∈ D^k(U).
6. (IsRectifiableTriple U k M θ ξ.)
   - M ⊆ ⋃_i D_i = U.
   - M is Hᵏ-null-measurable: a countable union of the null-measurable sets M_i intersected with Borel sets D_i.
   - M is countably k-rectifiable: M ⊆ ⋃_i M_i and each M_i ⊆ M_{i,0} ∪ ⋃_j F_{i,j}(ℝᵏ) with Hᵏ(M_{i,0}) = 0 and F_{i,j} Lipschitz; take M_0 := ⋃_i M_{i,0} (null) and the countable family (F_{i,j}).
   - θ > 0 and θ ∈ {1,2,…} on M (step 3).
   - Local integrability: for compact K ⊆ U, K ⊆ V_1 ∪ ⋯ ∪ V_l for some l, hence K ∩ D_j = ∅ for j > l and ∫_{M∩K} θ dHᵏ = Σ_{j≤l} ∫_{M_j∩D_j∩K} θ_j dHᵏ ≤ Σ_{j≤l} ∫_{M_j∩K} θ_j dHᵏ < ∞ (θ is a.e.-strongly measurable on each of the finitely many measurable pieces).
   - ξ is AE-strongly measurable for Hᵏ⌞M: on each measurable piece M_i ∩ D_i it equals ξ_i, which is AE-strongly measurable for Hᵏ⌞M_i; countable gluing.
   - orients: fix i. For Hᵏ-a.e. x ∈ M ∩ D_i (⊆ M_i), the orients property of (M_i,θ_i,ξ_i) gives an orthonormal τ with HasWeightedApproximateTangentSpaceAt k M_i θ_i x (span τ) and ξ_i(x) = ±simpleNVector τ. Apply `iwl_weighted_tangent_locality` to (M_i,θ_i) and (M,θ) at x: both M_i and M are Hᵏ-null-measurable (triple property of M_i; second item above for M); θ_i(x) = θ(x) (step 3); choose ρ > 0 with B̄_ρ(x) ⊆ V_i (V_i open, x ∈ D_i ⊆ V_i), then θ_i is integrable on M_i ∩ B̄_ρ(x) and θ on M ∩ B̄_ρ(x) (compact subsets of U); for every R > 0 and 0 < r < ρ/R we have B̄_{Rr}(x) ⊆ V_i, where 1_{M_i}θ_i = 1_Mθ Hᵏ-a.e. (step 4), so r^{−k}∫_{B̄_{Rr}(x)} |1_{M_i}θ_i − 1_Mθ| dHᵏ = 0 for all small r. Hence HasWeightedApproximateTangentSpaceAt k M θ x (span τ), and ξ(x) = ξ_i(x) = ±simpleNVector τ. The exceptional sets for the countably many i are null, so orients holds Hᵏ-a.e. on M.
7. By steps 5 and 6, X = τ(M,θ,ξ) with a rectifiable triple and θ natural-valued on M: X is integer multiplicity. ∎

## Key steps

1. By Lindelöf, countably many V_i cover U; write Y_i = τ(M_i,θ_i,ξ_i).
2. On V_i ∩ V_{i′} the vector measures θ_iξ_iHᵏ⌞M_i coincide (Riesz uniqueness); total variations and Radon–Nikodym uniqueness give a.e. agreement of carriers, multiplicities and orientations.
3. Glue the triples along the disjoint Borel pieces D_i := V_i ∖ ⋃_{j<i}V_j.
4. A partition of unity subordinate to the V_i shows X = τ(M,θ,ξ).
5. Check IsRectifiableTriple; the orients property transfers by iwl_weighted_tangent_locality because the triples agree a.e. near each point.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean (identical); Submission.lean byte-identical to Contract.lean`
- `python3: contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all 12 statements`
- `python3 listing of dag.json lean_name fields (45 nodes, no iwl_* names)`
- `rg -n 'theorem exists_disjoint_closedBall_covering_ae' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem ae_tendsto_average|theorem ae_tendsto_lintegral_div' mathlib/Mathlib/MeasureTheory/Covering/{Differentiation,DensityTheorem}.lean`
- `rg -n 'theorem hausdorffMeasure_smul|hausdorffMeasure_smul_right_image' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'ext_of_integral_eq_on_compactlySupported' mathlib/Mathlib`
- `rg -n 'theorem map_linearDependent' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `rg -n 'countable_not_continuousAt|MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem lintegral_liminf_le' mathlib/Mathlib`
- `sed -n 1,140p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, euclideanHausdorffMeasure_zero)`
- `rg -il 'BoundedVariation|Rellich|Helly' mathlib/Mathlib (only 1-D bounded variation and convex Helly; no BV compactness or Helly selection)`
- `rg -n 'theorem simon_theorem_4_14|vectorFunctionalEnvelopeMeasure|theorem simon_theorem_3_3|hasSymmetricVitaliProperty_euclidean|def IsLocallyBV|isLocallyBV_of_locallyL1_of_uniform_bound' simongmt/Poincare/SimonGMT/Chapter0{1,2}`
- `rg -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|HasWeightedApproximateTangentSpaceAt.unique|def CountablyRectifiable|countablyRectifiable_of_measure_zero|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'nVectorPushforward_simple|def simpleNVector|def covectorEuclideanNorm|massOn_le_liminf|boundary_boundary|WeaklyConvergesOn.boundary|def GeometricCurrentOn.support|restrictDomain' simongmt/Poincare/SimonGMT/Chapter06`
- `grep -n '3.3|3.6|3.11|4.14|4.16' book/chapter-01.txt; grep -n '2.6 Theorem' book/chapter-02.txt; sed -n 2290,2480p book/chapter-06.txt (printed 8.2 proof)`
- `lake build GMT.Ch06.Submission (scratch /tmp/iwl-decomp-scratch, pinned packages)`
- `lake env lean Scratch/Stmts.lean (12 child statements; only intended sorries)`
- `lake env lean Scratch/Final.lean (12 exact Submission.<name> checks + parent assembly IwlAssemblyCheck.parent + #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/iwl-decomp-scratch/Scratch/Stmts.lean`
- `/tmp/iwl-decomp-scratch/Scratch/Final.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 Contract and a byte-identical Submission with no Submission.* declarations.

Scratch Lean checks of the frozen project:
- All 12 child statements elaborate in the comparator's child scope.
- `exact Submission.<name>` resolves for each child.
- IntegralityOfWeakLimits follows from the 12 children plus SlicingTheorem, IsoperimetricTheorem, LipschitzPushforwardIntegerMultiplicity and RectifiabilityTheorem. The helper lemmas use only propext, Classical.choice and Quot.sound.
- The smoothness exponent ((⊤ : ℕ∞) : WithTop ℕ∞) was checked to mean C^∞, not analytic.

Mathlib supplies the tools the child proofs cite:
- the Besicovitch disjoint covering (`Besicovitch.exists_disjoint_closedBall_covering_ae`);
- Lebesgue–Besicovitch differentiation (`VitaliFamily.ae_tendsto_average`);
- Hausdorff scaling (`hausdorffMeasure_smul`);
- Riesz uniqueness (`Measure.ext_of_integral_eq_on_compactlySupported`);
- monotone-derivative integral bounds (`MonotoneOn.intervalIntegral_deriv_mem_uIcc`);
- Fatou (`lintegral_liminf_le`);
- `AlternatingMap.map_linearDependent`;
- μHE[0] = μH[0] (counting measure).

SimonGMT supplies the vector Riesz theorem (`simon_theorem_4_14`, `vectorFunctionalEnvelopeMeasure`), the density comparison (`simon_theorem_3_3`), `HasWeightedApproximateTangentSpaceAt.unique`, `nVectorPushforward_simple`, `WeaklyConvergesOn.massOn_le_liminf`, `GeometricCurrentOn.boundary_boundary` and `restrictDomain`.

No match was found for BV compactness, Helly's selection theorem or the product formula for Hausdorff measure. These are cited from Simon Ch. 2, 2.6, the parent's (P6), and Simon 3.2(2) / Federer 3.2.23.

The DAG (45 nodes) reserves no iwl_* name. These checks do not certify the analytic proofs.
