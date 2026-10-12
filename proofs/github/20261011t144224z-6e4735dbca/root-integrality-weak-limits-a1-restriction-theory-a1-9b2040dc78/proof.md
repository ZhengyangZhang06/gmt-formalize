# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1`
- Child DAG node: `root.integrality_weak_limits-a1.restriction_theory-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (fixed for this proof). ℝ^P := Eucl P with standard orthonormal basis e_1,…,e_P. Hᵏ := μHE[k], the normalized k-dimensional Hausdorff measure (a positive constant multiple of μH[k]; it equals Lebesgue measure on a k-dimensional Euclidean space, and μHE[0] = μH[0] is the counting measure). D_k(U) := GeometricCurrentOn U k; D^k(U) := TestFormOn U k (C^∞ k-forms on ℝ^P with compact tsupport contained in U). I(k,P) := the strictly increasing maps {1,…,k} → {1,…,P}; for I ∈ I(k,P), e_I := (e_{I(1)},…,e_{I(k)}) and dx^I is the constant k-covector with dx^I(e_J) = δ_{IJ} (J ∈ I(k,P)); every k-covector is α = Σ_I α(e_I) dx^I. |α| := covectorEuclideanNorm α = (Σ_I α(e_I)²)^{1/2} (the norm used in the definition of mass), and ‖ω‖ := sup_x |ω(x)| for a form ω. For a k-vector w (an element of NVector = the dual of the k-covectors) put w^I := w(dx^I) and |w|_* := (Σ_I (w^I)²)^{1/2}; then w(α) = Σ_I α(e_I) w^I, so |w(α)| ≤ |α| |w|_* (Cauchy–Schwarz). M_W(X) := X.massOn W, M(X) := X.mass = M_U(X), spt X := X.support, X_j ⇀ X := WeaklyConvergesOn, ∂ := boundary. τ(M,θ,ξ)(ω) := tauAction = ∫_M θ ⟨ω,ξ⟩ dHᵏ with ⟨ω,ξ⟩(x) := ξ(x)(ω(x)); "i.m." := IsIntegerMultiplicity; "X⌞A" denotes a current S with IsRestriction X A S; W ⊂⊂ U := CompactlyContainedOpen W U. B_r(x), B̄_r(x) denote open and closed balls.

Source: (P1) of the parent proof, i.e. Simon Ch. 6, 2.7–2.9 (representation of currents of locally finite mass by the Riesz Representation Theorem, Ch. 1, 4.14; the characterization 2.8 of μ_T; the restriction 2.9), together with the independence of the restriction from the chosen representation that the contract's IsRestriction (2.9) refers to ("the result does not depend on the representation (uniqueness of the vector measure T⃗ μ_T)").

Fact used. (F1) If tsupport ω ⊆ W then |X(ω)| ≤ ‖ω‖ M_W(X): if ‖ω‖ = 0 then ω = 0; otherwise ±ω/‖ω‖ is admissible in the definition of M_W(X).

Part (R0): a measure representation forces locally finite mass.
1. Let (μ,v) be a measure representation of X ∈ D_k(U) (IsMeasureRepresentation: for every ω ∈ D^k(U), x ↦ v(x)(ω(x)) is μ-integrable and X(ω) = ∫ v(x)(ω(x)) dμ), and let W ⊂⊂ U. Choose φ ∈ C_c^∞(U) with 0 ≤ φ ≤ 1 and φ = 1 on the compact set closure(W) ⊆ U. For each I ∈ I(k,P), φ·dx^I ∈ D^k(U), so x ↦ φ(x) v^I(x) is μ-integrable and c_I := ∫_{closure W} |v^I| dμ < ∞.
2. If ω is admissible for M_W (tsupport ω ⊆ W, |ω| ≤ 1), then |v(x)(ω(x))| ≤ |ω(x)| |v(x)|_* ≤ Σ_I |v^I(x)| 1_{closure W}(x), so X(ω) ≤ Σ_I c_I. Hence M_W(X) ≤ Σ_I c_I < ∞.

Part (R1): restrictions are unique.
3. Let S_1, S_2 be restrictions of X to A, via representations (μ_1,v_1), (μ_2,v_2) of X (so A is measurable and S_l(ω) = ∫_A v_l(ω) dμ_l). As in step 1, ∫_K |v_l^I| dμ_l < ∞ for every compact K ⊆ U and every I. Hence ν_l^I(B) := ∫_B v_l^I dμ_l (Borel B ⊆ U) defines signed Borel measures on U of locally finite total variation.
4. For φ ∈ C_c^∞(U): ∫ φ dν_1^I = X(φ dx^I) = ∫ φ dν_2^I. Every φ ∈ C_c(U) is the uniform limit of mollifications φ_ε ∈ C_c^∞(U) supported in a fixed compact subset K of U; by dominated convergence (|v_l^I| is μ_l-integrable on K) the identity extends to all φ ∈ C_c(U).
5. Hence ν_1^I = ν_2^I on Borel subsets of U: the positive locally finite Borel measures λ_1 := (ν_1^I)⁺ + (ν_2^I)⁻ and λ_2 := (ν_2^I)⁺ + (ν_1^I)⁻ on U (Jordan decompositions) have equal integrals against every φ ∈ C_c(U); locally finite Borel measures on the open set U ⊆ ℝ^P (a locally compact, σ-compact metric space) are regular and are determined by these integrals (Riesz uniqueness, Simon Ch. 1, 4.12; Mathlib `Measure.ext_of_integral_eq_on_compactlySupported`). So λ_1 = λ_2.
6. Let ω ∈ D^k(U); write ω = Σ_I ω_I dx^I with ω_I := ω(·)(e_I) ∈ C_c^∞(U), so v_l(x)(ω(x)) = Σ_I ω_I(x) v_l^I(x), and ω vanishes off the compact K := tsupport ω ⊆ U. Then S_l(ω) = Σ_I ∫_{A∩K} ω_I dν_l^I, which by step 5 is the same for l = 1, 2. Thus S_1(ω) = S_2(ω) for all ω, and S_1 = S_2 (GeometricCurrentOn.ext).

Part (R2): mass measure, existence of restrictions, mass identity. Assume M_W(X) < ∞ for all W ⊂⊂ U. Let N := #I(k,P) and identify a k-covector α with its coefficient vector (α(e_I))_I ∈ ℝ^N; this is an isometry between |·| and the Euclidean norm of ℝ^N.
7. (Extension to continuous forms.) Let K_c(U;ℝ^N) be the continuous maps φ : U → ℝ^N with compact support in U. For such φ choose W ⊂⊂ U with spt φ ⊆ W; componentwise mollification gives test forms ω_ε with tsupport ω_ε ⊆ W for small ε, ‖ω_ε − φ‖ → 0 and |ω_ε| ≤ sup|φ| pointwise (mollification is an average and the Euclidean ball is convex). By (F1), |X(ω_ε) − X(ω_δ)| ≤ M_W(X)‖ω_ε − ω_δ‖ → 0, so L(φ) := lim_ε X(ω_ε) exists, does not depend on the approximating sequence, is linear, equals X on test forms, and |L(φ)| ≤ M_W(X) sup|φ| whenever spt φ ⊆ W ⊂⊂ U. Moreover, for every open W′ ⊆ U,
   sup{L(φ) : φ ∈ K_c(U;ℝ^N), spt φ ⊆ W′, |φ| ≤ 1} = M_{W′}(X):
   "≥" since admissible test forms are such φ; "≤" since for spt φ compact ⊆ W′ the mollifications are admissible for M_{W′} when ε is small, and L(φ) = lim X(ω_ε).
8. (Riesz.) L is a locally bounded linear functional on K_c(U;ℝ^N). By the Riesz Representation Theorem (Simon Ch. 1, 4.14; SimonGMT `simon_theorem_4_14`, on the locally compact Hausdorff space U with the finite-dimensional Hilbert space ℝ^N) there are a Radon measure μ_0 on U and a μ_0-measurable ν : U → ℝ^N with |ν| = 1 μ_0-a.e. and L(φ) = ∫ ⟨φ, ν⟩ dμ_0; moreover μ_0 is the total variation measure of L: by (∗) in the proof of 4.14 (the envelope identity sup{L(φ) : |φ| ≤ g} = ∫ g dμ_0 for g ∈ C_c(U), g ≥ 0; SimonGMT `vectorFunctionalEnvelopeMeasure`) and inner regularity of μ_0 on open sets, μ_0(W′) = sup{L(φ) : spt φ ⊆ W′, |φ| ≤ 1} for every open W′ ⊆ U. By step 7, μ_0(W′) = M_{W′}(X) for every open W′ ⊆ U. Define the Borel measure μ on ℝ^P by μ(B) := μ_0(B ∩ U), and replace ν by a Borel function equal to it μ_0-a.e. Then μ(ℝ^P ∖ U) = 0 and μ(W) = M_W(X) for every W ⊂⊂ U, i.e. IsMassMeasure X μ.
9. (Representation.) Let v(x) be the k-vector with coefficients v^I(x) := ν_I(x) for x ∈ U (v := 0 off U), i.e. v(x)(α) := Σ_I α(e_I) ν_I(x). For ω ∈ D^k(U): |v(x)(ω(x))| ≤ |ω(x)| |ν(x)| ≤ ‖ω‖ 1_{tsupport ω}(x) μ-a.e., which is μ-integrable since tsupport ω is a compact subset of U and μ is finite on it; and X(ω) = L(ω) = ∫ v(x)(ω(x)) dμ. So (μ, v) is a measure representation of X, with |v|_* = 1 μ-a.e.
10. (Existence of restrictions.) For a Borel set A ⊆ ℝ^P put S_A(ω) := ∫_A v(x)(ω(x)) dμ. S_A is linear on D^k(U); it is sequentially continuous: if ω_j → 0 in the test-form topology (tsupport ω_j ⊆ K for a fixed compact K ⊆ U and ω_j → 0 uniformly), then |S_A(ω_j)| ≤ ‖ω_j‖ μ(K) → 0. Thus S_A ∈ D_k(U) and IsRestriction X A S_A holds via the representation (μ, v).
11. (Mass identity.) Let S be any restriction of X to a set A (so A is measurable) and W ⊆ U open. By (R1), S = S_A.
   "≤": for admissible ω (tsupport ω ⊆ W, |ω| ≤ 1), S_A(ω) ≤ ∫_{A∩W} |ω||v|_* dμ ≤ μ(W ∩ A).
   "≥": let K ⊆ A ∩ W be compact and ε > 0. By Lusin's theorem (μ_0 Radon, ν measurable) there is a compact K′ ⊆ K with μ(K ∖ K′) < ε such that ν|_{K′} is continuous and |ν| = 1 on K′; by outer regularity there is an open O with K′ ⊆ O, closure(O) compact ⊆ W, μ(O ∖ K′) < ε. Extend ν|_{K′} (Tietze, componentwise), compose with the radial retraction of ℝ^N onto its closed unit ball and multiply by a cutoff in C_c(O) equal to 1 on K′: this gives φ ∈ K_c(U;ℝ^N) with spt φ ⊆ O, |φ| ≤ 1, φ = ν on K′. Then ∫_A ⟨φ,ν⟩ dμ ≥ μ(K′) − μ(O ∖ K′) ≥ μ(K) − 2ε. The mollifications ω_ε of φ are admissible for M_W for small ε and converge to φ uniformly with supports in closure(O), so S_A(ω_ε) → ∫_A ⟨φ,ν⟩ dμ (dominated convergence). Hence M_W(S) ≥ μ(K) − 2ε. By inner regularity of the Radon measure μ_0 on the Borel set A ∩ W ⊆ U (valid also when μ(A ∩ W) = ∞, U being σ-compact), the supremum of μ(K) over compact K ⊆ A ∩ W is μ(W ∩ A). So M_W(S) = μ(W ∩ A).
12. Steps 8, 10, 11 give (R2). Together with (R0) and (R1) this proves the three conjuncts. ∎

## Key steps

1. (R0): testing with φ dx^I (φ = 1 near closure W) bounds M_W(X) by Σ_I ∫_{closure W}|v^I| dμ.
2. (R1): the coefficient signed measures of two representations agree on C_c^∞(U), hence on C_c(U), hence as measures (Riesz uniqueness), so the restrictions agree.
3. (R2): by the mass bound X extends to continuous compactly supported forms; the Riesz Representation Theorem (Ch. 1, 4.14) gives μ and ν with |ν| = 1 and μ(W′) = M_{W′}(X).
4. S_A(ω) := ∫_A⟨ω,v⟩dμ is a current and a restriction of X to A.
5. Mass identity M_W(S) = μ(W ∩ A): '≤' from |v|_* = 1, '≥' by Lusin approximation, mollification and inner regularity.

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
