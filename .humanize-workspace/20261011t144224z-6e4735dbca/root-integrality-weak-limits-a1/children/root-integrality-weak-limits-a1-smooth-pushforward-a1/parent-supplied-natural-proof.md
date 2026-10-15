# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1`
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (fixed for this proof). ℝ^P := Eucl P with standard orthonormal basis e_1,…,e_P. Hᵏ := μHE[k], the normalized k-dimensional Hausdorff measure (a positive constant multiple of μH[k]; it equals Lebesgue measure on a k-dimensional Euclidean space, and μHE[0] = μH[0] is the counting measure). D_k(U) := GeometricCurrentOn U k; D^k(U) := TestFormOn U k (C^∞ k-forms on ℝ^P with compact tsupport contained in U). I(k,P) := the strictly increasing maps {1,…,k} → {1,…,P}; for I ∈ I(k,P), e_I := (e_{I(1)},…,e_{I(k)}) and dx^I is the constant k-covector with dx^I(e_J) = δ_{IJ} (J ∈ I(k,P)); every k-covector is α = Σ_I α(e_I) dx^I. |α| := covectorEuclideanNorm α = (Σ_I α(e_I)²)^{1/2} (the norm used in the definition of mass), and ‖ω‖ := sup_x |ω(x)| for a form ω. For a k-vector w (an element of NVector = the dual of the k-covectors) put w^I := w(dx^I) and |w|_* := (Σ_I (w^I)²)^{1/2}; then w(α) = Σ_I α(e_I) w^I, so |w(α)| ≤ |α| |w|_* (Cauchy–Schwarz). M_W(X) := X.massOn W, M(X) := X.mass = M_U(X), spt X := X.support, X_j ⇀ X := WeaklyConvergesOn, ∂ := boundary. τ(M,θ,ξ)(ω) := tauAction = ∫_M θ ⟨ω,ξ⟩ dHᵏ with ⟨ω,ξ⟩(x) := ξ(x)(ω(x)); "i.m." := IsIntegerMultiplicity; "X⌞A" denotes a current S with IsRestriction X A S; W ⊂⊂ U := CompactlyContainedOpen W U. B_r(x), B̄_r(x) denote open and closed balls.

Source: (P3) of the parent proof (Simon Ch. 6, 2.23–2.24 for smooth maps, and 3.9 via the sibling `LipschitzPushforwardIntegerMultiplicity`), including its detailed identification of the Lipschitz push-forward with the classical smooth push-forward f_#X(ω) = X(ζ f^#ω); copied and filled in. Degree n := k + 1 ≥ 1.

Notation and facts.
- For a linear L : ℝ^P → ℝ^Q and a j-covector α on ℝ^Q, L^#α := α∘(L,…,L) (`ContinuousAlternatingMap.compContinuousLinearMap α L`); (f^#ω)(x) := Df(x)^# ω(f(x)) with Df(x) := fderiv ℝ f x.
(F1) |Y(ω)| ≤ ‖ω‖ M_W(Y) if tsupport ω ⊆ W.
(F2) (Support.) If η, η′ ∈ D^j(U) agree on an open set N ⊇ spt Y (Y ∈ D_j(U)), then Y(η) = Y(η′): K := tsupport(η − η′) ⊆ ℝ^P ∖ N is a compact subset of U ∖ spt Y, which is the union of the open sets W (closure W compact ⊆ U) on which Y vanishes; finitely many such W_1,…,W_l cover K, and with a smooth partition of unity χ_i ∈ C_c^∞(W_i), Σχ_i = 1 near K, Y(η − η′) = Σ_i Y(χ_i(η − η′)) = 0.
(F3) (Pull-back norm.) |L^#α| ≤ ‖L‖^j |α| for j-covectors α. [In the Euclidean structures on j-covectors for which {dx^I} are orthonormal, L^# is the j-th exterior power of the adjoint of L; by the singular value decomposition L = Σ_i σ_i u_i⊗v_i (orthonormal u, v), Λ^j is diagonal in the bases {v_I}, {u_I} with entries ∏_{i∈I}σ_i ≤ ‖L‖^j.]
(F4) (Naturality.) For C^∞ f and a smooth j-form ω on ℝ^Q, d(f^#ω) = f^#(dω) (chain rule and symmetry of second derivatives; standard).
(F5) (Compatible test forms exist.) For ω ∈ D^j(V), K_ω := spt X ∩ f⁻¹(tsupport ω) is compact (properness hypothesis); take ζ ∈ C_c^∞(U), 0 ≤ ζ ≤ 1, ζ = 1 on an open O ⊇ K_ω; then η := ζ·f^#ω ∈ D^j(U) and η = f^#ω on the open set N := O ∪ f⁻¹(ℝ^Q ∖ tsupport ω) ⊇ spt X, with tsupport η ⊆ tsupport ζ ∩ f⁻¹(tsupport ω).

Proof.
1. (The sibling push-forward.) f is C^∞, hence locally Lipschitz on U; f maps U into V; X is i.m.; and f⁻¹(K) ∩ spt X is compact for compact K ⊆ V. By the hypothesis `LipschitzPushforwardIntegerMultiplicity` there is an i.m. S ∈ D_n(V) with IsLipschitzPushforward X f S: there are a rectifiable triple (M,θ,ξ) in U (θ > 0 real and integrable on compact subsets of U — not necessarily integer valued or ≥ 1) with X = τ(M,θ,ξ), and linear maps L(x) such that for Hⁿ-a.e. x ∈ M, every weighted tangent space T of (M,θ) at x and every v ∈ T, the derivative of t ↦ f(x + tv) at 0 is L(x)v; and S(ω) = ∫_M θ ⟨ω(f(x)), L(x)_#ξ(x)⟩ dHⁿ for ω ∈ D^n(V) (L(x)_# = nVectorPushforward n (L x)).
2. (L(x) = Df(x) on the tangent plane.) For Hⁿ-a.e. x ∈ M the orients property gives an orthonormal τ spanning a weighted tangent space T_x with ξ(x) = ±simpleNVector τ. For v = τ_i ∈ T_x, t ↦ f(x + tv) has derivative Df(x)τ_i at 0 (f is differentiable), so L(x)τ_i = Df(x)τ_i by uniqueness of derivatives. Hence (`nVectorPushforward_simple`) L(x)_#ξ(x) = ±simpleNVector(L(x)∘τ) = ±simpleNVector(Df(x)∘τ) = Df(x)_#ξ(x), and by duality (nVectorPushforward is precomposition with the covector pull-back, (1.9)) ⟨ω(f(x)), Df(x)_#ξ(x)⟩ = ⟨(f^#ω)(x), ξ(x)⟩. Therefore
   S(ω) = ∫_M θ ⟨(f^#ω)(x), ξ(x)⟩ dHⁿ(x) for all ω ∈ D^n(V).
3. (Hⁿ(M ∖ spt X) = 0.) Let O′ := U ∖ spt X (open). By (F2) (with η′ = 0), X vanishes on every test form supported in O′. The coefficient measures θξ^I Hⁿ⌞M (locally finite total variation on U: |ξ^I| ≤ |ξ|_* = 1 a.e. since ξ = ±simpleNVector τ with τ orthonormal (Cauchy–Binet), and θ is integrable on compacts) thus annihilate every φ ∈ C_c^∞(O′) (test X with φ dx^I), hence every φ ∈ C_c(O′) (uniform approximation with supports in a fixed compact subset of O′, dominated convergence), hence they vanish on Borel subsets of O′ (Riesz uniqueness for locally finite signed measures on O′, via Jordan decompositions). So θξ = 0 Hⁿ-a.e. on M ∩ O′; since θ > 0 on M and |ξ|_* = 1 a.e. on M, Hⁿ(M ∩ O′) = 0.
4. (Formula for S.) Let ω ∈ D^n(V) and η ∈ D^n(U) with η = f^#ω on an open N ⊇ spt X. By step 2, S(ω) = ∫_M θ⟨f^#ω, ξ⟩ dHⁿ, and X(η) = ∫_M θ⟨η, ξ⟩ dHⁿ. The integrands coincide on M ∩ N ⊇ M ∩ spt X, and M ∖ spt X is Hⁿ-null (step 3). [Both are integrable: on M ∩ spt X the first integrand vanishes off the compact set K_ω of (F5) and is bounded there by (sup_{K_ω}‖Df‖)^n ‖ω‖ θ.] Hence S(ω) = X(η).
5. (Formula for ∂S.) Let ω ∈ D^k(V) and η ∈ D^k(U) with η = f^#ω on an open N ⊇ spt X. Since d is local, dη = d(f^#ω) = f^#(dω) on N (F4). By (F5) choose η′ ∈ D^n(U) with η′ = f^#(dω) on an open N′ ⊇ spt X. Then ∂S(ω) = S(dω) = X(η′) by step 4, and X(η′) = X(dη) by (F2) (η′ and dη agree on N ∩ N′ ⊇ spt X). Hence ∂S(ω) = X(dη) = ∂X(η).
6. (Mass bounds.) Let c ≥ 0 with ‖Df(x)‖ ≤ c for all x, and W ⊆ ℝ^Q. Let ω ∈ D^n(V) be admissible for M_W(S) (tsupport ω ⊆ W, |ω| ≤ 1) and let η := ζ f^#ω be as in (F5). Then tsupport η ⊆ U ∩ f⁻¹(W) and |η(x)| ≤ |Df(x)^#ω(f(x))| ≤ cⁿ by (F3). By step 4 and (F1), S(ω) = X(η) ≤ cⁿ M_{f⁻¹(W)∩U}(X) (if c = 0 then η = 0 since n ≥ 1, and S(ω) = 0). Taking the supremum over ω: M_W(S) ≤ ofReal(c^{k+1}) · M_{f⁻¹(W)∩U}(X) (the case c = 0 gives M_W(S) = 0, so the ENNReal convention 0·∞ = 0 is harmless). Likewise, for admissible ω ∈ D^k(V) and η := ζ f^#ω, step 5 gives ∂S(ω) = ∂X(η) with |η| ≤ c^k and tsupport η ⊆ U ∩ f⁻¹(W), so M_W(∂S) ≤ ofReal(c^k) · M_{f⁻¹(W)∩U}(∂X) (for k ≥ 1 and c = 0, η = 0 and ∂S(ω) = 0; for k = 0, c^0 = 1 and |η| = |ζ ω∘f| ≤ 1).
7. Steps 1, 4, 5, 6 give all assertions, with S integer multiplicity by step 1. ∎

## Key steps

1. The sibling Lipschitz push-forward gives an integer multiplicity S defined by the 3.6 formula over a rectifiable representation of X.
2. For smooth f the linear maps L(x) equal Df(x) on the weighted tangent planes a.e., so S(ω) = ∫θ⟨f^#ω, ξ⟩dHⁿ.
3. Hⁿ(M ∖ spt X) = 0 because the vector measure θξHⁿ⌞M vanishes off spt X.
4. Hence S(ω) = X(η) for every η agreeing with f^#ω near spt X; ∂S = f_#∂X by naturality of d.
5. Mass bounds from |L^#α| ≤ ‖L‖^j|α| for the Euclidean coefficient norm.

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
