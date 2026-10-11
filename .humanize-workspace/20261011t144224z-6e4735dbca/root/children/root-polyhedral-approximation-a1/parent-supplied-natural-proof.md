# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.polyhedral_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, 6.2 (Weak Polyhedral Approximation Theorem) and its printed proof (pp. 169–170). Book n = m + 1, ambient ℝ^{n+ℓ}, ℓ ≥ 1. The printed proof: first the case U = ℝ^{n+ℓ}, M(T), M(∂T) < ∞ via the scaled deformation theorem with ρ = ρ_k ↓ 0; then the general case via T_λ = T ⌞ {φ > λ} for an exhaustion function φ and a.e. λ (4.5), and a diagonal choice λ_j ↓ 0. It is copied below with the details filled in. Errata applied: “F ∈ F_n(ρ_k)”, “β_R^{(k)}” mean F ∈ 𝓛_n(ρ_k), β_F^{(k)} (README); “Pk(ω) → Tk(ω)” means P_k(ω) → T(ω); “{x D φ(x) > λ}” means {x : φ(x) > λ}; we use T⌞{φ ≥ λ} instead of T⌞{φ > λ}, which avoids discarding the countably many λ with μ_T({φ = λ}) > 0 (the two coincide for all other λ).

Sibling results used: `DeformationTheorem` (5.3) and `SlicingTheorem` (§4).

Setting. n := m + 1, d := n + ℓ, U ⊆ ℝ^d open, T ∈ D_n(U) integer multiplicity with M_W(T), M_W(∂T) < ∞ for all W ⊂⊂ U.

Preliminaries. (P1) Representation and restriction (Simon 2.7–2.9): T and ∂T have locally finite mass, so T(ω) = ∫⟨ω,T⃗⟩dμ_T, ∂T(ω) = ∫⟨ω,∂T⃗⟩dμ_{∂T} with Radon μ_T, μ_{∂T} on U, unit vector fields, μ(W) = M_W for open W ⊆ U; X⌞A(ω) := ∫_A⟨ω,X⃗⟩dμ_X is the unique restriction (`IsRestriction`), M_W(X⌞A) = μ_X(W∩A), and |X(ω)| ≤ M_W(X)‖ω‖ for tsupport ω ⊆ W. (P2) Restriction of an integer multiplicity current τ(M,θ,ξ) to a Borel set A is τ(M∩A,θ,ξ), integer multiplicity (at Hⁿ-a.e. x ∈ M∩A the measure θHⁿ⌞(M∖A) has zero density — apply Ch. 1, 3.6 to the finite measures θHⁿ⌞((M∖A) ∩ B) for balls B ⊂⊂ U — so the weighted tangent spaces agree). (P3) Extension: if X ∈ D_k(U) has compact support K ⊆ U, put X̃(ω) := X(χω) for ω ∈ D^k(ℝ^d), with χ ∈ C_c^∞(U), 0 ≤ χ ≤ 1, χ = 1 near K (independent of χ since X kills forms vanishing near spt X); X̃ ∈ D_k(ℝ^d), ∂X̃ = (∂X)~, M(X̃) = M(X) (= M_W(X) for any open W ⊇ K, W ⊆ U), M(∂X̃) = M(∂X), X̃(ω) = X(ω) for ω ∈ D^k(U), and X̃ is integer multiplicity if X is (same triple, Hⁿ(M∖K) = 0). (P4) The restriction to U of a current Y ∈ D_k(ℝ^d), Y|_U(ω) := Y(ω) for ω ∈ D^k(U) ⊆ D^k(ℝ^d), is in D_k(U); if `IsLatticeChain ρ β Y` (on ℝ^d) then `IsLatticeChain ρ β (Y|_U)`.

Proof.

1. (Exhaustion function.) If U = ℝ^d let φ(x) := 1/(1+|x|); otherwise let φ(x) := min{dist(x, ℝ^d∖U), 1/(1+|x|)}. (If U = ∅ then T = 0 and P_k := 0 with β := 0, ρ_k := 1/(k+1) work; assume U ≠ ∅.) φ is Lipschitz with constant 1, φ > 0 on U, φ = 0 off U, and for λ > 0, {φ ≥ λ} ⊆ {x : dist(x,ℝ^d∖U) ≥ λ, |x| ≤ 1/λ} is compact and contained in U; in particular W_λ := {φ > λ/2} is open with compact closure in U ({φ ≥ λ/2}), i.e. W_λ ⊂⊂ U.

2. (Slices; 4.5 via the sibling theorem.) Apply `SlicingTheorem` to T, f = φ, L = 1 on U: we get S_t ∈ D_m(U) with `IsSlice T φ t S_t`, i.e. ∂(T⌞{φ < t}) = S_t + (∂T)⌞{φ < t} (sets intersected with U; P1 identifies the restrictions), spt S_t ⊆ spt T ∩ {φ = t}, and the mass bound. For k ≥ 1 apply the mass bound with W := W_{1/(k+1)} (open ⊆ U), L_W := 1 (|Dφ| ≤ 1 a.e.), a := 1/(k+1), b := 1/k and R := T⌞{a < φ < b}: there is a measurable g_k ≥ M_W(S_t) on (a,b) with ∫_a^b g_k ≤ M_W(R) = μ_T(W ∩ {a < φ < b}) ≤ μ_T({φ ≥ 1/(k+1)}) < ∞. Hence M_W(S_t) < ∞ for a.e. t ∈ (1/(k+1), 1/k). For such t, spt S_t ⊆ {φ = t} is a compact subset of W, so M(S_t) = M_W(S_t) < ∞ (a test form ω with ‖ω‖ ≤ 1 satisfies S_t(ω) = S_t(χω) with χ ∈ C_c^∞(W), 0 ≤ χ ≤ 1, χ = 1 near spt S_t). Doing this for all k, M(S_λ) < ∞ for a.e. λ ∈ (0,1).

3. (The truncated currents T′_λ.) For such λ let A_λ := {x ∈ U : φ(x) ≥ λ} and T′_λ := T⌞A_λ = T − T⌞{φ < λ}. Then T′_λ is integer multiplicity (P2), spt T′_λ ⊆ A_λ compact ⊆ U, M(T′_λ) ≤ μ_T(A_λ) < ∞, and ∂T′_λ = ∂T − ∂(T⌞{φ<λ}) = (∂T)⌞A_λ − S_λ, so M(∂T′_λ) ≤ μ_{∂T}(A_λ) + M(S_λ) < ∞. Moreover T′_λ(ω) = T(ω) whenever φ ≥ λ on tsupport ω, because then the integrand ⟨ω,T⃗⟩·1_{φ<λ} of T⌞{φ<λ}(ω) vanishes identically.

4. (Case of finite mass in ℝ^d — the printed first paragraph.) For X ∈ D_n(ℝ^d) integer multiplicity with M(X) + M(∂X) < ∞ and ρ > 0, `DeformationTheorem` gives integer valued β, Pc = Σβ_F[[F]] with `IsLatticeChain ρ β Pc`, and R, S with X − Pc = ∂R + S, M(R) ≤ CρM(X), M(S) ≤ CρM(∂X). Hence for every ω ∈ D^n(ℝ^d): |X(ω) − Pc(ω)| = |R(dω) + S(ω)| ≤ M(R)‖dω‖ + M(S)‖ω‖ ≤ Cρ(M(X)‖dω‖ + M(∂X)‖ω‖) (printed (1),(2)).

5. (Diagonal choice — the printed last paragraph.) Index by k ∈ ℕ = {0,1,2,…}. Choose λ_k ↓ 0 (k ≥ 0) with λ_k ∈ (0,1) admissible in Step 2 (possible since admissible λ form a full-measure subset of (0,1)), and let X_k := (T′_{λ_k})~ ∈ D_n(ℝ^d) (P3): integer multiplicity, M(X_k) + M(∂X_k) < ∞. Define ρ_k := min{ρ_{k−1}, 1/((k+1)(1 + M(X_k) + M(∂X_k)))} for k ≥ 1 and ρ₀ := 1/(1 + M(X₀) + M(∂X₀)). Then ρ_k > 0 for all k ∈ ℕ, ρ is antitone and ρ_k → 0. By Step 4 with X = X_k, ρ = ρ_k obtain integer valued β_k and Pc_k with `IsLatticeChain ρ_k β_k Pc_k` and |X_k(ω) − Pc_k(ω)| ≤ (C/(k+1))(‖dω‖ + ‖ω‖) for ω ∈ D^n(ℝ^d). Let P_k := Pc_k|_U (P4): `IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (P_k)` for every k ∈ ℕ.

6. (Weak convergence.) Let ω ∈ D^n(U). K := tsupport ω is compact ⊆ U, so φ ≥ δ > 0 on K. For k with λ_k < δ, X_k(ω) = T′_{λ_k}(ω) = T(ω) (P3 and Step 3). Hence |P_k(ω) − T(ω)| = |Pc_k(ω) − X_k(ω)| ≤ (C/(k+1))(‖dω‖ + ‖ω‖) → 0. So `WeaklyConvergesOn P T`, and (ρ, β, P) witness `PolyhedralApproximation`. (In the special case U = ℝ^d with M(T), M(∂T) < ∞ one may take X_k = T directly, which is the printed first paragraph.)

## Key steps

1. Lipschitz exhaustion function φ with {φ ≥ λ} compact in U.
2. Sibling slicing theorem: for a.e. λ ∈ (0,1) the slice ⟨T,φ,λ⟩ has finite mass.
3. T′_λ := T⌞{φ ≥ λ} is integer multiplicity with compact support and finite mass and boundary mass; extend to ℝ^{m+1+ℓ}.
4. Sibling deformation theorem at scale ρ: |X(ω) − Pc(ω)| ≤ Cρ(M(X)‖dω‖ + M(∂X)‖ω‖).
5. Diagonal choice λ_k ↓ 0, antitone ρ_k → 0 small relative to the masses; restrict the lattice chains to U.
6. For each test form, T′_{λ_k}(ω) = T(ω) eventually, so P_k(ω) → T(ω).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def |^structure |^theorem main_theorem' project/GMT/Ch06/Contract.lean`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all byte-identical)`
- `python3 listing of dag.json nodes (only 'root'; no reserved child lean_name)`
- `python3 audit of nodes/root/decomposition-audit-v2.json and decomposition-v2.json (only deformation A3 rejected; search of all 12 proofs for 'θ′ ≥ 1', 'σ-finite', 'Radon–Nikodym', 'IsLipschitzPushforward', 'LipschitzPushforwardIntegerMultiplicity', 'as in the conventions')`
- `rg -n 'theorem sigmaFinite_of_countable' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `rg -n 'theorem mul_meas_ge_le_lintegral₀' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n 'theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite|theorem Integrable.ae_eq_of_forall_setIntegral_eq' mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `rg -n 'theorem hausdorffMeasure_image_le (h : LipschitzWith' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem restrict_congr_set|theorem restrict_restrict [(]|theorem ae_restrict_iff.₀|theorem ae_restrict_mem₀' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -il 'coarea|co-area' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -il 'Besicovitch.Federer|purely unrectifiable' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique|def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'abbrev NVector|def simpleNVector|def nVectorPushforward|theorem nVectorPushforward_simple|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/`
- `#print MeasureTheory.Measure.euclideanHausdorffMeasure (μHE[d] = volume.addHaarScalarFactor μH[d] • μH[d])`
- `grep -n '1.12|1.15|Borel-regular|3.19|3.24' book/chapter-01.txt`
- `lake build GMT.Ch06.Submission (scratch /tmp/gmt_ch06_v3_check, frozen commit d8d46c9, pinned packages)`
- `lake env lean Scratch/V3_Stmts.lean (12 child statements in gmt-compare.py contract_scope; 0 errors)`
- `lake env lean Scratch/V3_Assembly.lean (exact Submission.<name>; 12-way assembly vs type_of% GMT.Ch06.main_theorem; ff_from_siblings; parent_from_children; #print axioms)`
- `lake env lean Scratch/V3_SigmaFinite.lean (v3_sigmaFinite_restrict; #print axioms)`
- `lake env lean Scratch/V3_Tangent.lean (v3_weightedTangent_congr; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Stmts.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Assembly.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_SigmaFinite.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Tangent.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract, a byte-identical Submission with no Submission.* declarations, and the README. The DAG contains only root, so the 12 bare child names are unreserved. All 12 conjuncts are `def … : Prop` in namespace GMT.Ch06. In a scratch build of the frozen project, every child statement elaborates in the comparator's child scope, `exact Submission.<name>` resolves for all 12 children, and the 12-way assembly typechecks against `type_of% GMT.Ch06.main_theorem`. FedererFlemingCompactness follows from its three declared siblings and the parent from the other 11 children, with axioms [propext, Classical.choice, Quot.sound]. The contract's `IsLipschitzPushforward` supplies only an `IsRectifiableTriple` representation (θ′ > 0 real, integrable on compacts), confirming the v2 defect. The repaired deformation A3 uses only that. Its σ-finiteness step is kernel-checked as `v3_sigmaFinite_restrict` (via Mathlib `Measure.sigmaFinite_of_countable`, `mul_meas_ge_le_lintegral₀`, `Measure.restrict_restrict`, `ae_restrict_mem₀`), and its tangent-space step as `v3_weightedTangent_congr`, against the actual SimonGMT `HasWeightedApproximateTangentSpaceAt`/`blowUpMap` definitions (via `LipschitzWith.hausdorffMeasure_image_le`, `Measure.restrict_congr_set`, `ae_restrict_iff'₀`; μHE[d] is a scalar multiple of μH[d]), both with standard axioms only. Mathlib provides Radon–Nikodym-type uniqueness (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`, `Integrable.ae_eq_of_forall_setIntegral_eq`). SimonGMT provides `nVectorPushforward_simple`, `covectorEuclideanNorm` and `HasWeightedApproximateTangentSpaceAt.unique`. Simon Ch. 1 gives 1.12 (μ⌞Y is Borel regular for measurable Y of finite measure), 1.15(2) (inner regularity) and 2.6 (H^m is Borel regular), as cited. There is no Mathlib match for co-area or for Besicovitch–Federer/purely unrectifiable; these are cited from Simon Ch. 3, as SimonGMT omits them. These checks do not certify the analytic proofs.
