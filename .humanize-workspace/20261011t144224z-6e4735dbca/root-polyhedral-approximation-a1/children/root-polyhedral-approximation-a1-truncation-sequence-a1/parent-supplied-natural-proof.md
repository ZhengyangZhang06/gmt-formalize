# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1`
- Child DAG node: `root.polyhedral_approximation-a1.truncation_sequence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 6.2, second paragraph of the printed proof (p. 169), with Steps 1–3 and the λ-choice of Step 5 of the supplied parent proof. The printed proof takes a Lipschitz φ with φ > 0 in U, φ ≡ 0 off U and {φ > λ} ⊂⊂ U. For L¹-a.e. λ > 0, 4.5 gives T_λ ≡ T⌞{φ > λ} with M(∂T_λ) < ∞; since spt T_λ ⊂ U, the finite-mass case applies (errata: ‘ans’ = and, ‘{x D φ(x) > λ}’ = {x : φ(x) > λ}). We truncate exactly as printed, by the open sets {φ > λ}. The frozen SlicingTheorem describes ⟨T,f,t⟩ = ∂(T⌞{f<t}) − (∂T)⌞{f<t} (4.6). We apply it with f = −φ and t = −λ, so {f < t} = {φ > λ}; this is 4.7 up to sign. The supplied proof's variant T⌞{φ ≥ λ} would need its density argument (P2) at points of {φ = λ}. With the open set {φ > λ}, the tangent condition is local (sibling open_truncation).

Notation. n := m + 1; |α| := covectorEuclideanNorm α; W ⊂⊂ U means CompactlyContainedOpen W U. A test form ω ∈ Dⁿ(U) is regarded as an element of Dⁿ(ℝ^P) via testFormOnInclusion, which does not change the underlying form.

0. (Representation.) T is integer multiplicity, so there are M, θ, ξ with IsRectifiableTriple U n M θ ξ, θ(x) ∈ ℕ for x ∈ M, and T(ω) = tauAction n M θ ξ ω = ∫_M θ⟨ω,ξ⟩ dHⁿ for all ω ∈ Dⁿ(U). In particular M ⊆ U.
1. (Exhaustion function.) If U = ℝ^P let φ(x) := 1/(1+|x|). Otherwise let φ(x) := min{dist(x, ℝ^P∖U), 1/(1+|x|)}, using Metric.infDist; this case includes U = ∅, where φ ≡ 0.
   (a) φ is 1-Lipschitz on ℝ^P. x ↦ dist(x,F) is 1-Lipschitz (lipschitz_infDist_pt). For a, b ≥ 0, |1/(1+a) − 1/(1+b)| = |a−b|/((1+a)(1+b)) ≤ |a−b|, and ||x| − |y|| ≤ |x−y|. A minimum of 1-Lipschitz functions is 1-Lipschitz.
   (b) For t > 0, K_t := {x : φ(x) ≥ t} is compact and K_t ⊆ U. It is closed because φ is continuous, and contained in the closed ball of radius 1/t. If U ≠ ℝ^P and x ∈ K_t, then dist(x, ℝ^P∖U) ≥ t > 0, while dist(y, ℝ^P∖U) = 0 for y ∉ U; so x ∈ U.
   (c) φ > 0 on U. If U ≠ ℝ^P, then ℝ^P∖U is closed and nonempty, so dist(x, ℝ^P∖U) > 0 for x ∈ U (IsClosed.notMem_iff_infDist_pos). Consequently, for every compact K ⊆ U there is δ > 0 with φ ≥ δ on K: this is trivial for K = ∅, and otherwise the continuous φ attains a positive minimum on K.
   For t > 0 put V_t := {x : φ(x) > t}. It is open with closure V_t ⊆ K_t, so V_t ⊂⊂ U and V_t ⊆ U.
2. (Slices.) f := −φ is 1-Lipschitz on U. Apply SlicingTheorem to P, m, U, T, f and L = 1; its hypotheses are ours. We get S : ℝ → D_m(U) such that (i) IsSlice T f s (S s) for every s ∈ ℝ, and (iv) the mass bound holds.
   - By (i), for each s there are A_s ∈ Dⁿ(U) and B_s ∈ D_m(U) with IsRestriction T {x ∈ U : f(x) < s} A_s and IsRestriction ∂T {x ∈ U : f(x) < s} B_s.
   - Also S_s(ψ) = ∂A_s(ψ) − B_s(ψ) = A_s(dψ) − B_s(ψ) for ψ ∈ D^m(U).
   - Note {x ∈ U : f(x) < −λ} = U ∩ V_λ.
   - Unpacking IsRestriction for s = 0 gives a measure representation (μ, v) of T (IsMeasureRepresentation T μ v).
3. (Choice of levels.) Fix k ∈ ℕ. Put a := −1/(k+1) < b := −1/(k+2) and W_k := V_{1/(2(k+2))}; W_k is open, W_k ⊆ U and W_k ⊂⊂ U by step 1.
   - E_k := {x ∈ U : a < f(x) < b} is Borel (U open, f continuous).
   - By restriction_exists (a) with (μ, v) there is R_k with IsRestriction T E_k R_k. By restriction_exists (b), M_{W_k}(R_k) < ∞.
   - f is 1-Lipschitz on ℝ^P, so ‖fderiv ℝ f x‖ ≤ 1 for every x (norm_fderiv_le_of_lipschitz). Hence L_W := 1 satisfies the a.e. derivative hypothesis on W_k.
   - The mass bound of SlicingTheorem (for W_k, L_W = 1, a < b and R_k) gives a measurable g_k : ℝ → [0,∞] with M_{W_k}(S_s) ≤ g_k(s) for s ∈ (a,b) and ∫_{(a,b)} g_k ≤ M_{W_k}(R_k) < ∞.
   - Hence g_k < ∞ for L¹-a.e. s ∈ (a,b) (ae_lt_top for the restricted measure). Since L¹((a,b)) = b − a > 0, there is s_k ∈ (a,b) with g_k(s_k) < ∞, i.e. M_{W_k}(S_{s_k}) < ∞.
   - Put λ_k := −s_k, so 1/(k+2) < λ_k < 1/(k+1).
4. (Truncated currents.) For each k apply open_truncation to (M, θ, ξ), U and V := V_{λ_k} ⊂⊂ U. This gives an integer multiplicity X_k ∈ Dⁿ(ℝ^P) with M(X_k) < ∞ and X_k(η) = tauAction n (M ∩ V_{λ_k}) θ ξ η = ∫_{M∩V_{λ_k}} θ⟨η,ξ⟩ dHⁿ for every η ∈ Dⁿ(ℝ^P). (X_k is the printed T_{λ_k} = T⌞{φ > λ_k}, extended to ℝ^P.)
5. (Finite boundary mass.) Fix k and write λ := λ_k, s := s_k = −λ, A := A_s, B := B_s, S := S_s and W := W_k.
   (a) Apply restriction_tau to U, T = τ(M,θ,ξ) and IsRestriction T {x ∈ U : f(x) < s} A. It gives A(η) = tauAction n (M ∩ {x ∈ U : f(x) < s}) θ ξ η for η ∈ Dⁿ(U). Since M ⊆ U, M ∩ {x ∈ U : −φ(x) < −λ} = M ∩ V_λ. Hence A(η) = ∫_{M∩V_λ} θ⟨η,ξ⟩ dHⁿ.
   (b) By restriction_exists (b), applied to the current ∂T ∈ D_m(U) and B, M_W(B) < ∞. By step 3, M_W(S) < ∞.
   (c) (Cut-off.) F₁ := {φ ≥ 3λ/4} and F₀ := {φ ≤ λ/2} are disjoint closed sets.
       - By the smooth Urysohn lemma (exists_contMDiffMap_zero_one_of_isClosed, model 𝓘(ℝ, ℝ^P), smoothness ∞) there is a C^∞ function χ : ℝ^P → [0,1] with χ = 0 on F₀ and χ = 1 on F₁.
       - Then {χ ≠ 0} ⊆ {φ > λ/2}, so tsupport χ ⊆ K_{λ/2}.
       - K_{λ/2} is compact, contained in U, and contained in W because λ/2 > 1/(2(k+2)).
   (d) Let ψ ∈ D^m(ℝ^P) with |ψ(x)| ≤ 1 for all x; these are the admissible forms for M(∂X_k) = M_{ℝ^P}(∂X_k). Put ψ′ := χψ (x ↦ χ(x)·ψ(x)).
       - ψ′ is C^∞ with compact support and tsupport ψ′ ⊆ tsupport χ ⊆ W ⊆ U, so ψ′ ∈ D^m(U).
       - By homogeneity of covectorEuclideanNorm, |ψ′(x)| = χ(x)·|ψ(x)| ≤ 1.
       - Hence ψ′ ∈ massAdmissibleOn U m W.
   (e) On the open set O := {φ > 3λ/4} ⊆ F₁ we have ψ′ = ψ.
       - The exterior derivative is computed pointwise from fderiv: extDeriv ω x = alternatizeUncurryFin (fderiv ℝ ω x). fderiv depends only on the germ (Filter.EventuallyEq.fderiv_eq). So dψ′ = dψ on O.
       - Since V_λ ⊆ O, the integrands θ(x)⟨dψ(x),ξ(x)⟩ and θ(x)⟨dψ′(x),ξ(x)⟩ agree at every x ∈ M ∩ V_λ.
       - Therefore, by step 4, (a) and IsSlice: ∂X_k(ψ) = X_k(dψ) = ∫_{M∩V_λ} θ⟨dψ,ξ⟩ dHⁿ = ∫_{M∩V_λ} θ⟨dψ′,ξ⟩ dHⁿ = A(dψ′) = S(ψ′) + B(ψ′).
   (f) By (d), ofReal S(ψ′) ≤ M_W(S) and ofReal B(ψ′) ≤ M_W(B) (le_massOn). Hence ofReal ∂X_k(ψ) ≤ ofReal S(ψ′) + ofReal B(ψ′) ≤ M_W(S) + M_W(B). Taking the supremum over admissible ψ, M(∂X_k) ≤ M_W(S) + M_W(B) < ∞ by (b). With step 4, M(X_k) + M(∂X_k) < ∞.
6. (Eventual agreement.) Let ω ∈ Dⁿ(U) and K := tsupport ω, compact with K ⊆ U.
   - By step 1(c) choose δ > 0 with φ ≥ δ on K, and k₀ with 1/(k₀+1) < δ.
   - For k ≥ k₀, λ_k < 1/(k+1) ≤ 1/(k₀+1) < δ, so K ⊆ V_{λ_k}.
   - x ↦ θ(x)⟨ω(x),ξ(x)⟩ vanishes outside K, so it equals 1_{V_{λ_k}}(x)·θ(x)⟨ω(x),ξ(x)⟩ everywhere.
   - By setIntegral_indicator (V_{λ_k} open), X_k(ω) = ∫_{M∩V_{λ_k}} θ⟨ω,ξ⟩ dHⁿ = ∫_M θ⟨ω,ξ⟩ dHⁿ = T(ω).
   Thus X_k(ω) = T(ω) for all k ≥ k₀, which is the eventual equality. ∎

## Key steps

1. Represent T = τ(M,θ,ξ); build the 1-Lipschitz exhaustion φ with {φ ≥ t} compact in U and V_t = {φ > t} ⊂⊂ U.
2. Apply SlicingTheorem to f = −φ: IsSlice gives A = T⌞(U∩V_λ), B = (∂T)⌞(U∩V_λ), S = ∂A − B, and a representation of T.
3. Use restriction_exists to get R_k and finite M_{W_k}(R_k); the slicing mass bound picks λ_k ∈ (1/(k+2), 1/(k+1)) with M_{W_k}(S) < ∞.
4. open_truncation gives an integer multiplicity X_k = τ(M ∩ V_{λ_k}, θ, ξ) on ℝ^P of finite mass.
5. Use restriction_tau (A = τ(M∩V_λ)), a smooth cut-off χ, and locality of d: ∂X_k(ψ) = S(χψ) + B(χψ), so M(∂X_k) ≤ M_W(S) + M_W(B) < ∞.
6. For ω ∈ Dⁿ(U), tsupport ω ⊆ V_{λ_k} eventually, so X_k(ω) = T(ω).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def (PolyhedralApproximation|IsLatticeChain|IsSlice|IsRestriction|IsMeasureRepresentation|IsIntegerMultiplicity|DeformationTheorem|SlicingTheorem|tauAction|CompactlyContainedOpen)|^structure IsRectifiableTriple' project/GMT/Ch06/Contract.lean`
- `rg -n 'polyhedral_approx|restrictDomain|testFormOnInclusion' project/ (no match)`
- `cmp project/GMT/Ch06/Contract.lean and project/GMT/Ch06/Submission.lean against the workspace copies (byte-identical)`
- `grep lean_name in dag.json and nodes/*/decomposition-v*.json (polyhedral_approx_* unused; only sibling decomposition is root-federer-fleming-a1, should_split false)`
- `rg -n 'ext_alternating' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `rg -n 'theorem (ext_of_forall_integral_eq_of_IsFiniteMeasure|IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|ae_eq_zero_of_integral_contDiff_smul_eq_zero|integral_rnDeriv_smul|setIntegral_indicator|ae_lt_top|norm_fderiv_le_of_lipschitz|norm_iteratedFDeriv_zero|exists_contMDiffMap_zero_one_of_isClosed|countable_meas_level_set_pos|ae_restrict_mem₀)' mathlib/Mathlib`
- `rg -n 'exists_cthickening_subset_open' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean; rg -n 'Filter.EventuallyEq.fderiv_eq' mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean; rg -n 'def extDeriv' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean; rg -n 'theorem map_perm' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean; rg -n 'def orderEmbOfFin' mathlib/Mathlib/Data/Finset/Sort.lean`
- `rg -n 'infDist_pos|infDist_empty|lipschitz_infDist_pt' mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -ln 'euclideanCovectorCoordinate|covectorEuclideanNorm' simongmt/Poincare/SimonGMT (definitions only in FormsDuality/Mass/FormSupNorm; no coordinate-expansion lemma)`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'theorem simon_theorem_3_6' simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `grep -n '6.2 (Weak Polyhedral|4.5 Lemma|4.6|4.7|4.10' book/chapter-06.txt`
- `python3 contract_scope(Contract.lean, GMT.Ch06.main_theorem) from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all 7 statements`
- `lake build GMT.Ch06.Submission (scratch /tmp/pa_decomp_check, frozen d8d46c9, pinned packages)`
- `lake env lean Scratch/FinalStmts.lean (7 child statements as theorem _root_.HumanizeNodeComparator.target_<key>; elaborate)`
- `lake env lean Scratch/Assembly.lean (PolyhedralApproximation from finite_mass_approximation and truncation_sequence; #print axioms = propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/C5Skeleton.lean; lake env lean Scratch/C2Skeleton.lean (interface skeletons typecheck)`
- `lake env lean Scratch/Locality.lean; lake env lean Scratch/CoordBound.lean (#print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Finset/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-federer-fleming-a1/decomposition-v1.json`
- `/tmp/pa_decomp_check/Scratch/FinalStmts.lean`
- `/tmp/pa_decomp_check/Scratch/Assembly.lean`
- `/tmp/pa_decomp_check/Scratch/C5Skeleton.lean`
- `/tmp/pa_decomp_check/Scratch/C2Skeleton.lean`
- `/tmp/pa_decomp_check/Scratch/Locality.lean`
- `/tmp/pa_decomp_check/Scratch/CoordBound.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract and a byte-identical Submission with no Submission.* declarations. It contains no polyhedral_approx_* names, and none occur in the DAG or any node directory, so the seven proposed names are free. The contract supplies every notion the children use: IsMeasureRepresentation, IsRestriction, IsSlice, tauAction, IsRectifiableTriple, IsIntegerMultiplicity, IsLatticeChain, CompactlyContainedOpen, DeformationTheorem and SlicingTheorem. SimonGMT supplies GeometricCurrentOn, massOn/massAdmissibleOn, restrictDomain/testFormOnInclusion, covectorEuclideanNorm, euclideanCovectorCoordinate, wedgeCovectors (with wedgeCovectors_apply_det), simpleNVector (mkContinuous bound), HasWeightedApproximateTangentSpaceAt/blowUpMap and CountablyRectifiable.mono. SimonGMT has no coordinate-expansion lemma for the Λ_n × Λ^n pairing and no restriction-uniqueness lemma; these become the children pairing_expansion and measure_uniqueness/restriction_tau. The density theorem simon_theorem_3_6 exists, but the open-set truncation makes it unnecessary. Mathlib at the pin provides the cited tools: Module.Basis.ext_alternating, AlternatingMap.map_perm, Finset.orderEmbOfFin, IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (no local-finiteness hypothesis), integral_rnDeriv_smul, setIntegral_indicator, ae_lt_top, norm_fderiv_le_of_lipschitz, norm_iteratedFDeriv_zero, exists_contMDiffMap_zero_one_of_isClosed, IsCompact.exists_cthickening_subset_open, Filter.EventuallyEq.fderiv_eq, IsClosed.notMem_iff_infDist_pos and lipschitz_infDist_pt; extDeriv is pointwise alternatizeUncurryFin (fderiv). In a scratch build of the frozen project, all seven statements pass validate_lean_statement and elaborate in the comparator's child scope. The parent assembly compiles from finite_mass_approximation and truncation_sequence with axioms [propext, Classical.choice, Quot.sound]. The truncation_sequence and restriction_tau skeletons typecheck against their sibling statements. The tangent-locality step of open_truncation and the coordinate bound of pairing_expansion are fully kernel-checked with standard axioms. These checks validate contracts and selected steps, not complete child proofs.
