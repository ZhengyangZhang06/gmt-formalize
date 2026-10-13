# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1`
- Child DAG node: `root.polyhedral_approximation-a1.measure_uniqueness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is the uniqueness half of Simon's representation (2.7) used for the restriction (2.9) in the supplied proof's (P1): the signed Radon measures g₁μ₁⌞U and g₂μ₂⌞U agree on C_c^∞(U), hence agree. Note that ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) is C^∞ (it is definitionally ContDiff ℝ ∞ with the ContDiff notation).

1. (Localization.) Fix A and u, and let K := tsupport u, a compact subset of U.
   - If K = ∅, then u ≡ 0 and both sides vanish. Assume K ≠ ∅.
   - By IsCompact.exists_cthickening_subset_open there is r > 0 with L := cthickening (2r) K ⊆ U. L is closed and bounded, hence compact.
   - O := thickening r K is open with K ⊆ O ⊆ L. Every function that vanishes outside K, or outside O, vanishes outside L.
2. (Finite measures.) For i = 1, 2, g_i is μ_i-integrable on L, hence a.e.-strongly measurable for μ_i⌞L. Fix a Borel function h_i with h_i = g_i μ_i⌞L-a.e.
   - Define ν_i⁺ := (μ_i⌞L).withDensity(x ↦ ofReal(h_i x)) and ν_i⁻ := (μ_i⌞L).withDensity(x ↦ ofReal(−h_i x)).
   - They are finite, since ν_i^±(ℝ^P) ≤ ∫_L |g_i| dμ_i < ∞.
   - Put λ₁ := ν₁⁺ + ν₂⁻ and λ₂ := ν₂⁺ + ν₁⁻; both are finite Borel measures.
3. (Integrals against λ_i.) Let b : ℝ^P → ℝ be bounded and Borel.
   - Integration against a finite-valued measurable density gives ∫ b dν_i^± = ∫_L b·h_i^± dμ_i, all finite, where h⁺ = max(h,0) and h⁻ = max(−h,0).
   - Since h_i⁺ − h_i⁻ = h_i = g_i μ_i⌞L-a.e., we get (★): ∫ b dλ₁ − ∫ b dλ₂ = ∫_L b g₁ dμ₁ − ∫_L b g₂ dμ₂.
4. (Agreement on smooth functions supported in O.) Let ψ be C^∞ with compact support and tsupport ψ ⊆ O.
   - Then tsupport ψ ⊆ U, so the hypothesis gives ∫ ψ g₁ dμ₁ = ∫ ψ g₂ dμ₂.
   - ψ vanishes outside O ⊆ L, so ψ g_i = 1_L ψ g_i and ∫ ψ g_i dμ_i = ∫_L ψ g_i dμ_i.
   - By (★) with b = ψ, ∫ ψ dλ₁ = ∫ ψ dλ₂.
5. (Radon–Nikodym.) Let ν := λ₁ + λ₂, a finite measure. Then λ_i ≪ ν.
   - With f_i := (x ↦ (λ_i.rnDeriv ν x).toReal), f_i is ν-integrable and ∫ b dλ_i = ∫ b f_i dν for every bounded Borel b (integral_rnDeriv_smul).
   - By step 4, ∫ ψ·(f₁ − f₂) dν = 0 for every C^∞ ψ with compact support and tsupport ψ ⊆ O.
   - f₁ − f₂ is ν-integrable, hence locally integrable on O. By IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, applied to the open set O, f₁ = f₂ ν-a.e. on O.
6. (Conclusion.) b := 1_A·u is bounded, Borel, and vanishes outside K ⊆ O.
   - Hence b f₁ = b f₂ ν-a.e., and ∫ b dλ₁ = ∫ b f₁ dν = ∫ b f₂ dν = ∫ b dλ₂.
   - By (★), ∫_L 1_A u g₁ dμ₁ = ∫_L 1_A u g₂ dμ₂.
   - Since u = 0 outside K ⊆ L, the μ_i-integrable function 1_A u g_i vanishes outside L, so ∫_L 1_A u g_i dμ_i = ∫_A u g_i dμ_i.
   Therefore ∫_A u g₁ dμ₁ = ∫_A u g₂ dμ₂. ∎

## Key steps

1. Localize: K = tsupport u, compact L = cthickening(2r) K ⊆ U, open O = thickening r K.
2. Finite measures λ₁ = g₁⁺μ₁⌞L + g₂⁻μ₂⌞L and λ₂ = g₂⁺μ₂⌞L + g₁⁻μ₁⌞L with identity (★).
3. λ₁ and λ₂ agree on smooth functions supported in O.
4. Radon–Nikodym w.r.t. λ₁+λ₂ and IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero: densities agree a.e. on O.
5. Integrate 1_A·u against λ₁, λ₂ and unwind (★).

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
