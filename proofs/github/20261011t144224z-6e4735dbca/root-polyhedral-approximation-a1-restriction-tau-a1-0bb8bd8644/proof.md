# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1`
- Child DAG node: `root.polyhedral_approximation-a1.restriction_tau-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is the supplied proof's (P1)/(P2): the restriction T⌞A does not depend on the representation, and for T = τ(M,θ,ξ) it equals τ(M∩A,θ,ξ).

Notation. dx^I, α_I and χ_K are as follows. For I ∈ SimonMultiIndex n P, dx^I := wedgeCovectors n (fun j => EuclideanSpace.proj (I j)) and α_I := euclideanCovectorCoordinate α I. For compact K ⊆ U, χ_K is a C^∞ function ℝ^P → [0,1] with compact support, tsupport χ_K ⊆ U and χ_K = 1 on K. It is obtained by choosing r > 0 with cthickening (2r) K ⊆ U (IsCompact.exists_cthickening_subset_open) and applying the smooth Urysohn lemma exists_contMDiffMap_zero_one_of_isClosed to the closed sets ℝ^P ∖ thickening r K and K. Write Hⁿ := μHE[n] and ν := Hⁿ⌞M = μHE[n].restrict M.

Unpack IsRestriction T A S: A is Borel, and there is a representation (μ, v) of T (IsMeasureRepresentation T μ v) with S(ω) = ∫_A v(x)(ω(x)) dμ for all ω ∈ Dⁿ(U).

1. (Unit simple n-vectors.) By the orientation field of the triple, for Hⁿ-a.e. x ∈ M, ξ(x) = ±simpleNVector τ for an orthonormal τ. simpleNVector τ is built by mkContinuous with bound Π_i |τ_i| = 1, so ‖ξ(x)‖ ≤ 1. Hence |ξ(x)(α)| ≤ ‖α‖ for ν-a.e. x and all n-covectors α.
2. (Coordinate functions.) For each I put g₁^I(x) := v(x)(dx^I) and g₂^I(x) := θ(x)·ξ(x)(dx^I).
   (a) g₁^I is μ-integrable on every compact K ⊆ U. The test form χ_K·dx^I ∈ Dⁿ(U) makes x ↦ χ_K(x)·g₁^I(x) μ-integrable, and this function equals g₁^I on K.
   (b) g₂^I is ν-integrable on every compact K ⊆ U. Here ν⌞K = Hⁿ⌞(K ∩ M) since K is Borel. θ is Hⁿ-integrable on M ∩ K (triple field integrableOn). The function x ↦ ξ(x)(dx^I) is a.e.-strongly measurable for Hⁿ⌞M (ξ is, and evaluation at a fixed covector is continuous linear) and bounded by ‖dx^I‖ a.e. by step 1. Hence the product is integrable.
3. (Agreement on smooth functions.) Let ψ : ℝ^P → ℝ be C^∞ with compact support and tsupport ψ ⊆ U.
   - Then ω_ψ := (x ↦ ψ(x)·dx^I) lies in Dⁿ(U), with v(x)(ω_ψ(x)) = ψ(x)·g₁^I(x) and θ(x)·ξ(x)(ω_ψ(x)) = ψ(x)·g₂^I(x).
   - By the representation and the τ formula for T: ∫ ψ g₁^I dμ = T(ω_ψ) = ∫_M θ ξ(ω_ψ) dHⁿ = ∫ ψ g₂^I dν.
4. (Uniqueness.) Apply measure_uniqueness with U, μ₁ := μ, μ₂ := ν, g₁ := g₁^I and g₂ := g₂^I; its hypotheses hold by steps 2 and 3. Hence for every Borel A′ and every continuous u with compact support and tsupport u ⊆ U, ∫_{A′} u g₁^I dμ = ∫_{A′} u g₂^I dν.
5. (Coordinates of ω.) Fix ω ∈ Dⁿ(U) and put u_I(x) := (ω(x))_I = ω(x)(e_{I(0)},…,e_{I(n−1)}).
   - u_I is continuous, because ω is continuous and evaluation at a fixed tuple is continuous linear on covectors.
   - u_I vanishes wherever ω vanishes, so it has compact support with tsupport u_I ⊆ tsupport ω ⊆ U.
   - Step 4 with A′ := A gives ∫_A u_I g₁^I dμ = ∫_A u_I g₂^I dν.
6. (Expansion.) By pairing_expansion with c = ω(x), applied to w = v(x) and to w = ξ(x) (then multiplied by θ(x)), for every x: v(x)(ω(x)) = Σ_I u_I(x) g₁^I(x) and θ(x)·ξ(x)(ω(x)) = Σ_I u_I(x) g₂^I(x). Each u_I g_i^I is integrable on A: u_I is bounded and vanishes outside the compact set tsupport ω ⊆ U, on which g_i^I is integrable by step 2.
7. (Conclusion.) Using steps 5 and 6 and finite additivity of the integral:
   S(ω) = ∫_A v(ω) dμ = Σ_I ∫_A u_I g₁^I dμ = Σ_I ∫_A u_I g₂^I dν = ∫_A θ ξ(ω) dν.
   Since A is measurable, ν⌞A = Hⁿ⌞(A ∩ M) (Measure.restrict_restrict). Hence ∫_A θ ξ(ω) dν = ∫_{M∩A} θ⟨ω,ξ⟩ dHⁿ = tauAction n (M ∩ A) θ ξ ω. ∎

## Key steps

1. Unpack IsRestriction: S(ω) = ∫_A ⟨ω,v⟩ dμ for some representation (μ,v) of T.
2. Coordinate functions g₁^I = v(·)(dx^I) w.r.t. μ and g₂^I = θ ξ(·)(dx^I) w.r.t. Hⁿ⌞M are locally integrable on U (‖ξ‖ ≤ 1 a.e.).
3. Both pair with smooth ψ to T(ψ dx^I).
4. measure_uniqueness: ∫_A u g₁^I dμ = ∫_A u g₂^I d(Hⁿ⌞M) for continuous compactly supported u.
5. Expand ω in coordinates (pairing_expansion), sum over I, and use (Hⁿ⌞M)⌞A = Hⁿ⌞(M∩A).

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
