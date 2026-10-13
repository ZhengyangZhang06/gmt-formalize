# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1`
- Child DAG node: `root.polyhedral_approximation-a1.open_truncation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is the supplied proof's (P2)+(P3) for an open truncation set: X is T⌞V for T = τ(M,θ,ξ), extended to ℝ^P, as for the printed T_λ = T⌞{φ > λ}.

Let N := closure V (compact, N ⊆ U), M′ := M ∩ V and Hⁿ := μHE[n]. For I ∈ SimonMultiIndex n P let dx^I := wedgeCovectors n (fun j => EuclideanSpace.proj (I j)). For an n-covector α let α_I := euclideanCovectorCoordinate α I and |α| := covectorEuclideanNorm α.

1. (Integrability of θ.) By the triple field integrableOn with K = N, θ is Hⁿ-integrable on M ∩ N. Since M′ ⊆ M ∩ N, θ is integrable on M′ and on M′ ∩ K for every set K. In particular θ is a.e.-strongly measurable for Hⁿ⌞M′. Put Θ := ∫_{M′} θ dHⁿ < ∞.
2. (Bounds for ξ.) For Hⁿ-a.e. x ∈ M, ξ(x) = ±simpleNVector τ with τ orthonormal, and ‖simpleNVector τ‖ ≤ Π_i |τ_i| = 1 (mkContinuous bound). Hence |ξ(x)(α)| ≤ ‖α‖ for all n-covectors α. Moreover, by pairing_expansion (ξ(x)(α) = Σ_I α_I ξ(x)(dx^I) and |α_I| ≤ |α|), |ξ(x)(α)| ≤ c_*·|α| for a.e. x ∈ M, where c_* := Σ_I ‖dx^I‖.
3. (The functional.) Let ω ∈ Dⁿ(ℝ^P) and F_ω(x) := θ(x)·ξ(x)(ω(x)).
   - F_ω is a.e.-strongly measurable for Hⁿ⌞M′: θ is by step 1, and x ↦ ξ(x)(ω(x)) composes the a.e.-strongly measurable pair (ξ, ω) with the continuous evaluation map.
   - |F_ω| ≤ θ·sup_y ‖ω(y)‖ a.e. on M′ by step 2; the supremum is finite because ω is continuous with compact support.
   - Hence F_ω is Hⁿ⌞M′-integrable. Define X(ω) := ∫_{M′} F_ω dHⁿ = tauAction n M′ θ ξ ω.
   - X is linear, by linearity of each ξ(x) and of the integral of integrable functions.
4. (Continuity.) Let ω_j → 0 in Dⁿ(ℝ^P), i.e. TestFormOnConverges ω_j 0 for the domain univ. All tsupports lie in one compact K, and ω_j → 0 uniformly on K (0-th derivative; ‖iteratedFDeriv ℝ 0 ω_j x‖ = ‖ω_j(x)‖). So ε_j := sup_x ‖ω_j(x)‖ → 0, and |X(ω_j)| ≤ ε_j·Θ → 0 by step 2. Hence X ∈ D_n(ℝ^P) (a GeometricCurrentOn univ n) and X(ω) = tauAction n (M ∩ V) θ ξ ω for all ω.
5. (Finite mass.) If ω ∈ Dⁿ(ℝ^P) has |ω(x)| ≤ 1 for all x, then by step 2, X(ω) ≤ ∫_{M′} θ·|ξ(ω)| dHⁿ ≤ c_*·Θ. Hence M(X) = M_{ℝ^P}(X) ≤ ofReal(c_*Θ) < ∞.
6. (Tangent planes are local.) Claim: if x ∈ V and HasWeightedApproximateTangentSpaceAt n M θ x Q, then HasWeightedApproximateTangentSpaceAt n M′ θ x Q.
   - The dimension condition finrank Q = n is unchanged.
   - Let f ∈ C_c(ℝ^P, ℝ). Choose R > 0 with tsupport f ⊆ B̄_R(0), and δ > 0 with B_δ(x) ⊆ V (V open).
   - Let 0 < r < δ/R, η := blowUpMap x r (y ↦ r⁻¹(y − x)), g(y) := f(y)·θ(x + r•y) and B := B̄_R(0), a closed Borel set.
   - f vanishes off B, so g = 1_B·g. By setIntegral_indicator (which needs only B measurable), ∫_{η(M)} g dHⁿ = ∫_{η(M)∩B} g dHⁿ, and likewise for M′.
   - η(M) ∩ B = η(M′) ∩ B. Indeed, if y = η(z) with z ∈ M and |y| ≤ R, then |z − x| = r|y| ≤ rR < δ, so z ∈ V and z ∈ M′. The other inclusion is clear.
   - Hence the integrals of Simon's Definition 1.7 for M and for M′ coincide for every r ∈ (0, δ/R), a set in 𝓝[>] 0. So they have the same limit θ(x)∫_Q f dHⁿ (Tendsto.congr′).
   - This step has been kernel-checked against the SimonGMT definitions.
7. (Integer multiplicity.) The triple (M′, θ, ξ) satisfies IsRectifiableTriple univ n M′ θ ξ:
   - M′ ⊆ ℝ^P.
   - M′ = M ∩ V is Hⁿ-null-measurable, because M is and V is open.
   - M′ is countably n-rectifiable (CountablyRectifiable.mono, M′ ⊆ M).
   - θ > 0 on M′ ⊆ M.
   - θ is Hⁿ-integrable on M′ ∩ K for every compact K (step 1).
   - ξ is a.e.-strongly measurable for Hⁿ⌞M′, the restriction of Hⁿ⌞M to a subset (mono_measure).
   - Orientation: Hⁿ⌞M′ ≤ Hⁿ⌞M, so for Hⁿ⌞M′-a.e. x we have x ∈ M′ (ae_restrict_mem₀ with null-measurability) and the orientation property of (M,θ,ξ) holds. That is, there is an orthonormal τ with HasWeightedApproximateTangentSpaceAt n M θ x (span τ) and ξ(x) = ±simpleNVector τ. Since x ∈ V, step 6 gives the tangent condition for M′.
   Finally θ(x) ∈ ℕ for x ∈ M′ ⊆ M, and X(ω) = tauAction n M′ θ ξ ω for all ω ∈ Dⁿ(ℝ^P). Hence X is integer multiplicity, witnessed by the triple (M ∩ V, θ, ξ), and M(X) < ∞ by step 5. ∎

## Key steps

1. θ is integrable on M ∩ closure V; ξ is a.e. a unit simple n-vector (‖ξ(x)‖ ≤ 1).
2. X(ω) := ∫_{M∩V} θ⟨ω,ξ⟩ dHⁿ is linear and sequentially continuous on Dⁿ(ℝ^P).
3. pairing_expansion gives |⟨α,ξ(x)⟩| ≤ (Σ_I ‖dx^I‖)·covectorEuclideanNorm α, so M(X) < ∞.
4. For x in the open set V, weighted tangent planes of M and M∩V coincide (blow-ups agree on supp f for small r).
5. (M∩V, θ, ξ) is a rectifiable triple in ℝ^P with θ ∈ ℕ, so X is integer multiplicity.

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
