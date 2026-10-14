# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1`
- Child DAG node: `root.polyhedral_approximation-a1.finite_mass_approximation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, 6.2, first paragraph of the printed proof (p. 169). For any ρ_k ↓ 0, the scaled deformation theorem (with ρ = ρ_k) gives T − P_k = ∂R_k + S_k (printed (1)) with M(R_k) ≤ cρ_k M(T) and M(S_k) ≤ cρ_k M(∂T) (printed (2)). Hence P_k(ω) → T(ω); the printed ‘T_k(ω)’ is a misprint for T(ω), and the printed F_n(ρ_k), β_R^{(k)} mean 𝓛_n(ρ_k), β_F^{(k)}. Here this is applied to a sequence X_k with the mass-dependent choice of ρ_k from Step 5 of the supplied parent proof.

Notation. d := m+1+ℓ, n := m+1. For a j-covector α, |α| := covectorEuclideanNorm α and ‖α‖ is the operator norm. M(Y) = M_{ℝ^d}(Y) = Y.massOn univ.

1. (Homogeneity.) For a ∈ ℝ and a j-covector α, |aα| = |a|·|α|: each coordinate (aα)(e_J) equals a·α(e_J), so the sum of squares is multiplied by a², and √(a²s) = |a|√s.
2. (Finite sup norms.) For a strictly increasing J : Fin j → Fin d, |α(e_J)| ≤ ‖α‖·Π_i ‖e_{J(i)}‖ = ‖α‖. Hence |α| ≤ √N_j·‖α‖, where N_j is the (finite) number of strictly increasing maps Fin j → Fin d.
   - A test form η ∈ D^j(ℝ^d) is continuous with compact support, so sup_x ‖η(x)‖ < ∞ and therefore sup_x |η(x)| < ∞.
   - For ω ∈ Dⁿ(ℝ^d), the form dω underlying exteriorDerivativeTestOn univ n ω is again a test form.
   - Fix c₀, c₁ > 0 with |ω(x)| ≤ c₀ and |dω(x)| ≤ c₁ for all x.
3. (Evaluation bound.) Let Y ∈ D_j(ℝ^d) with M(Y) < ∞, η ∈ D^j(ℝ^d), and c > 0 with |η(x)| ≤ c for all x. By step 1, c⁻¹η ∈ massAdmissibleOn univ j univ, so ofReal(Y(c⁻¹η)) ≤ M(Y), i.e. Y(η) ≤ c·M(Y).toReal. Applying this to −η gives |Y(η)| ≤ c·M(Y).toReal.
4. (Scales.) Let a_k := (M(X_k) + M(∂X_k)).toReal ≥ 0; then M(X_k).toReal ≤ a_k and M(∂X_k).toReal ≤ a_k. Define ρ₀ := 1/(1+a₀) and ρ_{k+1} := min{ρ_k, 1/((k+2)(1+a_{k+1}))}.
   - By induction ρ_k > 0.
   - ρ_{k+1} ≤ ρ_k, so ρ is antitone (antitone_nat_of_succ_le).
   - ρ_k ≤ 1/((k+1)(1+a_k)) ≤ 1/(k+1) for all k: for k = 0 by definition, and for k+1 by the second argument of min.
   - Hence ρ_k → 0, by squeezing between 0 and 1/(k+1).
5. (Deformation.) Let C = C(m,ℓ) ∈ ℝ≥0 be the constant that DeformationTheorem provides for m and ℓ (1 ≤ ℓ). For each k apply it to T := X_k (M(X_k) + M(∂X_k) < ∞) and ρ := ρ_k > 0. This gives Pc_k, β′_k : faces → ℝ, R_k ∈ D_{n+1}(ℝ^d) and S_k ∈ Dⁿ(ℝ^d) with:
   - IsLatticeChain ρ_k β′_k Pc_k;
   - X_k(ω) − Pc_k(ω) = ∂R_k(ω) + S_k(ω) = R_k(dω) + S_k(ω) for all ω;
   - M(R_k) ≤ C·ρ_k·M(X_k) and M(S_k) ≤ C·ρ_k·M(∂X_k);
   - since X_k is integer multiplicity, for every face F there is an integer equal to β′_k(F).
   Choose β_k(F) ∈ ℤ with β′_k(F) = β_k(F) (Classical.choose). Then IsLatticeChain ρ_k (F ↦ (β_k F : ℝ)) Pc_k is the same statement. Also M(R_k) and M(S_k) are finite, with M(R_k).toReal ≤ Cρ_k·M(X_k).toReal and M(S_k).toReal ≤ Cρ_k·M(∂X_k).toReal.
6. (Convergence.) Fix ω ∈ Dⁿ(ℝ^d) and c₀, c₁ from step 2. Apply step 3 to R_k with dω and c₁, and to S_k with ω and c₀:
   |Pc_k(ω) − X_k(ω)| = |R_k(dω) + S_k(ω)| ≤ c₁·M(R_k) + c₀·M(S_k) ≤ Cρ_k·(c₁·M(X_k) + c₀·M(∂X_k)) ≤ C(c₀+c₁)·ρ_k·a_k ≤ C(c₀+c₁)·a_k/((k+1)(1+a_k)) ≤ C(c₀+c₁)/(k+1).
   Hence Pc_k(ω) − X_k(ω) → 0. Together with steps 4 and 5, ρ, β and Pc have all the required properties. ∎

## Key steps

1. covectorEuclideanNorm is homogeneous, and every test form has a finite Euclidean sup norm.
2. Evaluation bound |Y(η)| ≤ c·M(Y) when |η| ≤ c, via the admissible form c⁻¹η.
3. Recursive scales ρ_{k+1} = min(ρ_k, 1/((k+2)(1+a_{k+1}))): positive, antitone, ρ_k ≤ 1/(k+1).
4. DeformationTheorem at scale ρ_k: X_k − Pc_k = ∂R_k + S_k with mass bounds and integer β (by choice).
5. |Pc_k(ω) − X_k(ω)| ≤ C(c₀+c₁)/(k+1) → 0.

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
