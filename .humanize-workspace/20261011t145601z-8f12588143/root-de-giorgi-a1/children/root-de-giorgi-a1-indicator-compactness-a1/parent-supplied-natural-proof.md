# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1`
- Child DAG node: `root.de_giorgi-a1.indicator_compactness-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof Part 3b; Simon, Ch. 3, proof of Theorem 4.3, lines 653-655 ("by the Compactness Theorem 2.6 of Ch. 2, it follows that we can select a sequence ρ_k ↓ 0 so that χ_{ρ_k⁻¹E} → χ_F in L¹_loc", erratum E2: printed χ_R), and Simon, Ch. 2, Theorem 2.6 (chapter-02.txt lines 598-628), proved there by mollification and Arzelà's theorem ([GT01, Thm 7.22]). SimonGMT contains only the closure half (Chapter02/BV.lean, isLocallyBV_of_locallyL1_of_uniform_bound: "Extracting a convergent subsequence remains the compactness obligation") and Mathlib has no BV compactness, so the mollification/Arzelà-Ascoli route of the parent is written out.

Notation. L^N = volume; χ_k := 1_{F_k}; div g = euclideanDivergence g; φ ∈ C^∞_c(B_1(0)) with φ ≥ 0, ∫φ = 1, φ(−y) = φ(y), and φ_σ(y) := σ^{−N}φ(y/σ) for σ > 0.

Step 0 (N = 0). ℝ⁰ = {0}, so each F_k is ∅ or {0}. One of these two values is taken for infinitely many k; let φ enumerate those k increasingly and let G be that value (measurable). Then F_{φ(k)} Δ G = ∅ for all k, and the conclusion holds. From now on N ≥ 1.

Step 1 (reductions). Replacing each F_k by a measurable F_k' with L^N(F_k Δ F_k') = 0 changes neither the hypothesis nor the conclusion, so assume every F_k measurable. For each integer R ≥ 1 fix C_R and k_R such that the hypothesis holds for all k ≥ k_R; replacing C_R by max(C_R, 0) we may assume C_R ≥ 0. Applying the hypothesis to g and to −g (both admissible), |∫_{F_k} div g| ≤ C_R for k ≥ k_R and every admissible g.

Step 2 (translation estimate). For an integer R ≥ 1, h ∈ ℝ^N with |h| ≤ 1 and k ≥ k_{R+1}:
 ∫_{B_R(0)} |χ_k(y + h) − χ_k(y)| dy ≤ C_{R+1}|h|.
Proof. Let h ≠ 0 (h = 0 is trivial). Let ψ ∈ C¹_c(ℝ^N, ℝ) with tsupport ψ ⊆ B_R(0) and |ψ| ≤ 1. By translation invariance, ∫(χ_k(y + h) − χ_k(y))ψ(y) dy = ∫ χ_k(z)(ψ(z − h) − ψ(z)) dz. For each z, ψ(z − h) − ψ(z) = −∫_0^1 ⟨∇ψ(z − th), h⟩ dt = −∫_0^1 div Ψ_t(z) dt, where Ψ_t(z) := ψ(z − th)h. Each Ψ_t is C¹ with compact support, |Ψ_t| ≤ |h|, and tsupport Ψ_t = tsupport ψ + th ⊆ B_{R+1}(0) (tsupport ψ is a compact subset of B_R(0), hence lies in B̄_{R'}(0) for some R' < R, and |th| ≤ 1). By Fubini (bounded integrands with compact support), ∫ χ_k(ψ(· − h) − ψ) = −∫_0^1 ∫_{F_k} div Ψ_t dz dt, and Step 1 applied to Ψ_t/|h| gives |∫_{F_k} div Ψ_t| ≤ C_{R+1}|h|. Hence |∫(χ_k(· + h) − χ_k)ψ| ≤ C_{R+1}|h|. Finally let s := sgn(χ_k(· + h) − χ_k)·1_{B_R(0)}. There are ψ_j ∈ C^∞_c(ℝ^N) with tsupport ψ_j ⊆ B_R(0), |ψ_j| ≤ 1 and ψ_j → s a.e. (approximate s in L¹(B_R(0)) by continuous functions with compact support in B_R(0), truncate them to [−1, 1], mollify with radius smaller than the distance of their supports to ∂B_R(0) and less than 1/j, and pass to an a.e. convergent subsequence). Dominated convergence gives ∫_{B_R(0)} |χ_k(· + h) − χ_k| = lim_j ∫(χ_k(· + h) − χ_k)ψ_j ≤ C_{R+1}|h|.

Step 3 (mollification error). For σ ∈ (0, 1], an integer R ≥ 1 and k ≥ k_{R+1}: since (φ_σ * χ_k)(y) − χ_k(y) = ∫ φ_σ(h)(χ_k(y − h) − χ_k(y)) dh, Fubini and Step 2 (applied with −h, |h| ≤ σ ≤ 1) give
 ‖φ_σ * χ_k − χ_k‖_{L¹(B_R(0))} ≤ ∫ φ_σ(h) C_{R+1}|h| dh ≤ σ C_{R+1}.

Step 4 (equicontinuity). For fixed σ > 0 the functions v_k^σ := φ_σ * χ_k take values in [0, 1] and are Lipschitz with constant L_σ := ∫ |∇φ_σ|, uniformly in k: |v_k^σ(y) − v_k^σ(y')| ≤ ∫ |φ_σ(y − z) − φ_σ(y' − z)| dz ≤ |y − y'| ∫ |∇φ_σ|.

Step 5 (diagonal subsequence). For each integer m ≥ 1, the restrictions of (v_k^{1/m})_k to the compact ball B̄_m(0) are uniformly bounded and equi-Lipschitz, so by the Arzelà-Ascoli theorem every subsequence has a further subsequence converging uniformly on B̄_m(0). Choose inductively strictly increasing maps ψ_1 and ψ_m = ψ_{m−1} ∘ θ_m (θ_m strictly increasing) such that (v^{1/m}_{ψ_m(k)})_k converges uniformly on B̄_m(0), and put φ(k) := ψ_k(k). Then φ is strictly increasing, and for every m the sequence (φ(k))_{k≥m} is a subsequence of ψ_m, so (v^{1/m}_{φ(k)})_k converges uniformly on B̄_m(0).

Step 6 (Cauchy in L¹(B_R)). Fix an integer R ≥ 1 and ε > 0; choose an integer m ≥ R with 2C_{R+1}/m < ε/2 and put σ := 1/m ≤ 1. For k, l large (so that φ(k), φ(l) ≥ k_{R+1}), Steps 3 and 5 give
 ‖χ_{φ(k)} − χ_{φ(l)}‖_{L¹(B_R(0))} ≤ ‖χ_{φ(k)} − v^σ_{φ(k)}‖ + ‖v^σ_{φ(k)} − v^σ_{φ(l)}‖ + ‖v^σ_{φ(l)} − χ_{φ(l)}‖ ≤ 2σC_{R+1} + L^N(B_R(0)) sup_{B̄_m(0)} |v^σ_{φ(k)} − v^σ_{φ(l)}| < ε.

Step 7 (the limit is a characteristic function). By completeness of L¹(B_R(0)) for each integer R ≥ 1, and since the limits on nested balls agree a.e., there is u ∈ L¹_loc(ℝ^N) with χ_{φ(k)} → u in L¹(B_R(0)) for every R. A subsequence converges a.e. on each ball B_R(0) (diagonally, a.e. on ℝ^N), and χ_{φ(k)} takes values in {0, 1}, so u ∈ {0, 1} a.e. Fix a Borel representative ũ of u and set G := {y : ũ(y) = 1}. Then G is measurable and 1_G = u a.e.

Step 8 (conclusion). Let K be compact and choose an integer R ≥ 1 with K ⊆ B_R(0). Then L^N(K ∩ (F_{φ(k)} Δ G)) = ∫_K |χ_{φ(k)} − 1_G| ≤ ‖χ_{φ(k)} − u‖_{L¹(B_R(0))} → 0 as k → ∞. ∎

## Key steps

1. N = 0 by pigeonhole; otherwise the hypothesis applied to ±g gives |∫_{F_k} div g| ≤ C_R for k ≥ k_R.
2. Translation estimate ∫_{B_R}|χ_k(·+h) − χ_k| ≤ C_{R+1}|h| from ψ(z−h) − ψ(z) = −∫_0^1 div(ψ(·−th)h)(z)dt and L¹-duality.
3. Mollification error ‖φ_σ*χ_k − χ_k‖_{L¹(B_R)} ≤ σC_{R+1}; the φ_σ*χ_k ∈ [0,1] are equi-Lipschitz for fixed σ.
4. Arzelà-Ascoli on each B̄_m(0) and a diagonal argument give φ with φ_{1/m}*χ_{φ(k)} uniformly convergent on B̄_m(0) for every m.
5. (χ_{φ(k)}) is Cauchy in every L¹(B_R); the L¹_loc limit is {0,1}-valued, equal a.e. to 1_G with G measurable, so L^N(K ∩ (F_{φ(k)} Δ G)) → 0.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `grep -n 'def IsGaussGreenPair|def normalAverage|def reducedBoundary|def reducedNormal|def HasApproxTangentPlaneWithMultiplicity|def DeGiorgiTheorem|def ApproximateTangentCharacterization|def GaussGreenRepresentation' <snapshot>/project/GMT/Ch03/Contract.lean`
- `grep -rn -i 'de.?giorgi|reducedBoundary' <snapshot>/mathlib/Mathlib .lake/packages/simongmt/Poincare`
- `grep -n -i 'compactness|arzela' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/*.lean`
- `grep -n 'def blowUpMap|def HasApproximateTangentSpaceAt|theorem countablyRectifiable_iUnion' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'def euclideanDivergence|support_euclideanDivergence_subset|euclideanDivergence_eq_sum_inner|def IsLocallyBV|isLocallyBV_of_locallyL1_of_uniform_bound' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `grep -rn 'simon_theorem_3_3|def dimensionalUpperDensity|def dimensionalDensityQuotient|simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure|def realUnitBallVolume' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n 'WeakDerivativesZero|constancyMollifier' .lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `grep 'theorem ae_tendsto_rnDeriv|theorem ae_tendsto_average|theorem tendsto_filterAt|protected def vitaliFamily' <snapshot>/mathlib/Mathlib/MeasureTheory/Covering`
- `grep 'theorem Monotone.ae_differentiableAt|theorem eLpNorm_le_eLpNorm_fderiv_of_eq|theorem LipschitzWith.ae_differentiableAt|theorem tendsto_of_subseq_tendsto|theorem arzela_ascoli|theorem integral_Ioi_of_hasDerivAt_of_tendsto' <snapshot>/mathlib/Mathlib`
- `grep 'MonotoneOn.intervalIntegral_deriv_mem_uIcc|MonotoneOn.intervalIntegral_slope_le' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral`
- `grep 'StronglyMeasurable.integral_prod_right|measurable_measure_prodMk_left|measurableSet_exists_tendsto|StronglyMeasurable.limUnder' <snapshot>/mathlib/Mathlib`
- `grep 'euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_homothety_image|measurePreserving_euclideanHausdorffMeasure|theorem hausdorffMeasure_image|notation "μHE[' <snapshot>/mathlib/Mathlib`
- `grep 'withDensity_rnDeriv_eq|addHaar_image_homothety|theorem addHaar_smul|ae_convolution_tendsto_right_of_locallyIntegrable|finrank_orthogonal_span_singleton|LinearIsometryEquiv.measurePreserving|tendsto_measure_iUnion_atTop|Filter.Tendsto.limUnder_eq|HasCompactSupport.contDiff_convolution_left|OrthonormalBasis.volume_parallelepiped' <snapshot>/mathlib/Mathlib`
- `python3 -I (importlib of verifier/gmt-compare.py) contract_scope(Contract.lean, 'GMT.Ch03.main_theorem') -> NodeChallenge prefix; lake env lean /tmp/dg-decomp/challenges/Challenge_*.lean (10 files), /tmp/dg-decomp/Assembly.lean, /tmp/dg-decomp/Interfaces.lean`
- `python3 -I lean_name collision check against dag.json (73 nodes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Constructions/Polish/StronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/dg-decomp/Assembly.lean`
- `/tmp/dg-decomp/Interfaces.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). Neither Mathlib nor the pinned SimonGMT has a De Giorgi theorem, BV subsequence compactness, a Lipschitz Gauss–Green identity, density estimates for the reduced boundary, half-space rigidity, or measurability of the reduced boundary. SimonGMT FinitePerimeter.lean records only the definitions, and BV.lean states that subsequence extraction 'remains the compactness obligation'. These obligations therefore become children. Library facts located for the child proofs: Besicovitch differentiation (VitaliFamily.ae_tendsto_average, Besicovitch.ae_tendsto_rnDeriv, Besicovitch.tendsto_filterAt); the Gagliardo–Nirenberg–Sobolev inequality (eLpNorm_le_eLpNorm_fderiv_of_eq); Monotone.ae_differentiableAt and MonotoneOn.intervalIntegral_deriv_mem_uIcc; Rademacher; Arzelà–Ascoli; a.e. convergence of mollifiers; product measurability; μHE scaling and isometry invariance; SimonGMT simon_theorem_3_3 with simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure; countablyRectifiable_iUnion; WeakDerivativesZero. All ten child types elaborate in the exact NodeChallenge scope. The parent assembly and the sibling-interface checks compile against stubs, with propext, Classical.choice, Quot.sound and the stubs' sorryAx as the only axioms. No lean_name collides with dag.json.
