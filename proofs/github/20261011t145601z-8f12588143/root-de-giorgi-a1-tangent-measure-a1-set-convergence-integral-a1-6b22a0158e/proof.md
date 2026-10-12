# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.tangent_measure-a1`
- Child DAG node: `root.de_giorgi-a1.tangent_measure-a1.set_convergence_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the supplied parent proof, Step 3(i): 'By sibling blowup_halfspace with the compact set K := tsupport φ: |∫_{E_r} D_eφ − ∫_H D_eφ| ≤ sup|D_eφ|·L^N(K ∩ (E_r Δ H)) → 0'. It corresponds to parent Part 4(i): 'by 3f (L¹_loc convergence; D_Nφ is bounded with compact support)'. This is the L¹_loc step behind the last sentence of Simon Ch. 3, proof of Theorem 4.3, chapter-03.txt lines 739-746. Here the estimate is proved for an arbitrary family A(r), set H and continuous compactly supported g.

Notation. L^N = volume on ℝ^N, K := tsupport g, S_r := K ∩ (A(r) Δ H).

1. Constants. g is continuous with compact support, so there is M with |g(y)| ≤ M for all y (Continuous.bounded_above_of_compact_support); then M ≥ |g(0)| ≥ 0. Also g is L^N-integrable (Continuous.integrable_of_hasCompactSupport). K is compact, hence Borel with L^N(K) < ∞, and g(y) = 0 for y ∉ K (image_eq_zero_of_notMem_tsupport).

2. The difference as one integral. Fix r such that A(r) is null-measurable. Then ∫_{A(r)} g = ∫ 1_{A(r)} g and ∫_H g = ∫ 1_H g (integral_indicator₀). Both indicator functions are integrable (Integrable.indicator₀), so ∫_{A(r)} g − ∫_H g = ∫ (1_{A(r)} g − 1_H g) dL^N (integral_sub).

3. Pointwise domination. For every y, |1_{A(r)}(y)g(y) − 1_H(y)g(y)| ≤ M·1_{S_r}(y). Check by cases.
 - If y ∉ K, then g(y) = 0, so the left side is 0, and the right side is ≥ 0.
 - If y ∈ K and y lies in both or in neither of A(r) and H, the left side is 0.
 - If y ∈ K and y lies in exactly one of A(r) and H, then y ∈ S_r and the left side is |g(y)| ≤ M = M·1_{S_r}(y).

4. Bound. S_r is null-measurable: K is Borel, A(r) and H are null-measurable, and null-measurable sets are closed under symmetric difference and intersection. Also L^N(S_r) ≤ L^N(K) < ∞. So M·1_{S_r} is integrable with ∫ M·1_{S_r} = M·L^N(S_r), as a real number (integral_indicator₀, setIntegral_const). By step 3 and norm_integral_le_of_norm_le,
 |∫_{A(r)} g − ∫_H g| ≤ M·L^N(K ∩ (A(r) Δ H)).

5. Limit. By hypothesis, L^N(K ∩ (A(r) Δ H)) → 0 in [0, ∞] as r ↓ 0. Since the limit 0 is finite, the real values also tend to 0 (ENNReal.tendsto_toReal), so M·L^N(K ∩ (A(r) Δ H)) → 0. The bound of step 4 holds for every r in the 𝓝[>]0-eventual set where A(r) is null-measurable. By the squeeze theorem (squeeze_zero'), |∫_{A(r)} g − ∫_H g| → 0, i.e. ∫_{A(r)} g → ∫_H g as r ↓ 0 (tendsto_iff_norm_sub_tendsto_zero). ∎

## Key steps

1. |g| ≤ M and g is integrable. K = tsupport g is compact with L^N(K) < ∞, and g vanishes off K.
2. For null-measurable A(r): ∫_{A(r)} g − ∫_H g = ∫(1_{A(r)} − 1_H)g, and this integrand is bounded pointwise by M·1_{K ∩ (A(r) Δ H)}.
3. |∫_{A(r)} g − ∫_H g| ≤ M·L^N(K ∩ (A(r) Δ H)) → 0, eventually in 𝓝[>]0. Conclude by the squeeze theorem.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `rg -n '^def HasApproxTangentPlaneWithMultiplicity|^def IsGaussGreenPair|^def reducedBoundary|^noncomputable def reducedNormal|^noncomputable def normalAverage' <snapshot>/project/GMT/Ch03/Contract.lean`
- `rg -n 'theorem Submodule.measurePreserving_measurableEquivProd|theorem Isometry.map_euclideanHausdorffMeasure|theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_preimage' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'def toSpanUnitSingleton' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem integral_Ioi_of_hasDerivAt_of_tendsto' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `rg -n 'theorem exists_contDiff_tsupport_subset' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem dist_convolution_le' <snapshot>/mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem integral_prod_symm|theorem finrank_orthogonal_span_singleton' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem' -A 6 <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `sed -n 55,120p <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `sed -n 1,70p <snapshot>/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `sed -n 1,340p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'euclideanDivergence' -A 12 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean; grep -n 'def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `lake env lean /tmp/tm-decomp/Check1.lean ... Check6.lean (#check availability inside the import closure of GMT.Ch03.Submission)`
- `python3 -I /tmp/tm-decomp/mkchallenges.py (importlib of verifier/gmt-compare.py: child_modules + contract_scope for GMT.Ch03.main_theorem); lake env lean /tmp/tm-decomp/challenges/Challenge_*.lean`
- `lake env lean /tmp/tm-decomp/Assembly.lean; lake env lean /tmp/tm-decomp/Full.lean (#print axioms)`
- `lake env lean /tmp/tm-decomp/C1.lean C2.lean C3.lean C4.lean C5.lean (scratch child proofs)`
- `python3 -I lean_name collision check against dag.json (141 nodes); git grep 'deGiorgiTM_' over all 437 refs -- 'GMT/*.lean'; grep -rn over .lake/packages/simongmt/Poincare`
- `python3 -I: read lean_statement of nodes/root-de-giorgi-a1-{blowup-identity,density-estimates,blowup-halfspace}-a1/parent-child-handoff.json`
- `sed -n 570,760p book/chapter-03.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Module/Span.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/tm-decomp/challenges/Challenge_halfspace_flux.lean`
- `/tmp/tm-decomp/challenges/Challenge_set_convergence_integral.lean`
- `/tmp/tm-decomp/challenges/Challenge_excess_defect.lean`
- `/tmp/tm-decomp/challenges/Challenge_c1_to_cc_extension.lean`
- `/tmp/tm-decomp/Assembly.lean`
- `/tmp/tm-decomp/Full.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). HasApproxTangentPlaneWithMultiplicity (line 113), IsGaussGreenPair (153), normalAverage (161), reducedBoundary (168) and reducedNormal (173) were read there. Neither the snapshot Mathlib nor the pinned SimonGMT contains the half-space flux identity, the set-convergence integral lemma, the excess-defect estimate or the C¹→C_c extension. SimonGMT only provides euclideanDivergence (BV.lean) and blowUpMap (Rectifiable.lean). The snapshot Mathlib provides every tool the four child proofs use, inside the import closure of GMT.Ch03.Submission (checked with #check): Submodule.measurableEquivProd and measurePreserving_measurableEquivProd, Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_preimage, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, LinearIsometryEquiv.toSpanUnitSingleton, LinearIsometryEquiv.measurePreserving, integral_prod_symm, integral_Ioi_of_hasDerivAt_of_tendsto, exists_contDiff_tsupport_subset, dist_convolution_le, HasCompactSupport.contDiff_convolution_left, HasCompactSupport.convolution, Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero and Submodule.finrank_orthogonal_span_singleton. Some packaged lemmas are not in the closure: SmoothApprox.lean (UniformContinuous.exists_contDiff_dist_le), ContDiffBump.dist_normed_convolution_le and MeasureTheory.AEStronglyMeasurable.inner. So the c1_to_cc_extension proof builds the mollifier from exists_contDiff_tsupport_subset and dist_convolution_le, and excess_defect obtains measurability of ⟨e, ν⟩ as (continuous_const.inner continuous_id).comp_aestronglyMeasurable. The finiteness of Hⁿ on P ∩ B_R(0) is a 10-line inline argument, so the accepted cross-branch bf_plane_closedBall_measure_eq is not reused. All four child types elaborate in the exact comparator scope. The parent assembly and the full child proofs compile with only standard axioms plus the uncle stubs. No lean_name collides with dag.json or any ref.
