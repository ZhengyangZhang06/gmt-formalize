# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.projection_null-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1.mass_off_compact-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, proof of Lemma 2.36, displays (1)–(3), run for Q_#T as in Remark 2.37(2); this is Steps 4–5 of the parent proof. The currents p_{α#}(T⌞ω_α) are realized by the functionals a ↦ T(ω_α·(a∘π_α)·Q^*dx^α), and Remark 2.35 is replaced by the sibling pullback_top_form_bound. Printed (3) only needs some constant, so the orthonormality of Step 1 of the parent proof is not needed: explicit finite constants are used instead.
Notation: I := I(n,P). For α ∈ I let e^Q_α := (Q^{−1}e_{α(0)}, …, Q^{−1}e_{α(m)}) and e_α := (e_{α(0)}, …, e_{α(m)}), let dx^α := wedgeCovectors n (fun i => x^{α(i)}), and let θ_α := Q^*dx^α = wedgeCovectors n (fun i => x^{α(i)}∘Q). |·| = covectorEuclideanNorm. The pairing ⟨φ, ξ(x)⟩ is ξ(x)(φ), and euclideanNVectorCoordinate (ξ x) β = ξ(x)(dx^β).

1. The linear maps π_α. For α ∈ I let π_α : ℝ^P → ℝⁿ be the continuous linear map x ↦ ((Qx)_{α(0)}, …, (Qx)_{α(m)}); it is the map in the hypothesis. For every i, y^i∘π_α = x^{α(i)}∘Q, so wedgeCovectors n (fun i => y^i∘π_α) = θ_α. The set F_α := π_α(K) is compact, and Lⁿ(F_α) = 0 by hypothesis.

2. Two expansions. By the sibling covector_rotated_expansion, every n-covector φ satisfies φ = Σ_{α∈I} φ(e^Q_α)·θ_α. With Q = identity, the same sibling gives φ = Σ_{β∈I} φ(e_β)·dx^β.

3. Coordinate bound. For every n-covector φ and β ∈ I, |φ(e_β)| ≤ |φ|. Indeed, the strictly increasing map β is one of the indices of the sum |φ|² = Σ_{J strictly increasing} φ(e_J)², and all terms are ≥ 0.

4. Constants. For α ∈ I put c_α := Σ_{β∈I} |dx^β(e^Q_α)| and c'_α := Σ_{β∈I} |θ_α(e_β)|. Put C := 1 + Σ_{α∈I} c_α·c'_α ≥ 1. These depend only on P, n and Q.
 (a) If |φ| ≤ 1 then |φ(e^Q_α)| ≤ c_α. By Step 2 with Q = id, φ(e^Q_α) = Σ_β φ(e_β)·dx^β(e^Q_α), and |φ(e_β)| ≤ |φ| ≤ 1 by Step 3.
 (b) For μ-a.e. x, |ξ(x)(θ_α)| ≤ c'_α for all α. By Step 2 with Q = id, θ_α = Σ_β θ_α(e_β)·dx^β, so ξ(x)(θ_α) = Σ_β θ_α(e_β)·ξ(x)(dx^β) by linearity of ξ(x). At every x with Σ_β ξ(x)(dx^β)² = 1, which holds for μ-a.e. x, each |ξ(x)(dx^β)| ≤ 1, so |ξ(x)(θ_α)| ≤ c'_α.

5. Reduction. Fix an open W ⊂⊂ U. Then W ⊆ closure W ⊆ U, and M_W(T) < ∞ and M_W(∂T) < ∞ because their sum is finite. W∖K is Borel. If μ(W∖K) = ∞, then C·μ(W∖K) = ∞ because C > 0, and there is nothing to prove. Assume D := μ(W∖K) < ∞. M_W(T) is the supremum of ofReal(T(ω)) over the admissible ω, i.e. those with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x. So it suffices to show T(ω) ≤ (Σ_α c_α c'_α)·D for each admissible ω; then ofReal(T(ω)) ≤ ofReal(C·D) = C·μ(W∖K).

6. Printed (1): decomposition. Fix an admissible ω and α ∈ I, and let ω_α(x) := ω(x)(e^Q_α).
 – Evaluation at the fixed tuple e^Q_α is a continuous linear map on covectors, so ω_α is C^∞.
 – ω_α(x) = 0 whenever ω(x) = 0, so tsupport ω_α ⊆ tsupport ω ⊆ W and ω_α has compact support.
 – |ω_α| ≤ c_α by Step 4(a).
 The form ζ_α(x) := ω_α(x)·θ_α is a test form in Dⁿ(U). By Step 2, ω(x) = Σ_α ω_α(x)·θ_α for every x, i.e. ω = Σ_α ζ_α. By linearity, T(ω) = Σ_α T(ζ_α).

7. Printed (2): the estimate |T(ζ_α)| ≤ c_α c'_α D. Apply the sibling pullback_top_form_bound to T and W (W ⊆ U, finite masses), f := ω_α and L := π_α; it yields a constant C_α. Let δ > 0. The sibling null_compact_cutoff, applied to the compact null set F_α ⊆ ℝⁿ, gives a C^∞ compactly supported b : ℝⁿ → [0, 1] with b = 1 on F_α and Lⁿ(tsupport b) ≤ δ. Define the test forms φ₁(x) := ω_α(x)b(π_αx)·θ_α and φ₂ := ζ_α − φ₁, so φ₂(x) = ω_α(x)(1 − b(π_αx))·θ_α. φ₁ is C^∞ with tsupport φ₁ ⊆ tsupport ω_α ⊆ W ⊆ U. Then T(ζ_α) = T(φ₁) + T(φ₂).
 (a) By Step 1, φ₁(x) = ω_α(x)b(π_αx)·wedgeCovectors n (fun i => y^i∘π_α). So pullback_top_form_bound with a := b and M := 1 gives |T(φ₁)| ≤ C_α·Lⁿ(tsupport b)^{1/n} ≤ max(C_α, 0)·δ^{1/n}.
 (b) By the representation, T(φ₂) = ∫ g dμ with g(x) := ξ(x)(φ₂(x)) = ω_α(x)(1 − b(π_αx))·ξ(x)(θ_α), and g is μ-integrable. For μ-a.e. x, |g(x)| ≤ c_α c'_α·1_{W∖K}(x):
  – if x ∉ W, then x ∉ tsupport ω_α, so ω_α(x) = 0;
  – if x ∈ K, then π_αx ∈ F_α, so b(π_αx) = 1;
  – otherwise |g(x)| ≤ |ω_α(x)|·|1 − b(π_αx)|·|ξ(x)(θ_α)| ≤ c_α·1·c'_α, by Step 6 and Step 4(b).
 Hence |T(φ₂)| ≤ ∫|g| dμ ≤ c_α c'_α·μ(W∖K) = c_α c'_α D.
 So |T(ζ_α)| ≤ max(C_α, 0)·δ^{1/n} + c_α c'_α D for every δ > 0. Letting δ ↓ 0, so that δ^{1/n} → 0, gives |T(ζ_α)| ≤ c_α c'_α D.

8. Printed (3). By Steps 6 and 7, T(ω) = Σ_α T(ζ_α) ≤ Σ_α |T(ζ_α)| ≤ (Σ_α c_α c'_α)·D. By Step 5, M_W(T) ≤ C·μ(W∖K) for every open W ⊂⊂ U, and C does not depend on W. If I = ∅ (P < n), the sum is empty, T(ω) = 0, and the claim still holds. ∎

## Key steps

1. π_α is linear with y^i∘π_α = x^{α(i)}∘Q, so its top form is θ_α = Q^*dx^α. F_α = π_α(K) is compact and Lⁿ-null.
2. covector_rotated_expansion gives ω = Σ_α ω_α·θ_α, where ω_α = ω(Q^{−1}e_α) is smooth, supported in W, and |ω_α| ≤ c_α. With Q = id it gives |ξ(θ_α)| ≤ c'_α μ-a.e.
3. Split ζ_α = ω_α·θ_α using a cutoff b from null_compact_cutoff. Then |T(ω_α(b∘π_α)θ_α)| ≤ C_α·δ^{1/n} by pullback_top_form_bound.
4. The remainder equals ∫ω_α(1 − b∘π_α)ξ(θ_α) dμ. Its integrand vanishes off W and on K, so it is at most c_αc'_α·μ(W∖K).
5. Let δ → 0, sum over α, and take the supremum over admissible ω: M_W(T) ≤ C·μ(W∖K).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c95; mathlib_commit 25730c7c)`
- `sha256sum GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (all ea3ee0dd…)`
- `rg -n 'def CompactlyContainedOpen|def IsMassMeasure|def IsMeasureRepresentation|abbrev Eucl|^theorem main_theorem|RectifiabilityTheorem' project/GMT/Ch06/Contract.lean`
- `rg -n 'theorem toSphere_apply_univ|theorem measurePreserving_homeomorphUnitSphereProd' Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `rg -n 'integral_fun_norm_addHaar|integrableOn_fun_norm_addHaar' Mathlib/MeasureTheory`
- `rg -n 'contDiff_convolution_right|hasFDerivAt_convolution_right' Mathlib/Analysis/Calculus/ContDiff/Convolution.lean Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem integral_Ioi_of_hasDerivAt_of_tendsto' Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `rg -n 'theorem tendsto_measure_thickening_of_isClosed' Mathlib/MeasureTheory`
- `rg -n 'MeasurableSet.exists_isClosed_lt_add|of_pseudoMetrizableSpace_of_isFiniteMeasure' Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'theorem sign_cycleRange|theorem cycleRange_symm_zero|theorem cycleRange_symm_succ' Mathlib/GroupTheory/Perm/Fin.lean`
- `rg -n 'def extDeriv' Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `rg -n 'IsCompact.exists_cthickening_subset_open' Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'exists_contMDiffMap_zero_one_of_isClosed' Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `timeout 100 rg -il 'newtonian potential|fundamental solution of (the )?laplace|riesz potential' Mathlib/Analysis Mathlib/MeasureTheory (no match)`
- `rg -n 'compact' simongmt Chapter02/BV.lean (module header: compactness remains a separate obligation)`
- `rg -n 'massOn|def massAdmissibleOn|def covectorEuclideanNorm|abbrev SimonMultiIndex|def euclideanNVectorCoordinate|def wedgeCovectors|abbrev TestFormOn|def exteriorDerivativeTestOn|theorem wedgeCovectors_apply_det|theorem covectorPullback_wedgeCovectors' simongmt Chapter06/{Mass,FormsDuality,Currents}.lean`
- `python3 verifier/lean_contract.py validate_lean_statement on the 9 lean_statements`
- `python3 verifier/gmt-compare.py contract_scope + child_modules (mode contract) for the 9 children, the frozen parent and the sibling`
- `lean -o build/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean (exit 0, 252 s)`
- `lean Chal3/AllStatements.lean (11 frozen statements under the comparator header; exit 0)`
- `lean ExactMatch3.lean (13 exact-type witnesses, #print axioms; exit 0)`
- `lean -o Scratch/{C1Rev,C2Sign,C2Full,C3Full,C4Glue,C5Full,C6Full,C7Glue,C8Full,C9Full,Assembly,JsonConsistency,EndToEnd}.lean, sequential fresh rebuild`
- `grep -nE 'sorry|admit|axiom|native_decide|implemented_by|@[extern|unsafe|opaque' Scratch/*.lean (no match)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (378 reserved names)`
- `python3 audit of nodes/root-rectifiability-a1-projection-null-a1/decomposition-v{1,2}.json and decomposition-audit-v{1,2}.json; dag.json status/children of all nodes`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `GMT/Ch06/Submission.lean`
- `GMT/Ch06/Contract.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-v1.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-v2.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-audit-v1.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch06/4c8bd8bda7ad4cc398208c0ce88a9677.log`
- `/tmp/rpn_v3_nmhI8O1x/src/Chal3/AllStatements.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/ExactMatch3.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C1Rev.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C2Sign.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C2Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C3Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C4Glue.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C5Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C6Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C7Glue.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C8Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/C9Full.lean`
- `/tmp/rpn_v3_nmhI8O1x/src/Scratch/Assembly.lean`
- `/tmp/rpn_v3_nmhI8O1x/logs/AllStatements.log`
- `/tmp/rpn_v3_nmhI8O1x/logs/ExactMatch3.log`
- `/tmp/rpn_v3_nmhI8O1x/logs/ExactMatch3_fresh.log`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract and Submission (sha256 ea3ee0dd…). IsMassMeasure T μ is μ(Uᶜ) = 0 ∧ μ(W) = M_W(T) for open W ⊂⊂ U, and IsMeasureRepresentation requires integrability and T(ω) = ∫ξ(x)(ω(x))dμ. These are exactly the facts the parent assembly uses.
The pinned Mathlib supplies every analytic tool the children cite:
 – polar coordinates: toSphere_apply_univ and measurePreserving_homeomorphUnitSphereProd (HaarToSphere.lean:87,142), integral_fun_norm_addHaar and integrableOn_fun_norm_addHaar (:296,273);
 – smoothness of convolutions: HasCompactSupport.contDiff_convolution_right and hasFDerivAt_convolution_right (ContDiff/Convolution.lean:420,61);
 – ray FTC: integral_Ioi_of_hasDerivAt_of_tendsto (IntegralEqImproper.lean:786);
 – shrinking neighbourhoods: tendsto_measure_thickening_of_isClosed (BorelSpace/Metric.lean:160), IsCompact.exists_cthickening_subset_open (Thickening.lean:426);
 – inner regularity: MeasurableSet.exists_isClosed_lt_add and WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure (Regular.lean:1031,1072);
 – signs and exterior derivative: Fin.sign_cycleRange, cycleRange_symm_zero/succ (Perm/Fin.lean:225,258,262) and extDeriv (DifferentialForm/Basic.lean:72);
 – smooth Urysohn functions: exists_contMDiffMap_zero_one_of_isClosed (PartitionOfUnity.lean:492).
SimonGMT supplies massOn, le_massOn, massAdmissibleOn, covectorEuclideanNorm (Chapter06/Mass.lean), wedgeCovectors, wedgeCovectors_apply_det, covectorPullback_wedgeCovectors, SimonMultiIndex, euclideanNVectorCoordinate (FormsDuality.lean), and TestFormOn and exteriorDerivativeTestOn (Currents.lean).
No match: there is no Newtonian or Riesz potential and no fundamental solution of the Laplacian in Mathlib/Analysis or Mathlib/MeasureTheory. Chapter02/BV.lean states that compactness remains a separate obligation. Hence the self-contained potential_estimate child replaces Remark 2.35.
Re-verification. The nine frozen types, the frozen parent type and the sibling type elaborate under the comparator's own header. A generated exact-match harness proves every child type and the parent implication with only propext, Classical.choice and Quot.sound.
Formalization aid for child workers (not part of any natural proof). Sorry-free Lean witnesses of each child's exact frozen type are in /tmp/rpn_v3_nmhI8O1x/src/Scratch (identical copies in /tmp/rpn_v2_Yfpb0s4j/src/Scratch); all build on GMT.Ch06.Submission:
 – potential_estimate: C1Rev.lean, theorem rpn_potential_estimate_review;
 – potential_form_derivative: C2Sign.lean, then C2Full.lean, theorem c2_full;
 – mass_bound_opnorm: C3Full.lean, c3_full;
 – pullback_top_form_bound: C4Glue.lean, c4_glue, taking the three dependency types as hypotheses;
 – covector_rotated_expansion: C5Full.lean, c5_full;
 – null_compact_cutoff: C6Full.lean, c6_full;
 – mass_off_compact: C7Glue.lean, c7_glue, from its three dependencies;
 – compact_null: C8Full.lean, c8_full;
 – borel_null: C9Full.lean, c9_full;
 – the selected node's glue: Assembly.lean, assembly.
JsonConsistency.lean and EndToEnd.lean restate the exact JSON types.
