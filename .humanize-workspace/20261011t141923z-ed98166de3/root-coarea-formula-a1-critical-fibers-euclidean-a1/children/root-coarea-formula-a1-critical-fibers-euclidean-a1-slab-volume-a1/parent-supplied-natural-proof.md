# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.critical_fibers_euclidean-a1`
- Child DAG node: `root.coarea_formula-a1.critical_fibers_euclidean-a1.slab_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent-supplied proof (the rotated-box bound Lᵐ(R_r) = 2ᵐ ω(r)(L_G+ω(r))^{m−1} rᵐ and the invariance of Lᵐ under translations and linear isometries), isolated as a measure-geometric lemma.
Notation: ℝᵐ = Rn m = EuclideanSpace ℝ (Fin m), Lᵐ = volume, ⟨·,·⟩ the Euclidean inner product, S := {v ∈ ℝᵐ : ‖v − c‖ ≤ R and |⟨e, v − c⟩| ≤ ε}.
1. m ≥ 1. If m = 0, then ℝ⁰ has only the zero vector, so e = 0 and ‖e‖ = 0 ≠ 1, contradicting ‖e‖ = 1. Hence m = m′ + 1 for some m′ ∈ ℕ, and m − 1 = m′ (Nat.add_sub_cancel).
2. An orthonormal basis through e. The family indexed by s := {0} ⊆ Fin m with constant value e is orthonormal, because its only vector has norm 1. Since finrank ℝ ℝᵐ = m = card (Fin m), Orthonormal.exists_orthonormalBasis_extension_of_card_eq (with v := fun _ ↦ e and s := {0}) gives an orthonormal basis b = (b_i)_{i ∈ Fin m} of ℝᵐ with b_0 = e.
3. Measure-preserving coordinates. Define Φ : ℝᵐ → EuclideanSpace ℝ (Fin m) by Φ(v) := b.repr (v − c). For every i, Φ(v)_i = ⟨b_i, v − c⟩ (OrthonormalBasis.repr_apply_apply); in particular Φ(v)_0 = ⟨e, v − c⟩. Also ‖Φ(v)‖ = ‖v − c‖, since b.repr is a linear isometry equivalence. The translation v ↦ v − c preserves Lebesgue measure (measurePreserving_sub_right), and b.repr preserves Lebesgue measure (OrthonormalBasis.measurePreserving_repr). Hence Φ is measure preserving, and Lᵐ(Φ⁻¹(B)) = Lᵐ(B) for every measurable B.
4. A box containing Φ(S). Let a : Fin m → ℝ with a_0 := ε and a_i := R for i ≠ 0. Let B := {w ∈ EuclideanSpace ℝ (Fin m) : −a_i ≤ w_i ≤ a_i for all i}, i.e. the preimage of the closed box Icc(−a, a) ⊆ (Fin m → ℝ) under the coordinate map WithLp.ofLp. B is closed, hence measurable. Let v ∈ S and w := Φ(v). Then |w_0| = |⟨e, v − c⟩| ≤ ε = a_0. For i ≠ 0, a coordinate of a Euclidean vector is bounded by its norm (PiLp.norm_apply_le), so |w_i| ≤ ‖w‖ = ‖v − c‖ ≤ R = a_i. Hence S ⊆ Φ⁻¹(B).
5. Volume of the box. The coordinate map WithLp.ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ) is measure preserving (PiLp.volume_preserving_ofLp). Therefore Lᵐ(B) = vol(Icc(−a, a)) = ∏_i ofReal(a_i − (−a_i)) = ∏_i ofReal(2a_i) (Real.volume_Icc_pi). Splitting off the index 0 (Fin.prod_univ_succ) leaves m′ factors, each equal to ofReal(2R). So the product is ofReal(2ε)·ofReal(2R)^{m′} = ofReal(2ε·(2R)^{m′}), using ENNReal.ofReal_pow, ENNReal.ofReal_mul, ε ≥ 0 and R ≥ 0.
6. Conclusion. By monotonicity of measure and steps 3–5, Lᵐ(S) ≤ Lᵐ(Φ⁻¹(B)) = Lᵐ(B) = ofReal(2ε(2R)^{m′}) = ofReal(2ε(2R)^{m−1}).

## Key steps

1. m ≥ 1 because ‖e‖ = 1; write m = m′ + 1.
2. Extend e to an orthonormal basis b of ℝᵐ with b_0 = e (Orthonormal.exists_orthonormalBasis_extension_of_card_eq).
3. Φ(v) := b.repr(v − c) is measure preserving and maps S into the box {w : |w_i| ≤ a_i} with a_0 = ε and a_i = R for i ≠ 0.
4. The box has volume ∏ 2a_i = 2ε(2R)^{m−1} (PiLp.volume_preserving_ofLp, Real.volume_Icc_pi, Fin.prod_univ_succ).

## Reference use

### local-project

Queries:
- `rg -n 'theorem .*[Ss]ard' mathlib/Mathlib (no match)`
- `rg -il 'coarea' mathlib/Mathlib (no match)`
- `rg -n 'theorem hausdorffMeasure_le_liminf_sum|theorem hausdorffMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def|notation "μHE' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'def maximalSeparatedSet|lemma isCover_maximalSeparatedSet|def packingNumber' mathlib/Mathlib/Topology/MetricSpace/CoveringNumbers.lean`
- `rg -n 'def IsCover|def IsSeparated' mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'exists_orthonormalBasis_extension' mathlib/Mathlib`
- `rg -n 'theorem OrthonormalBasis.measurePreserving_repr|theorem PiLp.volume_preserving_ofLp' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `rg -n 'theorem volume_Icc_pi|theorem addHaar_ball_of_pos|theorem addHaar_ball_center' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue`
- `rg -n "theorem norm_image_sub_le_of_norm_fderiv_le'?" mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `rg -n 'theorem orthogonal_eq_bot_iff|theorem mem_orthogonal' mathlib/Mathlib/Analysis/InnerProductSpace`
- `rg -n 'exists_cthickening_subset_open|IsCompact.cthickening|mem_cthickening_of_dist_le|self_subset_cthickening' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `rg -n 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen|theorem ContDiffOn.differentiableOn' mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `rg -n 'IsCompact.uniformContinuousOn_of_continuous|theorem uniformContinuousOn_iff |exists_bound_of_continuousOn' mathlib/Mathlib/Topology mathlib/Mathlib/Analysis/Normed`
- `rg -n 'theorem lintegral_liminf_le|theorem lintegral_finsetSum|theorem Measurable.liminf|theorem measure_toMeasurable|theorem subset_toMeasurable|theorem lintegral_indicator_one' mathlib/Mathlib/MeasureTheory`
- `rg -n 'theorem isOpen_iUnion_countable|theorem ae_ball_iff|theorem measure_biUnion_null_iff' mathlib/Mathlib`
- `rg -n 'theorem ediam_le_of_forall_dist_le|def ediam' mathlib/Mathlib/Topology`
- `rg -n 'abbrev Rn|def coareaJacobian|def CoareaFormula|def C1Sard' project/GMT/Ch02/Contract.lean`
- `grep -n '^theorem' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `sed -n 1405,1530p book/chapter-02.txt (Simon §6: no printed proof of the critical-fibre statement)`
- `python3 -I gen_checks.py (gmt-compare.py child_modules contract scope + lean_contract.validate_lean_statement) on the five statements; lean NodeChallenge_00..04.lean against a scratch olean of GMT.Ch02.Submission`
- `lean Assembly1.lean / Assembly2.lean / LeafC1.lean / LeafC3.lean / LeafC4.lean / FullFinal.lean (five children proved verbatim; check_parent : frozen type; #print axioms)`
- `python3 -I: list lean_name of all 52 nodes in dag.json and test the five proposed names`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/CoveringNumbers.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Cover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/MetricSeparated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1/parent-child-handoff.json`
- `/tmp/critfib-decomp/checks_final/NodeChallenge_00.lean`
- `/tmp/critfib-decomp/checks_final/NodeChallenge_04.lean`
- `/tmp/critfib-decomp/assembly/FullFinal.lean`

The snapshot contains no Sard or co-area theorem: both rg searches return no match. The project defines Rn (Contract.lean l.48), coareaJacobian, CoareaFormula and C1Sard, but no Submission lemmas. SimonGMT's AreaCritical.area_image_eq_zero_of_critical covers only the equal-dimension critical-image case (the k = 0 analogue), so it is not reused.

The snapshot's Mathlib supplies every tool the children need:
- Measure.hausdorffMeasure_le_liminf_sum (Hausdorff.lean l.563) and euclideanHausdorffMeasure_def (Measure.lean l.74);
- maximalSeparatedSet, isCover_maximalSeparatedSet and packingNumber (CoveringNumbers.lean), an alternative route for child 3;
- Orthonormal.exists_orthonormalBasis_extension_of_card_eq (PiL2.lean l.1044);
- OrthonormalBasis.measurePreserving_repr (l.111) and PiLp.volume_preserving_ofLp (l.134) in Haar/InnerProductSpace.lean;
- Real.volume_Icc_pi (Lebesgue/Basic.lean l.235) and Measure.addHaar_ball_of_pos (EqHaar.lean l.445);
- Convex.norm_image_sub_le_of_norm_fderiv_le' (MeanValue.lean l.549) and Submodule.orthogonal_eq_bot_iff (Projection/Submodule.lean l.122);
- IsCompact.exists_cthickening_subset_open (l.426) and IsCompact.cthickening (l.283) in Thickening.lean;
- ContDiffOn.continuousOn_fderiv_of_isOpen and ContDiffOn.differentiableOn (ContDiff/Defs.lean), and IsCompact.uniformContinuousOn_of_continuous (HeineCantor.lean);
- lintegral_liminf_le, lintegral_finsetSum, Measurable.liminf, measure_toMeasurable and ediam_le_of_forall_dist_le;
- isOpen_iUnion_countable, ae_ball_iff and measure_biUnion_null_iff.

All five statements pass validate_lean_statement, and their NodeChallenge modules compile in the replayed contract scope. The scratch FullFinal.lean proves all five children verbatim and the selected frozen type, with only propext, Classical.choice and Quot.sound. None of the five lean_names is reserved in dag.json (52 nodes checked).
