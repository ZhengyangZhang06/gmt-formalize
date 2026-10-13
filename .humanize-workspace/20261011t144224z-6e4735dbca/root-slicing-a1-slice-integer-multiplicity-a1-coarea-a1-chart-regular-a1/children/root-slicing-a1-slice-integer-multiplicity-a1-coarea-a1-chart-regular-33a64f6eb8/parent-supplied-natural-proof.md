# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.tonelli-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is the coordinates-and-Tonelli tool (TO) of the parent proof, used in step 5.

Notation: for t ∈ ℝ and v ∈ ℝ^m, [t,v] := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) and e(t,v) := [t,v], e : ℝ × ℝ^m → ℝ^{m+1}. All measures are volume (Lebesgue measure); volume on Fin k → ℝ is Measure.pi (fun _ => volume) (volume_pi).

1. (e is measure preserving from volume.prod volume to volume.) e is the composite of three measure-preserving maps:
(a) (t, v) ↦ (t, WithLp.ofLp v), ℝ × ℝ^m → ℝ × (Fin m → ℝ): MeasurePreserving.prod of MeasurePreserving.id and PiLp.volume_preserving_ofLp (Fin m) (= EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp);
(b) (t, x) ↦ Fin.cons t x, ℝ × (Fin m → ℝ) → (Fin (m+1) → ℝ): this is (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm, since Fin.insertNth 0 = Fin.cons (MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero), and it is measure preserving by (MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => volume) 0).symm (equivalently volume_preserving_piFinSuccAbove);
(c) WithLp.toLp : (Fin (m+1) → ℝ) → ℝ^{m+1}: PiLp.volume_preserving_toLp (Fin (m+1)).
EuclideanSpace.equiv is ofLp and its inverse is toLp, so the composite (c)∘(b)∘(a) is e, by funext and simp. Hence MeasurePreserving e (volume.prod volume) volume.
2. F ∘ e is measurable (F measurable, e measurable). By MeasurePreserving.lintegral_comp, ∫ F dL^{m+1} = ∫ (F ∘ e) d(L¹ ⊗ L^m).
3. Tonelli (lintegral_prod with (F ∘ e).aemeasurable; volume on ℝ^m is σ-finite): ∫ (F ∘ e) d(L¹ ⊗ L^m) = ∫_ℝ ∫_{ℝ^m} F([t,v]) dv dt. With step 2 this is the second conjunct.
4. Measurability (Measurable.lintegral_prod_right' applied to the measurable F ∘ e on ℝ × ℝ^m): t ↦ ∫_{ℝ^m} F([t,v]) dv is measurable. This is the first conjunct. ∎

## Key steps

1. e(t,v) = [t,v] factors as (id × ofLp), then (piFinSuccAbove … 0).symm = Fin.cons, then toLp; each is volume preserving.
2. MeasurePreserving.lintegral_comp transfers ∫ F dL^{m+1} to ∫ F∘e on ℝ × ℝ^m.
3. lintegral_prod (Tonelli) gives the iterated integral.
4. Measurable.lintegral_prod_right' gives measurability of t ↦ ∫ F([t,v]) dv.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/{parent-child-handoff.json,parent-supplied-plan.md} and nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `python3 scans of dag.json: coarea siblings and the glue type; statements of accepted lpf_raf_*, lpf_wtc_*, lpf_c1_* nodes; search for Fin.cons/toLp/piFinSuccAbove/toOpenPartialHomeomorph statements (no reusable Tonelli or IFT lemma); name-collision and identical-type scan of the six child types against all 508 nodes (only the intended reuse matches)`
- `read nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json (precedent for reusing accepted declarations by name) and nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/{parent-supplied-natural-proof.md,parent-child-handoff.json}`
- `git show 9fc44225b304fca8af9dead3256575ef03818d1e:GMT/Ch06/Submission.lean (accepted lpf_raf_chart_change_of_variables and its accepted prerequisites lpf_raf_local_lipschitz_area, lpf_raf_chart_preimage_null)`
- `grep -rn 'slicing_im_creg|slicing_im_coarea_chart_regular' local-references/197bdd4b88278494/project (no match)`
- `grep in pinned Mathlib: def normDet / normDet_* (Analysis/InnerProductSpace/NormDet.lean), volume_preserving_symm_measurableEquiv_toLp / PiLp.volume_preserving_ofLp / toLp (MeasureTheory/Measure/Haar/InnerProductSpace.lean), ContDiffAt.toOpenPartialHomeomorph (Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean), isOpen_image_symm_of_subset_target (Topology/OpenPartialHomeomorph/Basic.lean), lipschitzOnWith_of_nnnorm_fderiv_le (Analysis/Calculus/MeanValue.lean), μHE API (Geometry/Euclidean/Volume/Measure.lean)`
- `#check probes after import GMT.Ch06.Submission: lintegral_image_eq_lintegral_abs_det_fderiv_mul, measurePreserving_piFinSuccAbove, OpenPartialHomeomorph.contDiffAt_symm, HasStrictFDerivAt.toOpenPartialHomeomorph, MeasurableSet.image_of_continuousOn_injOn, TopologicalSpace.isOpen_iUnion_countable (present); LinearMap.normDet (not in the frozen import closure, hence Gram-determinant statements)`
- `python3: contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the six child types and the parent type`
- `lake env lean /tmp/chartreg-decomp/Assembly.lean (six child stubs, parent proved from them; sorryAx only from the stubs)`
- `lake env lean /tmp/chartreg-decomp/{jac,tonelli,straight,l2g}/Proof.lean (complete; propext, Classical.choice, Quot.sound) and /tmp/chartreg-decomp/box/Check.lean (box from the three sibling types declared as axioms)`
- `lake env lean /tmp/chartreg-decomp/integrated/Integrated.lean (accepted block of 9fc44225 + five child proofs + parent assembly; all standard axioms)`
- `python3 -I /tmp/chartreg-scripts/jac_check.py (exact rational check of the Jacobian identity: 1552 cases, 0 mismatches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/chartreg-decomp/Assembly.lean`
- `/tmp/chartreg-decomp/jac/Proof.lean`
- `/tmp/chartreg-decomp/tonelli/Proof.lean`
- `/tmp/chartreg-decomp/straight/Proof.lean`
- `/tmp/chartreg-decomp/l2g/Proof.lean`
- `/tmp/chartreg-decomp/box/Proof.lean`
- `/tmp/chartreg-decomp/box/Check.lean`
- `/tmp/chartreg-decomp/integrated/Integrated.lean`
- `/tmp/chartreg-scripts/jac_check.py`

The snapshot (project d8d46c95, Mathlib 25730c7c) has no slicing_im_creg_* or chart_regular declaration, and the frozen import closure lacks LinearMap.normDet, so child statements use Gram-determinant Jacobians. The DAG holds the comparator-accepted lpf_raf_chart_change_of_variables (the area formula for Lipschitz, antilipschitz charts), reused here by name with a byte-identical type. It has no Tonelli split along Fin.cons and no inverse-function straightening lemma, so those become new children. Mathlib supplies the inverse function theorem (ContDiffAt.toOpenPartialHomeomorph, contDiffAt_symm), change of variables (lintegral_image_eq_lintegral_abs_det_fderiv_mul), Lusin–Souslin, Lindelöf, piFinSuccAbove/PiLp volume-preservation and Cramer's rule. Lean checks in the exact comparator scope: all six child types elaborate, and the parent's type follows from them. The five new children are fully proved in scratch files. The integrated file (accepted block + children + parent assembly) uses only propext, Classical.choice and Quot.sound.
