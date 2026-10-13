# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

This is step 6 of the parent proof (cover and glue). The remainder W ∖ ⋃_k W_k is empty, so the gluing is done directly by countable additivity, which is the argument of the gluing lemma with empty remainder.

Notation: for a Borel S ⊆ ℝⁿ, (LP)(S) is the statement "t ↦ ∫_{Φ(S) ∩ f⁻¹{t}} g dν is Lebesgue-a.e.-measurable and ∫_ℝ ∫_{Φ(S) ∩ f⁻¹{t}} g dν dt = ∫_{Φ(S)} J g dμ". Integrals over a set are integrals against the restricted measure.

1. (The set E.) E := Ω ∩ Φ⁻¹(W) is Borel (Ω open, Φ continuous, W Borel). Φ(E) = W: ⊆ is clear, and each x ∈ W is Φ(w) with w ∈ Ω because W ⊆ Φ(Ω), so w ∈ E.
2. (Local sets for all points.) (LP)(∅) holds: every set integral over ∅ vanishes, so the slice function is the constant 0 (measurable) and both sides are 0. For w ∈ E, the hypothesis gives an open O(w) ∋ w with (LP)(S) for all Borel S ⊆ O(w) ∩ E. For w ∉ E put O(w) := ∅; then every S ⊆ O(w) ∩ E is ∅ and (LP)(S) holds. So every w ∈ ℝⁿ has an open O(w) with (w ∈ E ⇒ w ∈ O(w)) and (LP)(S) for all Borel S ⊆ O(w) ∩ E (choose).
3. (Lindelöf.) ℝⁿ is second countable, so TopologicalSpace.isOpen_iUnion_countable gives a countable T with ⋃_{w∈T} O(w) = ⋃_w O(w) ⊇ E. Choose e : ℕ → ℝⁿ with T ⊆ range e (Set.countable_iff_exists_subset_range). Put A_k := E ∩ O(e_k). These are Borel and ⋃_k A_k = E: if w ∈ E, then w ∈ O(w) ⊆ ⋃_{u∈T} O(u), so w ∈ O(e_k) for some k.
4. (Disjointification.) D_k := disjointed A k = A_k ∖ ⋃_{l<k} A_l. The D_k are Borel (MeasurableSet.disjointed), pairwise disjoint (disjoint_disjointed), and ⋃_k D_k = ⋃_k A_k = E (iUnion_disjointed). Also D_k ⊆ A_k ⊆ O(e_k) ∩ E, so (LP)(D_k) holds for every k by step 2.
5. (Images.) W_k := Φ(D_k) is Borel by Lusin–Souslin (MeasurableSet.image_of_continuousOn_injOn: D_k is Borel in the Polish space ℝⁿ, and Φ is continuous and injective on D_k ⊆ Ω). The W_k are pairwise disjoint: for i ≠ j, Φ(D_i) ∩ Φ(D_j) = Φ(D_i ∩ D_j) = ∅ by injectivity on Ω (InjOn.image_inter). ⋃_k W_k = Φ(⋃_k D_k) = Φ(E) = W.
6. (Slices.) For each t ∈ ℝ, W ∩ f⁻¹{t} = ⋃_k (W_k ∩ f⁻¹{t}). These sets are Borel (f measurable) and pairwise disjoint, so countable additivity of the set integral (lintegral_iUnion; no measurability of g is needed) gives ∫_{W ∩ f⁻¹{t}} g dν = Σ_k ∫_{W_k ∩ f⁻¹{t}} g dν.
7. (Measurability.) By (LP)(D_k), each t ↦ ∫_{W_k ∩ f⁻¹{t}} g dν is a.e.-measurable, so their sum, which by step 6 is the slice function of W, is a.e.-measurable (AEMeasurable.tsum). This is the first conjunct.
8. (Identity.) ∫_ℝ ∫_{W ∩ f⁻¹{t}} g dν dt = ∫_ℝ Σ_k ∫_{W_k ∩ f⁻¹{t}} g dν dt = Σ_k ∫_ℝ ∫_{W_k ∩ f⁻¹{t}} g dν dt (lintegral_tsum, valid for a.e.-measurable summands) = Σ_k ∫_{W_k} J g dμ (by (LP)(D_k)) = ∫_W J g dμ (lintegral_iUnion for the disjoint Borel W_k with ⋃_k W_k = W). This is the second conjunct. ∎

## Key steps

1. E := Ω ∩ Φ⁻¹W is Borel and Φ(E) = W.
2. Choose open O(w) for every w (∅ off E); Lindelöf gives countably many O(e_k) covering E.
3. Disjointify A_k := E ∩ O(e_k) into Borel D_k with ⋃D_k = E and the local property for each D_k.
4. W_k := Φ(D_k) are Borel (Lusin–Souslin), pairwise disjoint (injectivity) and cover W.
5. Countable additivity (lintegral_iUnion) for the slices and for W; AEMeasurable.tsum and lintegral_tsum give both conjuncts.

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
