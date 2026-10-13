# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.chart_data-a1.c1_cover-a1.critical_image_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ = Eucl k = EuclideanSpace ℝ (Fin k) with Euclidean norm |·|. Hⁿ = μHE[n], Lⁿ = volume on ℝⁿ, B(0, m) is the open ball of radius m about 0, and Df(w) := fderiv ℝ f w. All measures are evaluated on arbitrary sets (outer measures).

Hypotheses: n, P ∈ ℕ, L ∈ ℝ≥0, and f : ℝⁿ → ℝ^P is L-Lipschitz. Let C := {w ∈ ℝⁿ : f is differentiable at w and Df(w) is not injective}. Goal: Hⁿ(f(C)) = 0.

1. (Reduction to bounded pieces.)
   - For each w ∈ ℝⁿ there is m ∈ ℕ with |w| < m (exists_nat_gt). Hence f(C) ⊆ ⋃_{m∈ℕ} f(C ∩ B(0, m)).
   - By monotonicity and countable subadditivity (measure_iUnion_null), it suffices to show Hⁿ(f(C ∩ B(0, m))) = 0 for every m ∈ ℕ.
   - Fix m. Put s := C ∩ B(0, m) and V := Lⁿ(B(0, m)). V is finite (measure_ball_lt_top).

2. (The estimate for a fixed t.) Let t ∈ ℝ≥0 with 0 < t ≤ 1. We show Hⁿ(f(s)) ≤ (L + 1)ⁿ · V · t.
   (a) If s = ∅, then f(s) = ∅ and Hⁿ(f(s)) = 0. Assume s ≠ ∅.
   (b) Every x ∈ s lies in C, so f is differentiable at x. Hence f has Fréchet derivative Df(x) at x, and in particular within s at x.
       Apply Mathlib's exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255) to f, s, f′ := Df and the constant function r ≡ t². Here r ≠ 0 because t > 0. It gives sets T_i ⊆ ℝⁿ and continuous linear maps A_i : ℝⁿ → ℝ^P (i ∈ ℕ) such that:
       – the T_i are pairwise disjoint and measurable, and s ⊆ ⋃_i T_i;
       – ApproximatesLinearOn f A_i (s ∩ T_i) (t²) for each i;
       – since s is nonempty, for each i there is y_i ∈ s with A_i = Df(y_i).
   (c) Fix i.
       - Since y_i ∈ s ⊆ C, A_i = Df(y_i) is not injective.
       - ‖A_i‖ ≤ L, since the derivative of an L-Lipschitz map has operator norm at most L (norm_fderiv_le_of_lipschitz).
       - Apply the sibling singular_compression (Submission.slicing_im_st_cd_c1c_singular_compression) with f, A := A_i, S := s ∩ T_i and t. Its hypotheses hold: 0 < t ≤ 1, A_i is not injective, and ApproximatesLinearOn f A_i (s ∩ T_i) (t²). It gives Hⁿ(f(s ∩ T_i)) ≤ (‖A_i‖ + t)ⁿ · (t · Lⁿ(s ∩ T_i)).
       - We have ‖A_i‖ + t ≤ L + 1 and s ∩ T_i ⊆ B(0, m) ∩ T_i. By monotonicity, Hⁿ(f(s ∩ T_i)) ≤ (L + 1)ⁿ · t · Lⁿ(B(0, m) ∩ T_i).
   (d) Since s ⊆ ⋃_i T_i, f(s) ⊆ ⋃_i f(s ∩ T_i). We use countable subadditivity, (c), and countable additivity of Lⁿ on the pairwise disjoint measurable sets B(0, m) ∩ T_i:
       Hⁿ(f(s)) ≤ Σ_i Hⁿ(f(s ∩ T_i))
               ≤ (L + 1)ⁿ · t · Σ_i Lⁿ(B(0, m) ∩ T_i)
               = (L + 1)ⁿ · t · Lⁿ(⋃_i (B(0, m) ∩ T_i))
               ≤ (L + 1)ⁿ · t · V.

3. (Letting t → 0.)
   - For k ∈ ℕ, apply step 2 with t := (k + 1)⁻¹ ∈ (0, 1]. This gives Hⁿ(f(s)) ≤ (L + 1)ⁿ · V · (k + 1)⁻¹ for every k.
   - In [0, ∞], (k + 1)⁻¹ → 0 (ENNReal.tendsto_inv_nat_nhds_zero composed with k ↦ k + 1), and (L + 1)ⁿ · V < ∞. So (L + 1)ⁿ · V · (k + 1)⁻¹ → 0 (ENNReal.Tendsto.const_mul).
   - A constant bounded above by every term of a sequence tending to 0 is ≤ 0 (ge_of_tendsto'). Hence Hⁿ(f(s)) = 0.

4. (Conclusion.) By step 3, Hⁿ(f(C ∩ B(0, m))) = 0 for every m ∈ ℕ. By step 1, Hⁿ(f(C)) = 0. ∎

Remark. For n = 0, C = ∅, because every linear map on ℝ⁰ = {0} is injective. The argument covers this case without change.

## Key steps

1. Reduce to s = C ∩ B(0, m) by countable subadditivity; V = Lⁿ(B(0, m)) < ∞.
2. Partition s into countably many disjoint measurable pieces s ∩ T_i on which f is t²-close to A_i = Df(y_i), y_i ∈ C (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt).
3. A_i is not injective and ‖A_i‖ ≤ L, so singular_compression gives Hⁿ(f(s ∩ T_i)) ≤ (L + 1)ⁿ·t·Lⁿ(B(0, m) ∩ T_i).
4. Summing gives Hⁿ(f(s)) ≤ (L + 1)ⁿ·V·t for all t ∈ (0, 1]; t = 1/(k + 1) → 0 gives Hⁿ(f(s)) = 0, hence Hⁿ(f(C)) = 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch06/Contract.lean with workspace Contract.lean and Submission.lean (identical)`
- `rg -n 'countably_rectifiable_c1_cover|c1_cover|lipschitz_c1_immersion|area_image_compl_regularSet_eq_zero|areaRegularSet' over the snapshot (no match: the snapshot project is the frozen contract only)`
- `rg snapshot mathlib: '^def ApproximatesLinearOn', 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt', 'theorem det_one_add_replicateCol_mul_replicateRow', 'theorem addHaar_image_continuousLinearMap', 'theorem norm_fderiv_le_of_lipschitz', 'theorem LipschitzWith.ae_differentiableAt', 'theorem lipschitzOnWith_of_nnnorm_fderiv_le', 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume', 'tendsto_inv_nat_nhds_zero', '^def eqv', 'theorem finrank_euclideanSpace_fin', 'theorem measure_union_null', 'theorem ae_iff', 'protected lemma _root_.LipschitzWith.locallyLipschitz'`
- `rg SimonGMT (lake-packages-25730c7c/simongmt): 'def areaRegularSet', 'theorem area_image_compl_regularSet_eq_zero', 'theorem area_image_criticalSet_eq_zero', 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn', 'def CountablyRectifiable'; python import-closure scan: AreaLipschitz/AreaCritical not reachable from the 8 frozen contract imports, Chapter02.Lipschitz reachable`
- `python3 -I over dag.json: lean_statement/status/children/candidate_commit of lpf_lipschitz_c1_immersion_pieces (accepted 682c558), lpf_countably_rectifiable_c1_cover (accepted 4f96ac67, children [], type byte-identical to this node), chart_data and this node; scan for critical-image/ApproximatesLinearOn types and name collisions (none)`
- `git show 4f96ac67:GMT/Ch06/Submission.lean (inline hpiece/hcrit Sard argument), 682c558 (sibling declaration), f9637977 (AreaDomain import added by a non-leaf composition); grep/git log -S for slicing_im_st_cd_c1c_* (no match)`
- `read runtime _recursive_lean/leaf_verification.py check_source_delta, parent_verification.py check_parent_git_delta, runtime.py _leaf_author_task/_overlay_accepted_children/_decompose/_existing_lean_name_problem/_reference_use_problem, prompts.py DECOMPOSE and DECOMPOSITION_AUDIT`
- `lake env lean /tmp/c1cover-nosplit-kFnB5j/{Challenge.lean, Cond.lean, Challenge_A.lean, Challenge_B.lean, Split3.lean} (all exit 0; axioms propext, Classical.choice, Quot.sound); python3 -I /tmp/c1cover-nosplit-scripts/delta_check.py (both children ACCEPTED, import control REJECTED)`
- `two independent reviewer subagents: first rejected no-split (leaf cannot add the AreaLipschitz import), second audited this split: ACCEPT, no text fixes`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ApproximatesLinearOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/Denumerable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-fbaf41bab5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-chart-d-fbaf41bab5/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/parent_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/c1cover-nosplit-kFnB5j/Challenge_A.lean`
- `/tmp/c1cover-nosplit-kFnB5j/Challenge_B.lean`
- `/tmp/c1cover-nosplit-kFnB5j/Split3.lean`
- `/tmp/c1cover-nosplit-kFnB5j/Cond.lean`
- `/tmp/c1cover-nosplit-scripts/delta_check.py`

Snapshot (project d8d46c95, Mathlib 25730c7c): the frozen Ch06 contract is byte-identical to the workspace Contract.lean and Submission.lean. No snapshot file contains a C¹-cover, critical-image or compression lemma.

Mathlib supplies every tool the children need:
- ApproximatesLinearOn (ApproximatesLinearOn.lean:71);
- exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (MeasureTheory/Function/Jacobian.lean:255);
- Matrix.det_one_add_replicateCol_mul_replicateRow (SchurComplement.lean:417);
- Measure.addHaar_image_continuousLinearMap (EqHaar.lean:310);
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
- LipschitzWith.ae_differentiableAt (Rademacher.lean:385);
- Convex.lipschitzOnWith_of_nnnorm_fderiv_le (MeanValue.lean:507);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
- ENNReal.tendsto_inv_nat_nhds_zero (ENNReal/Lemmas.lean:486);
- Denumerable.eqv (Basic/Denumerable.lean:71);
- measure_union_null (OuterMeasure/Basic.lean:128);
- ae_iff (OuterMeasure/AE.lean:134).

SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216) is in the frozen import closure. area_image_compl_regularSet_eq_zero and area_image_criticalSet_eq_zero (AreaLipschitz.lean:59, AreaCritical.lean:185) are not, and leaf candidates cannot add imports. Hence the split: two fresh children whose types elaborate in the exact comparator scope.

Both children and the parent composition compile under the frozen imports with standard axioms. The composition takes the accepted sibling lpf_lipschitz_c1_immersion_pieces (682c558) as its type.

The accepted lpf_countably_rectifiable_c1_cover (4f96ac67) has the parent's exact type. It is not reusable as a child (it would restate the parent) and is not in this node's base. Its stale 'not accepted' status in the handoff is corrected here.
