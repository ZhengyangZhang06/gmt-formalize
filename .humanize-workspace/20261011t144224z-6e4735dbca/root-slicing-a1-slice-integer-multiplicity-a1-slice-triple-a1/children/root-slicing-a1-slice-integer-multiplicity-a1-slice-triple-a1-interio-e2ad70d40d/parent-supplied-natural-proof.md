# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.interior_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P with inner product ⟨·,·⟩ and norm |·|. Λ^k := Covector (Eucl P) k is the space of continuous alternating k-forms, and a k-vector is a continuous linear functional on Λ^k. simpleNVector σ is the k-vector α ↦ α(σ) (simpleNVector_apply). For v ∈ ℝ^P, ι(v) := (alternatizeUncurryFinCLM ℝ ℝ^P ℝ) ∘L (smulRightL ℝ ℝ^P Λ^m (innerSL ℝ v)). By `rfl`, ι(v)α = alternatizeUncurryFin((innerSL ℝ v).smulRight α), and by alternatizeUncurryFin_apply, (ι(v)α)(σ) = Σ_{i : Fin (m+1)} (−1)^i ⟨v, σ_i⟩ α(removeNth i σ). This is Step 10 of the parent proof (Simon Ch. 6, 4.3); the frame-sign fact (Fact F of the parent) is the sibling frame_sign (fiw_ims_frame_sign).
1. (The subspace S.) Let T := span(range τ). Since τ is orthonormal it is linearly independent, so dim T = m + 1. Since g ∈ T and g ≠ 0, ν := |g|⁻¹g is a unit vector in T. Let S := T ⊓ (ℝ∙g)ᗮ = {v ∈ T : ⟨g, v⟩ = 0} (Submodule.mem_orthogonal_singleton_iff_inner_right). The linear functional v ↦ ⟨g, v⟩ on T is nonzero, since ⟨g, g⟩ = |g|² ≠ 0, and S is its kernel. By rank–nullity, dim S = m.
2. (Orthonormal basis τ′ of S.) Choose an orthonormal basis of S indexed by Fin m (stdOrthonormalBasis ℝ S reindexed along dim S = m), and let τ′_i ∈ ℝ^P be its vectors. The inner product of S is the restriction of that of ℝ^P, so τ′ : Fin m → ℝ^P is orthonormal, and span(range τ′) = S. This gives the first two conclusions.
3. (Adapted frame.) Let σ := Fin.snoc τ′ ν : Fin (m+1) → ℝ^P, i.e. σ = (τ′_0, …, τ′_{m−1}, ν). σ is orthonormal: τ′ is orthonormal, |ν| = 1, and ⟨τ′_i, ν⟩ = |g|⁻¹⟨τ′_i, g⟩ = 0 since τ′_i ∈ S. The m + 1 vectors of σ lie in T (S ⊆ T, ν ∈ T) and are linearly independent, and dim T = m + 1, so span(range σ) = T = span(range τ).
4. (Frame sign.) By frame_sign (fiw_ims_frame_sign) applied to τ and σ, simpleNVector σ = simpleNVector τ or simpleNVector σ = −simpleNVector τ. Together with w = ±simpleNVector τ, this gives w = ε·simpleNVector σ for some ε ∈ {1, −1}.
5. (Evaluation.) Let α ∈ Λ^m. In (ι(ν)α)(σ) = Σ_{i=0}^{m} (−1)^i ⟨ν, σ_i⟩ α(removeNth i σ):
   - for i = castSucc k (k < m), σ_i = τ′_k and ⟨ν, τ′_k⟩ = 0;
   - for i = last m, σ_i = ν, ⟨ν, ν⟩ = 1, and removeNth (last m) σ = init σ = τ′ (Fin.removeNth_last, Fin.init_snoc).
   Splitting the sum with Fin.sum_univ_castSucc gives (ι(ν)α)(σ) = (−1)^m α(τ′).
6. (Conclusion.) For every α ∈ Λ^m, (w ∘L ι(ν))(α) = ε·simpleNVector σ (ι(ν)α) = ε·(ι(ν)α)(σ) = ε(−1)^m α(τ′) = ε(−1)^m·simpleNVector τ′ (α). By extensionality of continuous linear maps, w ∘L ι(ν) = ε(−1)^m·simpleNVector τ′ with ε(−1)^m ∈ {1, −1}, so w ∘L ι(ν) is simpleNVector τ′ or −simpleNVector τ′.
   For m = 0, τ′ is the empty family, S = {0}, σ = (ν), simpleNVector τ′ is evaluation at the empty tuple, and the same computation applies. ∎

## Key steps

1. S := span τ ∩ g^⊥ is the kernel of the nonzero functional ⟨g, ·⟩ on the (m+1)-dimensional span τ, so dim S = m; take an orthonormal basis τ′ of S indexed by Fin m.
2. σ := (τ′, ν) with ν = g/|g| is an orthonormal basis of span τ, so frame_sign gives w = ±simpleNVector σ.
3. alternatizeUncurryFin_apply: (ν♭∧α)(σ) = (−1)^m α(τ′), since ⟨ν, τ′_k⟩ = 0, ⟨ν, ν⟩ = 1 and removeNth (last m) σ = τ′.
4. By extensionality, w ∘ ι(ν) = ±simpleNVector τ′.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical); read IsRectifiableTriple in the contract`
- `read nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/{parent-child-handoff.json,parent-supplied-natural-proof.md,parent-supplied-plan.md}`
- `python3 over dag.json: lean_name/status/lean_statement of all 361 nodes (slicing_im_coarea frozen type; accepted fiw_ims_frame_sign, lpf_c1_local_antilipschitz, lpf_wtc_*; speculative-ready lpf_weighted_tangent_on_c1_chart, lpf_countably_rectifiable_c1_cover, lpf_c1_approximation_real)`
- `grep -c 'slicing_im_st_' dag.json DAG.md issue-workers.json; grep -rl 'slicing_im_st_' nodes/ (no match)`
- `read decomposition-v1.json of root-slicing-a1-slice-integer-multiplicity-a1, root-lipschitz-pushforward-im-a1-chart-chain-rule-a1, root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1 (uncle-results-as-hypotheses and reuse-child conventions)`
- `read parent-supplied-natural-proof.md of lpf weighted_tangent_on_c1_chart, countably_rectifiable_c1_cover, lipschitz_c1_immersion_pieces, c1_local_antilipschitz and fiw_ims frame_sign`
- `grep SimonGMT: def CountablyRectifiable, countablyRectifiable_of_measure_zero/_iUnion/.mono, blowUpMap, HasWeightedApproximateTangentSpaceAt(.unique), simpleNVector(_apply), area_image_compl_regularSet_eq_zero, simon_theorem_3_6, euclideanHausdorffMeasure_image_le_of_lipschitzOn, injective_area_formula_lipschitzOn, rademacher_ae_differentiableAt`
- `grep Mathlib snapshot: alternatizeUncurryFin_apply/alternatizeUncurryFinCLM, LipschitzOnWith.extend_finite_dimension/extend_real, ContDiffAt.implicitFunction (+ eventually_apply_eq_iff_implicitFunction, contDiffAt_implicitFunction, implicitFunction_apply_self), restrict_apply₀', le_restrict_apply, ae_restrict_of_ae_restrict_of_subset, ae_restrict_union_iff, exists_measurable_subset_ae_eq, lintegral_eq_zero_iff', ae_lt_top', lintegral_indicator_one, aestronglyMeasurable_iUnion_iff, MeasurableSet.image_of_continuousOn_injOn, isOpen_iUnion_countable, mem_orthogonal_singleton_iff_inner_right, Fin.removeNth_last, Fin.init_snoc, euclideanHausdorffMeasure_zero, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hausdorffMeasure_image_le`
- `sed book/chapter-06.txt 1145-1240 (4.1-4.4); chapter-03.txt 1-470 (1.1-2.10); chapter-02.txt 160-190 and 895-975 (1.5, 1.6, 4.5-4.10)`
- `python3 -I scripts/gen.py (contract_scope from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all child strings)`
- `lean Stmts.lean / Final.lean (8 child types + parent + coarea + instance sanity checks; 0 errors)`
- `lean Assembly.lean (parent from coarea + ae_transfer + measure_fields + slice_geometry + interior_product; axioms propext, Classical.choice, Quot.sound)`
- `lean K6.lean (slice_geometry from its 5 sibling types; standard axioms)`
- `lean ProbeAE.lean (full proof of the ae_transfer type), SignCheck.lean (interior-product sign computation), Probe7.lean (strong measurability of ξ̃_t via a Lipschitz bound on ι)`
- `independent reviewer subagent: re-ran all Lean files, verdict ACCEPT-WITH-FIXES (fixes applied)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-frame-sign-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ImplicitContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/st-split-19917/Stmts.lean`
- `/tmp/st-split-19917/Final.lean`
- `/tmp/st-split-19917/Assembly.lean`
- `/tmp/st-split-19917/K6.lean`
- `/tmp/st-split-19917/ProbeAE.lean`
- `/tmp/st-split-19917/SignCheck.lean`
- `/tmp/st-split-19917/Probe7.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Submission is byte-identical to it. Child types may therefore use only contract, SimonGMT and Mathlib names. SimonGMT provides CountablyRectifiable with mono/iUnion/null lemmas, blowUpMap, HasWeightedApproximateTangentSpaceAt with uniqueness at θ ≠ 0, simpleNVector, the upper density theorem, area_image_compl_regularSet_eq_zero and Lipschitz image bounds. Mathlib provides alternatizeUncurryFin(_apply), ContDiffAt.implicitFunction with C¹ regularity, LipschitzOnWith.extend_finite_dimension, Lusin–Souslin images and the a.e./restriction API cited in the child proofs. Neither library has slicing, a rectifiable co-area formula, or tangent identification on C¹ charts. The co-area formula comes from the sibling slicing_im_coarea, passed as a hypothesis. Tangent identification is the new child weighted_tangent_chart. Its type equals that of the pending, not-accepted lpf_weighted_tangent_on_c1_chart, hence the fresh name. The only accepted declaration reused is fiw_ims_frame_sign, with identical type. All 8 child types elaborate in the comparator scope. The parent type follows from coarea plus 4 children, and slice_geometry from its 5 siblings, with standard axioms only. ae_transfer is fully proved in Lean. None of the names slicing_im_st_* occurs in the DAG or the snapshot. These checks do not certify the analytic proofs of the remaining children.
