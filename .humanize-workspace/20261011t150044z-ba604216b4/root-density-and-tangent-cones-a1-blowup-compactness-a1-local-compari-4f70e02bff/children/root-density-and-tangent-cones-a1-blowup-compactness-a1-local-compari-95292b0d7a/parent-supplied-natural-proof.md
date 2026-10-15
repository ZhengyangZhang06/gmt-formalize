# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.regular_coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2 and 4 of the parent proof, restricted to the regular part Y_r = Y ∩ {∇F ≠ 0}: choose countably many flattening charts covering it, make the pieces disjoint, apply the one-chart formula and sum.

1. Charts. The sibling flattening_atlas, applied to (n, F, V), gives open sets Ω_k and maps Θ_k (k ∈ ℕ) with the chart properties: Θ_k is C¹ and injective on Ω_k with injective derivative, W_k := Θ_k(Ω_k) is open and contained in V, and F(Θ_k(z)) = z_0 on Ω_k. It also gives {y ∈ V : DF(y) ≠ 0} ⊆ ⋃_k W_k. By hypothesis Y' ⊆ V and DF ≠ 0 on Y', so Y' ⊆ ⋃_k W_k.
2. Disjoint pieces. Let Y_k := (Y' ∩ W_k) ∖ ⋃_{i<k} (Y' ∩ W_i) (Mathlib disjointed). Each Y_k is Borel because Y' is Borel and the W_i are open. Also Y_k ⊆ Y' ∩ W_k, the Y_k are pairwise disjoint, and ⋃_k Y_k = ⋃_k (Y' ∩ W_k) = Y' ∩ ⋃_k W_k = Y'.
3. One chart. For each k, apply the sibling piece_coarea to (ψ, V, Ω_k, Y_k, F, Θ_k, G). Its chart hypotheses come from step 1; Y_k is Borel with Y_k ⊆ W_k = Θ_k(Ω_k); and the gradient hypothesis on Y_k ⊆ Y' is ours. So φ_k(t) := ∫_{ψ(Y_k∩F⁻¹(t))} g dHⁿ is Borel in t, and ∫_ℝ φ_k = ∫_{ψ(Y_k)} |G| g dH^{n+1}.
4. Images.
   - If A ⊆ Y' is Borel, then ψ(A) is Borel: ψ is continuous and injective on A ⊆ V, so the Lusin–Souslin theorem applies (Mathlib MeasurableSet.image_of_continuousOn_injOn).
   - If A_k ⊆ Y_k for every k, the sets ψ(A_k) are pairwise disjoint. Indeed, ψ(a) = ψ(b) with a ∈ A_i and b ∈ A_j forces a = b because ψ is injective on V ⊇ Y', which is impossible for i ≠ j since Y_i ∩ Y_j = ∅.
   - F⁻¹(t) is closed because F is continuous.
5. Slices. For every t, Y' ∩ F⁻¹(t) = ⋃_k (Y_k ∩ F⁻¹(t)), so ψ(Y'∩F⁻¹(t)) = ⋃_k ψ(Y_k∩F⁻¹(t)). By step 4 this is a countable disjoint union of Borel sets. Countable additivity of the set integral (Mathlib lintegral_iUnion, valid for any integrand) gives ∫_{ψ(Y'∩F⁻¹(t))} g dHⁿ = Σ_k φ_k(t). A countable sum of Borel [0,∞]-valued functions is Borel, which proves the measurability claim.
6. Integral. By monotone convergence for series (Mathlib lintegral_tsum) and step 3, ∫_ℝ Σ_k φ_k = Σ_k ∫_ℝ φ_k = Σ_k ∫_{ψ(Y_k)} |G| g dH^{n+1}. By step 4, ψ(Y') = ⋃_k ψ(Y_k) is a countable disjoint union of Borel sets, so lintegral_iUnion gives Σ_k ∫_{ψ(Y_k)} |G| g dH^{n+1} = ∫_{ψ(Y')} |G| g dH^{n+1}. ∎

## Key steps

1. flattening_atlas covers Y' ⊆ {y ∈ V : DF(y) ≠ 0} by countably many open W_k = Θ_k(Ω_k).
2. Disjointify: Y_k = disjointed(Y' ∩ W_k) are Borel, pairwise disjoint, Y_k ⊆ W_k, and their union is Y'.
3. piece_coarea on each Y_k gives a Borel slice function φ_k with ∫ φ_k = ∫_{ψ(Y_k)} |G| g.
4. ψ maps the disjoint Borel pieces to disjoint Borel sets (Lusin–Souslin, injectivity on V), so the slice integral is Σ_k φ_k, which is Borel.
5. lintegral_tsum and lintegral_iUnion give the formula on ψ(Y').

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db1da5…, mathlib_commit 25730c7c759d…)`
- `python3 -I json reads of nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4f70e02bff/{parent-child-handoff.json, parent-supplied-natural-proof.md, decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json}`
- `python3 -I scan of dag.json (1571 nodes): status and lean_statement of dtc_bc_lc_sl_chart_coarea (decomposing), dtc_bc_lc_sl_eilenberg (decomposing, depth-6 children dtc_bc_lc_sl_eil_limit and dtc_bc_lc_sl_eil_scale), dtc_bc_lc_sl_c1_tangent (decomposing), cmc_imRep_locality_restrict_sub (accepted); lean_name prefix dtc_bc_lc_sl_cc (no match)`
- `grep -rl 'dtc_bc_lc_sl_cc_' nodes decomposition-reopenings operator-dependency-edits issue-workers.json DAG.md (only this node's decomposition-v1/audit-v1/review-receipt-v1); git log --all --oneline -S 'dtc_bc_lc_sl_cc_' over 6785 refs (no match)`
- `head -80 and grep 'Euclid|μHE|^open|^namespace|^import' GMT/Ch07/Contract.lean (namespace GMT.Ch07, abbrev Euclid, CountablyRectifiable and HasApproximateTangentSpaceAt opened from Poincare.SimonGMT.Chapter03)`
- `grep -rln 'theorem <name>' local-references/123e8435b4a2469b/mathlib/Mathlib for the cited Mathlib lemma names (Ring.inverse, NormedRing.inverse_continuousAt, ContinuousOn.measurable_piecewise, normDet_sq/nonneg/comp_of_finrank_eq/eq_abs_det/eq_norm_det_toMatrix_rangeRestrict, det_succ_row_zero, toOpenPartialHomeomorph, isOpen_image_of_subset_source, contDiffAt_symm, hasFDerivAt_symm, isOpen_iUnion_countable, lintegral_image_eq_lintegral_abs_det_fderiv_mul, measurable_fderiv, piFinSuccAbove, measurePreserving_piFinSuccAbove, volume_preserving_symm_measurableEquiv_toLp, lintegral_prod_right', lintegral_prod, euclideanHausdorffMeasure_eq_volume, uniformContinuousOn_of_continuous, lipschitzOnWith_of_nnnorm_fderiv_le, lintegral_tsum, lintegral_liminf_le, lintegral_eq_zero_iff, image_of_continuousOn_injOn, lintegral_iUnion, denseSeq, ContDiffOn.exists_lipschitzOnWith, MeasurePreserving.prod/symm, volume_pi, volume_eq_prod)`
- `grep -rn 'theorem weighted_area_formula_volume_of_injective_derivative|theorem areaJacobianAt_eq_normDet|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|theorem countablyRectifiable_image_contDiffOn_open|theorem countablyRectifiable_iUnion|def CountablyRectifiable|def HasApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT`
- `lake env lean /tmp/cc_v2/names/Names.lean, Sig.lean, Sig2.lean (#check of every cited Mathlib/SimonGMT lemma: all resolve; the only unknown constant, EuclideanSpace.volume_preserving_measurableEquiv, was my own extra probe and is not cited)`
- `lake env lean /tmp/cc_v2/names/Inst.lean (rfl: (X.adjoint ∘L X).det = LinearMap.det of ContinuousLinearMap.comp (adjoint X) X; (ℝ ∙ v)ᗮ = (span ℝ {v}).orthogonal; z 0 = WithLp.ofLp z 0)`
- `python3 -I /tmp/cc_v2/scripts/gen.py (lean_contract.validate_lean_statement + gmt-compare.py child_modules, contract mode) then lake env lean /tmp/cc_v2/challenges/Challenge_<key>.lean for all 9 keys (only the expected sorry warning)`
- `python3 -I /tmp/cc_v2/scripts/mkasm.py (frozen types read from dag.json and the proposal) then lake env lean /tmp/cc_v2/asm/Assembly.lean with #print axioms (propext, sorryAx, Classical.choice, Quot.sound; sorry only in the 12 stubs)`
- `python3 -I /tmp/cc_v2/scripts/mkedge.py then lake env lean /tmp/cc_v2/asm/Edge_{regular_coarea,piece_coarea,slice_param,slice_disks}.lean (stubs only for declared siblings; derivations sorry-free)`
- `sed -n 1380,1540p book/chapter-02.txt (Simon Ch. 2 §6, 6.1–6.7)`
- `python3 -I regex scan of decomposition-v1.json child titles/statements/proofs for ψ⁻¹|submanifold|F∘ψ|gradient of|embedd|tangential|diffeomorph|homeomorph|immersion (hits: chart_gradient statement/preamble, slice_param title 'C¹ embedding', slice_disks Simon 6.4 citation, v1 rationale)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4f70e02bff/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4f70e02bff/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4f70e02bff/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4f70e02bff/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4f70e02bff/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Piecewise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/cc_v2/challenges`
- `/tmp/cc_v2/asm/Assembly.lean`
- `/tmp/cc_v2/asm/Edge_regular_coarea.lean`
- `/tmp/cc_v2/asm/Edge_piece_coarea.lean`
- `/tmp/cc_v2/asm/Edge_slice_param.lean`
- `/tmp/cc_v2/asm/Edge_slice_disks.lean`
- `/tmp/cc_v2/names/Names.lean`
- `/tmp/cc_v2/names/Sig.lean`
- `/tmp/cc_v2/names/Sig2.lean`
- `/tmp/cc_v2/names/Inst.lean`

The pinned snapshot has every library result the children use. Mathlib: the C¹ inverse function theorem (ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm/hasFDerivAt_symm), injective change of variables (lintegral_image_eq_lintegral_abs_det_fderiv_mul), the measure-preserving splitting ℝ^{n+1} ≅ ℝ × ℝⁿ (measurePreserving_piFinSuccAbove, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, MeasurePreserving.prod/symm/comp), Tonelli, Fatou, Lusin–Souslin images, normDet_sq/normDet_comp_of_finrank_eq. SimonGMT: the injective weighted area formula for arbitrary [0,∞] weights (Chapter02/WeightedArea.lean:120), areaJacobianAt_eq_normDet (Chapter02/Area.lean:35), the Hausdorff Lipschitz-image bound (Chapter02/Lipschitz.lean:216), countablyRectifiable_image_contDiffOn_open (Chapter03/SubmanifoldCover.lean:44) and countablyRectifiable_iUnion (Chapter03/Rectifiable.lean:76). Neither library has a nonlinear co-area formula, a Sard/Eilenberg statement or a level-set parametrisation, so these become the nine children. No dtc_bc_lc_sl_cc_* name is reserved anywhere, and no DAG node with any of the nine types is accepted. All nine types elaborate in contract-mode challenge modules, with instances confirmed by rfl. A regenerated Lean assembly derives the exact frozen parent type from the nine children and the three resolved dependencies (eilenberg via critical_null's hypothesis, c1_tangent, accepted cmc_imRep_locality_restrict_sub). The four internal child edges compile from their declared siblings only. Axioms: propext, Classical.choice, Quot.sound, plus sorryAx from the stubs alone.
