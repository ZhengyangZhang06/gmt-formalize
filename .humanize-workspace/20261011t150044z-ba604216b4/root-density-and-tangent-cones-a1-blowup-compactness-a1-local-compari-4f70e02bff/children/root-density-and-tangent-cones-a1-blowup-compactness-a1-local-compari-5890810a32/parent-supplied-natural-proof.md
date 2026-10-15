# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.flat_fubini-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3(a) of the parent proof: the change of variables y = Φ_k⁻¹(t, w) = Θ(c(t, w)) and Tonelli in the product coordinates ℝ^{n+1} = ℝ × ℝⁿ.

Notation. All integrals over ℝ^k are for Lebesgue measure L^k (Mathlib volume on Euclid k). The hypothesis on c says c(s,w)_0 = s and c(s,w)_{i+1} = w_i. Points of ℝ^{n+1} are determined by their coordinates, so c(s,w) = (s, w_0, …, w_{n−1}) for all s, w. Put S := Ω ∩ Θ⁻¹(Y') and H(z) := 1_S(z)·ofReal|det DΘ(z)|·f(Θ(z)); both claims concern t ↦ ∫_{ℝⁿ} H(c(t,w)) dw.

1. S is Borel. Let Θ' := Θ on Ω and Θ' := 0 off Ω. Θ is continuous on the open (hence Borel) set Ω, so Θ' is Borel (Mathlib ContinuousOn.measurable_piecewise). Then S = Ω ∩ Θ'⁻¹(Y') is Borel because Y' is.
2. Θ(S) = Y'. Clearly Θ(S) ⊆ Y'. Conversely, if y ∈ Y' ⊆ Θ(Ω), then y = Θ(z) with z ∈ Ω, and z ∈ S.
3. Change of variables. For z ∈ S ⊆ Ω, Ω is a neighbourhood of z and Θ is C¹ on Ω, so Θ is differentiable at z and has derivative DΘ(z) within S at z. Θ is injective on S. The change of variables formula for injective differentiable maps (Mathlib MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul, Lebesgue measure on ℝ^{n+1}, S measurable) gives
   ∫_{Θ(S)} f = ∫_S ofReal|det DΘ(z)|·f(Θ(z)) dz.
   With step 2 and the indicator formula (lintegral_indicator, S Borel), ∫_{Y'} f = ∫_{ℝ^{n+1}} H.
4. H is Borel. On S, Θ = Θ', so H = 1_S·(ofReal|det DΘ|·f∘Θ'). The map z ↦ DΘ(z) is Borel for any function Θ (Mathlib measurable_fderiv); det, |·| and ofReal are continuous; f∘Θ' and S are Borel. Hence H is Borel.
5. Product coordinates. Define Π : ℝ × ℝⁿ → ℝ^{n+1} by Π(t, w) := c(t, w). Π is a measurable equivalence that carries L¹ ⊗ Lⁿ to L^{n+1} (Lebesgue measure on ℝ × ℝⁿ is the product measure, MeasureTheory.Measure.volume_eq_prod). Indeed, Π is the composite (MeasurePreserving.comp) of three measure-preserving measurable equivalences:
   - id_ℝ × (ℝⁿ → (Fin n → ℝ), w ↦ (w_0, …, w_{n−1})). The coordinate map ℝⁿ → (Fin n → ℝ) is measure preserving (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp). So the product map is measure preserving from L¹ ⊗ Lⁿ to L¹ ⊗ (Lebesgue measure on Fin n → ℝ) (MeasurePreserving.prod).
   - The inverse of Mathlib MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 : (Fin (n+1) → ℝ) → ℝ × (Fin n → ℝ). The forward map u ↦ (u_0, (u_{i+1})_i) is measure preserving by MeasureTheory.measurePreserving_piFinSuccAbove, because Lebesgue measure on Fin k → ℝ is the product measure (MeasureTheory.volume_pi). Hence its inverse is measure preserving (MeasurePreserving.symm). The inverse sends (t, u) to the function with value t at 0 and u_i at i+1.
   - (Fin (n+1) → ℝ) → ℝ^{n+1}, the inverse of the coordinate map of EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, hence measure preserving (MeasurePreserving.symm).
   The composite sends (t, w) to the point with coordinate 0 equal to t and coordinate i+1 equal to w_i, i.e. to c(t, w). In particular Π is continuous and H∘Π is Borel.
6. Tonelli. H∘Π is Borel on ℝ × ℝⁿ and Lebesgue measures are σ-finite. So t ↦ ∫_{ℝⁿ} H(c(t,w)) dw is Borel (Mathlib Measurable.lintegral_prod_right'), which is the first claim. Moreover:
   - ∫_ℝ ∫_{ℝⁿ} H(c(t,w)) dw dt = ∫_{ℝ×ℝⁿ} H∘Π d(L¹⊗Lⁿ) (lintegral_prod);
   - this equals ∫_{ℝ^{n+1}} H dL^{n+1} (step 5, MeasurePreserving.lintegral_comp);
   - this equals ∫_{Y'} f (step 3).
   This is the second claim. ∎

## Key steps

1. S = Ω ∩ Θ⁻¹(Y') is Borel (Θ continuous on open Ω, piecewise extension) and Θ(S) = Y'.
2. Change of variables (lintegral_image_eq_lintegral_abs_det_fderiv_mul): ∫_{Y'} f = ∫_S |det DΘ| f∘Θ = ∫ H.
3. H is Borel (measurable_fderiv, continuity of det, piecewise extension of Θ).
4. (t, w) ↦ c(t, w) is a measure-preserving equivalence ℝ × ℝⁿ → ℝ^{n+1} (piFinSuccAbove at 0 and the EuclideanSpace toLp equivalences).
5. Tonelli gives Borel measurability of t ↦ ∫ H(c(t, w)) dw and ∫∫ H(c(t, w)) dw dt = ∫ H = ∫_{Y'} f.

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
