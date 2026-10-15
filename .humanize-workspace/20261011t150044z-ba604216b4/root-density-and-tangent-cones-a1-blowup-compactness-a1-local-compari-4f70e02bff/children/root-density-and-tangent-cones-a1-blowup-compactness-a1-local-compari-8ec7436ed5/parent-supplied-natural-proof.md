# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.piece_coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, the formula on one piece Y_k ⊆ W_k. It combines the weighted area formula for ψ, the change of variables, Tonelli, and the area formula for the level parametrisations χ^t together with (★).

Notation.
- Hᵏ = μHE[k]; on ℝ^k, Hᵏ = L^k (Mathlib InnerProductSpace.euclideanHausdorffMeasure_eq_volume with finrank_euclideanSpace_fin).
- c(s,w) := (s, w_0, …, w_{n−1}), e.g. WithLp.toLp 2 (Fin.cons s w); it satisfies the coordinate hypotheses of flat_fubini and slice_param.
- For a linear map X from a finite-dimensional inner product space, J(X) := √det(X*X). J(X) = normDet X by Mathlib ContinuousLinearMap.normDet_sq and LinearMap.normDet_nonneg. SimonGMT's metric Jacobian is areaJacobianAt f x = normDet(Df(x)) (areaJacobianAt_eq_normDet).

1. Gradient on Y'. Apply the sibling chart_gradient with N := n+1 and ψ, V, F. It gives a Borel Ĝ such that, for y ∈ V, Ĝ(y) ∈ Dψ(y)(ℝ^{n+1}), ⟨Ĝ(y), Dψ(y)e⟩ = DF(y)e, and Ĝ(y) is the unique such vector. For y ∈ Y' ⊆ Θ(Ω) ⊆ V, the vector G(ψ(y)) has both properties by hypothesis, so G(ψ(y)) = Ĝ(y).
2. A Borel density. Let J_ψ(y) := J(Dψ(y)). It is continuous in y: y ↦ Dψ(y) is continuous since ψ is C¹, and the adjoint, composition, det and √ are continuous. Put f(y) := ofReal(|Ĝ(y)|·J_ψ(y))·g(ψ(y)). f is Borel because Ĝ, J_ψ, ψ and g are Borel.
3. Fubini data. Apply the sibling flat_fubini to (n, c, Ω, Y', Θ, f). Let S := Ω ∩ Θ⁻¹(Y'), which is Borel as in flat_fubini, and H(z) := 1_S(z)·ofReal|det DΘ(z)|·f(Θ(z)). Then I(t) := ∫_{ℝⁿ} H(c(t,w)) dw is Borel in t and ∫_ℝ I(t) dt = ∫_{Y'} f dL^{n+1}.
4. One level. Fix t ∈ ℝ. Apply the sibling slice_param with c, ψ, V, Ω, F, Θ and t; all its hypotheses are among ours. It gives:
   - Ω^t := {w : c(t,w) ∈ Ω} is open;
   - χ(w) := ψ(Θ(c(t,w))) is C¹ and injective on Ω^t;
   - for w ∈ Ω^t, with z = c(t,w) and y = Θ(z), Dχ(w) is injective;
   - for every v ∈ Dψ(y)(ℝ^{n+1}) with ⟨v, Dψ(y)e⟩ = DF(y)e for all e, J(Dχ(w)) = |v|·J_ψ(y)·|det DΘ(z)|.
   Let S^t := {w : c(t,w) ∈ S} ⊆ Ω^t. It is Borel, being the preimage of S under the continuous map c(t,·).
5. Set identity ψ(Y' ∩ F⁻¹(t)) = χ(S^t).
   - ⊆: let y ∈ Y' with F(y) = t. Since Y' ⊆ Θ(Ω), y = Θ(z) for some z ∈ Ω, and z_0 = F(Θ(z)) = t. Let w_i := z_{i+1}. Then c(t,w) and z have equal coordinates, so c(t,w) = z, w ∈ S^t and χ(w) = ψ(y).
   - ⊇: if w ∈ S^t, then y := Θ(c(t,w)) ∈ Y', F(y) = c(t,w)_0 = t and ψ(y) = χ(w).
6. Area formula on the level. χ is differentiable at every w ∈ S^t, since it is C¹ on the open set Ω^t ⊇ S^t; Dχ(w) is injective; and χ is injective on S^t. SimonGMT weighted_area_formula_volume_of_injective_derivative (source ℝⁿ, finrank n) gives
   ∫_{χ(S^t)} g dHⁿ = ∫_{S^t} ofReal(normDet Dχ(w))·g(χ(w)) dw.
7. Matching the integrands. Let w ∈ S^t, z = c(t,w) ∈ S and y = Θ(z) ∈ Y'. By step 1, v := G(ψ(y)) = Ĝ(y) satisfies the hypothesis of step 4. So normDet Dχ(w) = J(Dχ(w)) = |Ĝ(y)|·J_ψ(y)·|det DΘ(z)|. All three factors are ≥ 0, so
   ofReal(normDet Dχ(w))·g(χ(w)) = ofReal|det DΘ(z)|·ofReal(|Ĝ(y)|·J_ψ(y))·g(ψ(y)) = ofReal|det DΘ(z)|·f(Θ(z)) = H(c(t,w)).
   If w ∉ S^t, then c(t,w) ∉ S and H(c(t,w)) = 0. With the indicator formula (S^t Borel) and steps 5–6:
   ∫_{ψ(Y'∩F⁻¹(t))} g dHⁿ = ∫_{ℝⁿ} 1_{S^t}(w)·ofReal(normDet Dχ(w))·g(χ(w)) dw = ∫_{ℝⁿ} H(c(t,w)) dw = I(t).
8. Measurability. By step 7, t ↦ ∫_{ψ(Y'∩F⁻¹(t))} g dHⁿ equals I, which is Borel by step 3.
9. Integral. By steps 7 and 3, ∫_ℝ ∫_{ψ(Y'∩F⁻¹(t))} g dHⁿ dt = ∫_{Y'} f dL^{n+1}. For y ∈ Y', f(y) = ofReal(J_ψ(y))·(ofReal|G(ψ(y))|·g(ψ(y))) by step 1 and nonnegativity.
   Now apply SimonGMT weighted_area_formula_volume_of_injective_derivative to ψ on the Borel set Y', with source ℝ^{n+1} (finrank n+1). Its hypotheses hold: ψ is differentiable, Dψ(y) is injective for y ∈ Y' ⊆ V, and ψ is injective on Y' ⊆ V. The formula allows an arbitrary (not necessarily Borel) target weight; take x ↦ ofReal|G(x)|·g(x). It gives
   ∫_{ψ(Y')} ofReal|G(x)|·g(x) dH^{n+1}(x) = ∫_{Y'} ofReal(areaJacobianAt ψ y)·ofReal|G(ψ(y))|·g(ψ(y)) dy = ∫_{Y'} f,
   because areaJacobianAt ψ y = normDet Dψ(y) = J_ψ(y). This is the claimed identity. ∎

## Key steps

1. chart_gradient gives a Borel Ĝ with G(ψ y) = Ĝ(y) on Y' (uniqueness). Put f = ofReal(|Ĝ|·J_ψ)·g∘ψ, which is Borel.
2. flat_fubini: I(t) = ∫ 1_S(c(t,w))·|det DΘ|·f(Θ(c(t,w))) dw is Borel and ∫ I = ∫_{Y'} f.
3. For each t: ψ(Y' ∩ F⁻¹t) = χ^t(S^t), and the injective area formula for χ^t (slice_param regularity) holds on the Borel set S^t.
4. slice_param's Jacobian identity with v = G(ψ y) turns the area-formula integrand into H(c(t,w)), so the slice integral equals I(t), which is Borel.
5. ∫_{Y'} f equals ∫_{ψ(Y')} |G| g dH^{n+1} by the weighted area formula for ψ, using J_ψ = areaJacobianAt ψ.

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
