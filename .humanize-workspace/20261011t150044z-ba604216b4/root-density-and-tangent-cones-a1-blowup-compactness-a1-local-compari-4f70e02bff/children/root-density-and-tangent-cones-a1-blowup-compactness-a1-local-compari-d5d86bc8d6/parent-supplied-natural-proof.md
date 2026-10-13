# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.chart_coarea-a1.slice_disks-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6–7 of the parent proof (each open slice Ω_k^t is covered by countably many closed balls; χ_k^t is Lipschitz on each ball; the tangent identification of step 2). This is the local, parametrised form of Simon Ch. 2, 6.4. In Simon's setting M is an embedded C¹ submanifold and f⁻¹(y) ∖ C is a C¹ submanifold. Here ψ need not be a topological embedding of V. So only countably many injective C¹ parametrised disks χ_j are produced, and no embeddedness of ψ(V) or of the level sets is asserted or used.

Notation: c(s,w) := (s, w_0, …, w_{n−1}) ∈ ℝ^{n+1} for s ∈ ℝ and w ∈ ℝⁿ, so c(s,w)_0 = s and c(s,w)_{i+1} = w_i; for instance c(s,w) = WithLp.toLp 2 (Fin.cons s w).

1. Charts and level parametrisations. The sibling flattening_atlas, applied to (n, F, V), gives (Ω_k, Θ_k)_{k∈ℕ} with the chart properties and {y ∈ V : DF(y) ≠ 0} ⊆ ⋃_k Θ_k(Ω_k). For each k, apply the sibling slice_param to (c, ψ, V, Ω_k, F, Θ_k, t); its hypotheses are ours plus the chart properties. It gives:
   - U^k := {w : c(t,w) ∈ Ω_k} is open;
   - χ^k(w) := ψ(Θ_k(c(t,w))) is C¹ and injective on U^k;
   - for w ∈ U^k, with y := Θ_k(c(t,w)): DF(y) ≠ 0, Dχ^k(w) is injective, and Dχ^k(w)(ℝⁿ) = Dψ(y)(ℝ^{n+1}) ∩ (ℝv)^⊥ for every v ∈ Dψ(y)(ℝ^{n+1}) with ⟨v, Dψ(y)e⟩ = DF(y)e for all e.
2. Indexing. ℝⁿ is separable; let (d_m)_{m∈ℕ} be a dense sequence in it (Mathlib TopologicalSpace.denseSeq). Let (q_l)_{l∈ℕ} enumerate ℚ, e.g. q_l := decode l with default 0. For j ∈ ℕ write j = ⟨k, ⟨m, l⟩⟩ using the Cantor pairing (Nat.unpair), and put:
   - U_j := U^k, χ_j := χ^k and a_j := d_m;
   - r_j := q_l if closedBall(d_m, q_l) ⊆ U^k, and r_j := −1 otherwise (note closedBall(a, −1) = ball(a, −1) = ∅).
3. Properties for each index. Fix j = ⟨k, ⟨m, l⟩⟩.
   (i) U_j = U^k is open, and closedBall(a_j, r_j) ⊆ U_j by the choice of r_j.
   (ii) χ_j is C¹ and injective on U_j (step 1).
   (iii) χ_j(U_j) is countably n-rectifiable: it is the image of the open set U_j ⊆ ℝⁿ under a map that is C¹ on U_j (SimonGMT countablyRectifiable_image_contDiffOn_open, Chapter03/SubmanifoldCover.lean).
   (iv) closedBall(a_j, r_j) is convex and compact, and χ_j is C¹ on it since it lies in U_j. So χ_j is K-Lipschitz on it for some K (Mathlib ContDiffOn.exists_lipschitzOnWith). Hence, by SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn, Hⁿ(χ_j(closedBall(a_j, r_j))) ≤ Kⁿ·Hⁿ(closedBall(a_j, r_j)) = Kⁿ·Lⁿ(closedBall(a_j, r_j)) < ∞, using Hⁿ = Lⁿ on ℝⁿ and finiteness of Lebesgue measure on compact sets.
   (v) Let w ∈ U_j and y := Θ_k(c(t,w)). Then y ∈ Θ_k(Ω_k) ⊆ V, ψ(y) = χ_j(w), and F(y) = c(t,w)_0 = t by the chart property F(Θ_k(z)) = z_0. By step 1, DF(y) ≠ 0, Dχ_j(w) is injective, and the range identity holds for every admissible v.
4. Covering. Let y ∈ V with F(y) = t and DF(y) ≠ 0.
   - By step 1, y = Θ_k(z) for some k and z ∈ Ω_k, and z_0 = F(Θ_k(z)) = t.
   - Let w ∈ ℝⁿ with w_i := z_{i+1}. Then c(t,w) and z have the same coordinates, so c(t,w) = z, w ∈ U^k and ψ(y) = χ^k(w).
   - U^k is open, so choose ε > 0 with ball(w, ε) ⊆ U^k, a rational q with 0 < q < ε/2, and, by density, m with |d_m − w| < q.
   - For u ∈ closedBall(d_m, q), |u − w| ≤ |u − d_m| + |d_m − w| < 2q < ε, so closedBall(d_m, q) ⊆ U^k. Also w ∈ ball(d_m, q).
   - Let l be an index with q_l = q and put j := ⟨k, ⟨m, l⟩⟩. Then a_j = d_m, r_j = q and χ_j = χ^k, so ψ(y) = χ_j(w) ∈ χ_j(ball(a_j, r_j)).
   Hence ψ({y ∈ V : F(y) = t, DF(y) ≠ 0}) ⊆ ⋃_j χ_j(ball(a_j, r_j)). ∎

## Key steps

1. flattening_atlas charts plus slice_param give, for each k, the open slice U^k = {w : c(t, w) ∈ Ω_k} and the C¹ injective χ^k = ψ∘Θ_k∘c(t,·), with injective derivative, DF ≠ 0 and the range identity at Θ_k(c(t, w)).
2. Index rational balls: j = (k, m, l) gives U_j = U^k, a_j = d_m (dense sequence), r_j = q_l if closedBall(d_m, q_l) ⊆ U^k and −1 otherwise.
3. Each χ_j(U_j) is countably rectifiable (countablyRectifiable_image_contDiffOn_open). χ_j is Lipschitz on the convex compact closedBall, so Hⁿ of its image is finite.
4. Points of U_j come from y = Θ_k(c(t, w)) ∈ V with F(y) = t, DF(y) ≠ 0 and the tangent identification.
5. Every y ∈ V with F(y) = t and DF(y) ≠ 0 is Θ_k(c(t, w)) with w ∈ U^k, and w lies in a rational ball whose closure is in U^k, so ψ(y) ∈ χ_j(ball(a_j, r_j)).

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
