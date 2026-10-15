# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 5, 6 and 7 of the parent proof restricted to one piece S = g(A) (Simon Ch. 3, §2, (2.4)–(2.5), chapter-03.txt lines 330–407, proved there by applying the Euclidean area formula of Ch. 2, 3.4–3.5 piece by piece), with the library facts (L1), (A1), (A2), (G). Notation: E := ℝ^P; λ := L^n = volume on ℝ^n; H^n := μHE[n] on E and on ℝ^n (on ℝ^n, μHE[n] = λ, EuclideanSpace.euclideanHausdorffMeasure_eq_volume); Γ := g(A); Φ := G∘g : ℝ^n → ℝ^n, which is Lipschitz; for φ between finite-dimensional inner product spaces, Dφ(a) := fderiv ℝ φ a and J_φ(a) := normDet(Dφ(a)) ≥ 0 (SimonGMT areaJacobianAt φ a, Mathlib LinearMap.normDet); for k : E → [0, ∞] and y ∈ ℝ^n, Σ_k(y) := Σ_{x∈Γ, F(x)=y} k(x) ∈ [0, ∞] (tsum over the subtype Γ ∩ F^{−1}{y}).
Library facts. (L1) If ψ is K-Lipschitz on X then μHE[n](ψ(X)) ≤ K^n μHE[n](X) (SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn). (A1) For a Lipschitz φ : ℝ^n → ℝ^n, a Borel s ⊆ ℝ^n and a Borel w : ℝ^n → [0, ∞], the fibre sum y ↦ Σ_{a∈s, φ(a)=y} w(a) is μHE[n]-a.e. measurable and ∫ Σ_{a∈s, φ(a)=y} w(a) dμHE[n](y) = ∫_s J_φ(a)w(a) dλ(a) (SimonGMT Chapter02/AreaNoninjective.lean aemeasurable_weightedAreaFiberSum_lipschitz and weighted_area_formula_lipschitz_fiberSum; finrank ℝ ℝ^n = n). (A2) For a Lipschitz ψ : ℝ^n → E, a Borel s on which ψ is injective and an arbitrary κ : E → [0, ∞], ∫_{ψ(s)} κ dμHE[n] = ∫_s J_ψ(a)κ(ψ(a)) dλ(a) (SimonGMT Chapter02/AreaLipschitz.lean weighted_area_formula_lipschitz_injOn). (G) For linear L : ℝ^n → E and A' : E → ℝ^n, normDet(A'∘L) = normDet(A'|_{range L})·normDet(L) (Mathlib LinearMap.normDet_comp), and for a subspace T ⊆ E with orthonormal basis u, normDet(A'|_T)² = det(⟨A'u_i, A'u_j⟩)_{i,j} (Mathlib LinearMap.normDet_sq_eq_det_gram applied to A'.domRestrict T and u; Matrix.gram is the matrix of inner products).
1. (Γ is Borel.) g is continuous, A is Borel in the Polish space ℝ^n and g is injective on A, so Γ is Borel (Lusin–Souslin, MeasurableSet.image_of_continuousOn_injOn).
2. (Reduction to Borel h; parent step 0.) As h is a.e. measurable for H^n⌞Γ, there is a Borel h̃ : E → [0, ∞] with (H^n⌞Γ)({h ≠ h̃}) = 0; since Γ is Borel, Measure.restrict_apply' gives H^n(N) = 0 for N := Γ ∩ {h ≠ h̃}. As N ⊆ Γ ⊆ V and F = G on V, F(N) = G(N), and by (L1) for the Lipschitz G, H^n(G(N)) = 0 on ℝ^n, i.e. λ(F(N)) = 0. If y ∉ F(N), every x ∈ Γ with F(x) = y satisfies h(x) = h̃(x), so Σ_h(y) = Σ_{h̃}(y); hence Σ_h = Σ_{h̃} λ-a.e. Also J_T·h = J_T·h̃ H^n⌞Γ-a.e. Since a.e. measurability is preserved by a.e. equality and lintegrals of a.e. equal functions coincide, both conclusions for h follow from those for h̃. From now on h is Borel.
3. (Fibres; parent step 7 on the piece.) Fix y ∈ ℝ^n. The map a ↦ g(a) is a bijection from {a ∈ A : Φ(a) = y} onto {x ∈ Γ : F(x) = y}: if a ∈ A and Φ(a) = y, then g(a) ∈ Γ ⊆ V, so F(g(a)) = G(g(a)) = y; if x ∈ Γ and F(x) = y, then x = g(a) for some a ∈ A and Φ(a) = G(g(a)) = F(g(a)) = y (F = G on V ∋ x); and g is injective on A. Reindexing the [0, ∞]-valued sum along this bijection (Equiv.tsum_eq) gives Σ_h(y) = W(y) := Σ_{a∈A, Φ(a)=y} h(g(a)).
4. (Euclidean area formula (A1).) Φ is Lipschitz, A is Borel and w := h∘g is Borel (h Borel, g continuous). By (A1) and μHE[n] = λ on ℝ^n, W is λ-a.e. measurable and ∫ W dλ = ∫_A J_Φ(a)h(g(a)) dλ(a). By step 3, Σ_h = W, so Σ_h is λ-a.e. measurable and ∫ Σ_h dλ = ∫_A J_Φ(a)h(g(a)) dλ(a).
5. (Jacobian chain rule; parent step 5.) Let a ∈ A with T(g(a)) = range Dg(a); by hypothesis this holds for λ⌞A-a.e. a. Put x := g(a) ∈ Γ ⊆ V, L := Dg(a) (g is differentiable at a ∈ A) and A' := DF(x) (F is differentiable at x ∈ Γ). Since F = G on the open set V ∋ x, F and G agree on a neighbourhood of x, so G is differentiable at x with DG(x) = A' (HasFDerivAt.congr_of_eventuallyEq, Filter.EventuallyEq.fderiv_eq). By the chain rule Φ = G∘g is differentiable at a and DΦ(a) = A'∘L. By (G), J_Φ(a) = normDet(A'∘L) = normDet(A'|_{range L})·normDet(L) = normDet(A'|_{T(x)})·J_g(a), and normDet(A'|_{T(x)})² = det(⟨A'u_i, A'u_j⟩)_{i,j} for the standard orthonormal basis u of T(x); as normDet ≥ 0, normDet(A'|_{T(x)}) = J_T(x). Hence J_Φ(a) = J_T(g(a))·J_g(a) for λ⌞A-a.e. a.
6. (Carrier side; parent step 6 on the piece.) Apply (A2) to ψ := g, s := A (g is Lipschitz and injective on the Borel set A) and κ := ofReal(J_T)·h (no measurability of κ is needed): ∫_Γ ofReal(J_T)h dH^n = ∫_A ofReal(J_g(a))·ofReal(J_T(g(a)))·h(g(a)) dλ(a). By step 5 and ofReal(st) = ofReal(s)ofReal(t) for s, t ≥ 0, the integrand equals ofReal(J_Φ(a))·h(g(a)) for λ⌞A-a.e. a, so ∫_Γ ofReal(J_T)h dH^n = ∫_A J_Φ(a)h(g(a)) dλ(a).
7. (Conclusion.) By steps 4 and 6, Σ_h is λ-a.e. measurable and ∫ Σ_h dλ = ∫_A J_Φ(a)h(g(a)) dλ(a) = ∫_Γ ofReal(J_T)·h dH^n, which are the two assertions (for Borel h, hence, by step 2, for the given h). ∎

## Key steps

1. g(A) is Borel (Lusin–Souslin); replace h by a Borel h̃ equal to it H^n-a.e. on g(A): the exceptional set N is H^n-null and F(N) = G(N) is λ-null since G is Lipschitz.
2. For each y, a ↦ g(a) is a bijection {a ∈ A : G(g(a)) = y} → {x ∈ g(A) : F(x) = y}, so the carrier fibre sum equals the parameter fibre sum of Φ = G∘g with weight h∘g.
3. The Euclidean weighted area formula for the Lipschitz Φ gives a.e. measurability and ∫ fibre sum = ∫_A J_Φ · h∘g dλ.
4. Where T(g(a)) = range Dg(a): DΦ(a) = DF(g(a))∘Dg(a) (F = G near g(a)), and normDet_comp + normDet_sq_eq_det_gram give J_Φ(a) = J_T(g(a))·J_g(a).
5. The injective area formula for g with the arbitrary weight J_T·h gives ∫_{g(A)} J_T h dH^n = ∫_A J_g·J_T∘g·h∘g dλ = ∫_A J_Φ · h∘g dλ.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project; project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); sed -n 1,457p GMT/Ch07/Contract.lean; python3 -I read of the node's parent-child-handoff.json and parent decomposition-v3.json`
- `lake env lean /tmp/caf_probe/Probe.lean (import GMT.Ch07.Submission, contract scope): LinearMap.normDet, Poincare.SimonGMT.Chapter02.areaJacobianAt, Poincare.SimonGMT.Chapter02.weightedAreaFiberSum, LinearMap.euclideanHausdorffMeasure_image unknown; LipschitzOnWith.extend_finite_dimension, ContDiffOn.exists_lipschitzOnWith, Besicovitch.ae_tendsto_measure_inter_div, LipschitzWith.ae_differentiableAt, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Poincare.SimonGMT.Chapter03.blowUpMap, stdOrthonormalBasis, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le available`
- `grep -n 'theorem weighted_area_formula_lipschitz_fiberSum|theorem aemeasurable_weightedAreaFiberSum_lipschitz|theorem weighted_area_formula_lipschitz_injOn|def areaRegularSet|theorem area_image_compl_regularSet_eq_zero|theorem measurable_areaJacobianAt|theorem weightedAreaFiberSum_iUnion|def weightedAreaFiberSum|def areaJacobianAt|theorem HasApproximateTangentSpaceAt.unique|theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn|theorem simon_theorem_3_6|def dimensionalUpperDensity|theorem measure_toOuterMeasure_isBorelRegular|simonAreaNormalization' -r /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT`
- `grep -rn 'theorem normDet_comp|theorem normDet_sq_eq_det_gram|theorem euclideanHausdorffMeasure_image|theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem lintegral_sum_measure|theorem restrict_iUnion|theorem lintegral_tsum|protected theorem tsum_sigma.|def unionEqSigmaOfDisjoint|theorem restrict_congr_set|theorem restrict_apply.|theorem ae_restrict_iff.|theorem ae_restrict_of_ae_restrict_of_subset|theorem ContDiffOn.contDiffAt|theorem ContDiffAt.differentiableAt|def gram|theorem isOpen_iUnion_countable|theorem countable_cover_nhdsWithin' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `python3 -I scans of /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json (720 nodes): accepted nodes (status accepted, candidate_commit set) whose lean_statement mentions HasApproximateTangentSpaceAt, approxTangentPlane, LipschitzWith/LipschitzOnWith, ContDiffOn, volume-null images or fibre tsums; statuses of dpf_rectifiable_bilipschitz_pieces, doraggt_ae_approxTangent_transfer, ptd_piece_image_measurable_ae_pullback, dpf_itt_approxTangentPlane_eq (accepted), dpf_approxTangent_ae_bilipschitz_piece (speculative-ready), ptd_piece_image_approxTangent_ae (waiting-children), pit_* (decomposing), dimred_rpd_bilipschitz_image_measure, doraggt_ae_rescaled_lebesgue_point, dorwbl_diff_quotient_tendstoUniformlyOn (accepted)`
- `cat nodes/*/parent-supplied-natural-proof.md of the four reused nodes and of doraggt_local_density_zero, doraggt_approxTangent_iff_of_density_zero; git show a2ba78f:GMT/Ch07/Submission.lean (imports, accepted declaration)`
- `grep -c idtp_caf_ dag.json DAG.md dag.mmd issue-workers.json; grep -rl idtp_caf_ nodes/; git for-each-ref (3388 refs) | xargs git grep -l idtp_caf_ -- GMT (all no match)`
- `sed -n on /runtime/flows/gmt-claude-ebe9113f52d5/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, child id mapping by lean name, _install_parent_supplied_child_handoff early return for accepted nodes, accepted-child overlay of depends_on) and store.py ensure; verifier/gmt-compare.py child_modules and contract_scope`
- `python3 -I /tmp/caf_scripts/assemble.py (verifier/lean_contract.py validate_lean_statement on all 10 child statements)`
- `lake env lean /tmp/caf_dec/Stmts.lean (10 stubs elaborate); lake env lean /tmp/caf_dec/Assembly.lean (#print axioms caf_parent_check, caf_Dprime_check: propext, sorryAx, Classical.choice, Quot.sound)`
- `independent reviewer subagent: /tmp/caf_review/Check.lean and CheckAx.lean (child stubs as named axioms; per-theorem axiom dependencies)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3c1713cbf6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6e2110e6b7/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-cda4d660ba/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-c5809c1d90/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-e483a373f0/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-tan-cd2837f661/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Disjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-ebe9113f52d5/_recursive_lean/runtime.py`
- `/tmp/caf_dec/Assembly.lean`
- `/tmp/caf_dec/subproblems.json`

Pins match. The snapshot manifest has project b4d606d (the workspace HEAD) and mathlib 25730c7c. Contract.lean and Submission.lean are byte-identical.

Library support.
- SimonGMT provides the Euclidean-domain Lipschitz area formulas: weighted_area_formula_lipschitz_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitz, and weighted_area_formula_lipschitz_injOn with arbitrary weights.
- SimonGMT also provides areaRegularSet with its null-image lemma, measurable_areaJacobianAt, euclideanHausdorffMeasure_image_le_of_lipschitzOn, HasApproximateTangentSpaceAt.unique, simon_theorem_3_6 and measure_toOuterMeasure_isBorelRegular.
- Mathlib provides normDet_comp, normDet_sq_eq_det_gram, euclideanHausdorffMeasure_image_eq_normDet_mul_volume, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Besicovitch density, Lebesgue differentiation, Lipschitz extension, ContDiffOn.exists_lipschitzOnWith, restrict_iUnion and lintegral_sum_measure (no measurability needed).

Statement scope. normDet, areaJacobianAt and weightedAreaFiberSum are not in the contract's import closure. The child statements therefore use the parent's Gram-determinant and subtype-tsum forms; child proofs may add imports, as accepted candidates already do.

Reuse.
- Four exactly matching declarations are comparator-accepted and are reused with byte-identical types: dpf_rectifiable_bilipschitz_pieces, doraggt_ae_approxTangent_transfer, ptd_piece_image_measurable_ae_pullback and dpf_itt_approxTangentPlane_eq.
- The runtime maps these to the existing nodes and overlays their candidate commits for dependents.
- The related unaccepted nodes ptd_piece_image_approxTangent_ae, dpf_approxTangent_ae_bilipschitz_piece and pit_* cannot be shared, so fresh idtp_caf_* names are used. These names are unused everywhere.

Lean checks.
- All 10 child types elaborate in the contract scope.
- The assembly proves the exact frozen parent type from the 10 child stubs. Its axioms are propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only.
- The step-3 glue child follows from its four siblings.
