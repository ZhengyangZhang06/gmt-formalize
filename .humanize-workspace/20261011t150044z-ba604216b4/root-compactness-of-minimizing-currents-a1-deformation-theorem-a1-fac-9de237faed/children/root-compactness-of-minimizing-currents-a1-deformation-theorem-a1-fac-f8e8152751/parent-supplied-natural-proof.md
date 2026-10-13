# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1.local_plane_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4(iii) of the parent proof: the blow-ups of the carrier agree with V_p on B(0, R) for small r, so V_p is the approximate tangent space. Here it is stated for an arbitrary set M and subspace V. It generalizes SimonGMT's hasApproximateTangentSpaceAt_submodule (Poincare/SimonGMT/Chapter03/Rectifiable.lean), which is the case M = V, x ∈ V.

Notation. η_{x,r}(y) := blowUpMap x r y = r⁻¹ • (y − x); Hⁿ := μHE[n] on ℝ^P. By definition, HasApproximateTangentSpaceAt n M x V means: finrank ℝ V = n, and for every f ∈ C_c(ℝ^P, ℝ), r ↦ ∫_{η_{x,r}(M)} f dHⁿ tends to ∫_V f dHⁿ along 𝓝[>] 0.

1. finrank ℝ V = n is a hypothesis.
2. Fix f ∈ C_c(ℝ^P, ℝ). Its topological support is compact, hence bounded, so tsupport f ⊆ B̄(0, R₀) for some R₀ ∈ ℝ. Put R := max(R₀, 0) + 1, so R > 0 and R > R₀. If |y| ≥ R then y ∉ B̄(0, R₀) ⊇ tsupport f, hence f(y) = 0 (image_eq_zero_of_notMem_tsupport). So f vanishes outside the open ball B := B(0, R).
3. Claim: if 0 < r < δ/R (equivalently 0 < r and rR < δ), then B ∩ η_{x,r}(M) = B ∩ V.
 (⊆) Let y ∈ B with y = r⁻¹(z − x) for some z ∈ M. Then z − x = r y, so dist(z, x) = |z − x| = r|y| < rR < δ. By the hypothesis, z ∈ M gives z − x ∈ V. Hence y = r⁻¹(z − x) ∈ V.
 (⊇) Let y ∈ B ∩ V and set z := x + r y. Then z − x = r y ∈ V, since V is a subspace, and dist(z, x) = r|y| < rR < δ. So z ∈ M by the hypothesis. Moreover η_{x,r}(z) = r⁻¹(r y) = y because r ≠ 0. So y ∈ η_{x,r}(M).
4. Localization. For every set S ⊆ ℝ^P, measurable or not, ∫_S f dHⁿ = ∫_{B∩S} f dHⁿ. Indeed, B is Borel, so (Hⁿ⌞S)⌞B = Hⁿ⌞(B ∩ S) (Measure.restrict_restrict). Since f = 0 off B, ∫ f d((Hⁿ⌞S)⌞B) = ∫ f d(Hⁿ⌞S) (setIntegral_eq_integral_of_forall_compl_eq_zero).
5. For 0 < r < δ/R, steps 4, 3 and 4 again give
 ∫_{η_{x,r}(M)} f dHⁿ = ∫_{B∩η_{x,r}(M)} f dHⁿ = ∫_{B∩V} f dHⁿ = ∫_V f dHⁿ.
6. Since δ/R > 0, the interval (0, δ/R) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT). So r ↦ ∫_{η_{x,r}(M)} f dHⁿ is eventually equal along 𝓝[>] 0 to the constant ∫_V f dHⁿ, and hence tends to it (tendsto_const_nhds.congr'). As f was arbitrary, HasApproximateTangentSpaceAt n M x V holds. ∎ No measurability of M is used. For n = 0 and V = {0} the argument is identical.

Lean note (checked): a Lean proof of exactly this statement compiles in the comparator scope with only standard axioms, following steps 1–6 literally. blowUpMap lives in Poincare.SimonGMT.Chapter03 and is not opened by the contract, so write Poincare.SimonGMT.Chapter03.blowUpMap. Also, blowUpMap x r y = r⁻¹ • (y − x) holds by rfl.

## Key steps

1. tsupport f is compact, so f = 0 outside B(0, R) for some R > 0.
2. For 0 < r < δ/R, B(0,R) ∩ η_{x,r}(M) = B(0,R) ∩ V: |z − x| = r|η_{x,r}(z)| < δ, then apply the local hypothesis in both directions.
3. Restricting to the Borel ball does not change ∫ f, so ∫_{η_{x,r}(M)} f dHⁿ = ∫_V f dHⁿ for all small r.
4. The map is eventually constant along 𝓝[>]0, which gives the limit; finrank V = n is a hypothesis.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch07/Contract.lean against the workspace Contract.lean (identical) and the workspace Contract.lean against Submission.lean (identical)`
- `rg -n 'theorem (Isometry\.euclideanHausdorffMeasure_image|Isometry\.map_euclideanHausdorffMeasure|EuclideanSpace\.euclideanHausdorffMeasure_eq_volume)|theorem isClosedEmbedding|Topology\.IsClosedEmbedding\.measurableEmbedding|theorem restrict_map \(μ|MeasurableEmbedding\.integral_map|setIntegral_eq_integral_of_forall_compl_eq_zero|theorem restrict_restrict \(hs|integral_biUnion_finset|lintegral_biUnion_finset|Submodule\.mem_span_range_iff_exists_fun|finrank_span_eq_card|theorem le_opNorm \(f : E \[⋀|Continuous\.integrable_of_hasCompactSupport|protected theorem ite|ae_restrict_of_forall_mem|Orthonormal\.comp|theorem norm_apply_le|basisFun_apply' mathlib/Mathlib -g '*.lean'`
- `rg -n 'IMRep|hasApproximateTangentSpaceAt|cmcdtfr|polyhedral|IsLatticeChain' project/GMT -g '*.lean'`
- `rg -n 'cmcdtfrpi_|isometry_image_integral|local_plane_tangent|coord_plane_orientation|face_union_local_plane|finite_piece_imrep' project mathlib/Mathlib lake-packages-25730c7c/simongmt -g '*.lean' (no match)`
- `python3 scan of dag.json: lean_name collisions with prefix cmcdtfrpi_ (none among 1619 nodes); identical or overlapping lean_statements (none; only dor_lmb_fc_dtop_isometric_pushforward_im mentions Isometry, a different statement)`
- `grep in lake-packages-25730c7c/simongmt Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, countablyRectifiable_range, countablyRectifiable_iUnion, blowUpMap, HasApproximateTangentSpaceAt, hasApproximateTangentSpaceAt_submodule) and Chapter06/{Forms,Currents,Mass}.lean (DifferentialForm, IsTestForm, TestFormOn, GeometricCurrentOn.ext, zero_apply, massOn, mass)`
- `python3 verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') -> replayed scope used for all Lean checks`
- `lake env lean /tmp/pimdecomp/lean/Types.lean (five child types elaborate); lake env lean /tmp/pimdecomp/lean/Assembly.lean (PIM.assembly: child types + frozen cmcdtfr_face_geometry type imply the selected frozen type; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/pimdecomp/lean/Small.lean and /tmp/pimdecomp/lean/Big.lean (all five children proved against their exact strings; standard axioms; instance checks); lake env lean /tmp/pimdecomp/lean/Inst*.lean (ContinuousAdd (MultiVector P k) fails to synthesize; the StronglyMeasurable.ite list fold works)`
- `lake env lean /tmp/pimdecomp/lean/Final.lean (regenerated from the final JSON strings: five child proofs, FINAL.assembly, and FINAL.parent_from_children (frozen face_geometry type ⊢ selected frozen type); no sorry; only propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-9de237faed/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-297ffaa421/decomposition-v1.json`
- `/tmp/pimdecomp/lean/Types.lean`
- `/tmp/pimdecomp/lean/Assembly.lean`
- `/tmp/pimdecomp/lean/Small.lean`
- `/tmp/pimdecomp/lean/Big.lean`
- `/tmp/pimdecomp/lean/Final.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace, and Submission.lean equals the contract. Its project tree has no reusable proofs: Ch06/Contract.lean only defines lattice chains (IsLatticeChain, main_theorem := by sorry), and Ch07 only defines IMRep. Mathlib supplies every tool used by the children: isometry invariance of μHE and μHE = volume on Euclid d (Geometry/Euclidean/Volume/Measure.lean); Isometry.isClosedEmbedding; IsClosedEmbedding.measurableEmbedding; MeasurableEmbedding.restrict_map and integral_map; restrict_restrict; setIntegral_eq_integral_of_forall_compl_eq_zero; integral_biUnion_finset; lintegral_biUnion_finset; Submodule.mem_span_range_iff_exists_fun; finrank_span_eq_card; ContinuousAlternatingMap.le_opNorm; Orthonormal.comp; EuclideanSpace.basisFun_apply; PiLp.norm_apply_le; Continuous.integrable_of_hasCompactSupport; StronglyMeasurable.ite; ae_restrict_of_forall_mem. SimonGMT Chapter03/Rectifiable.lean supplies CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt and the flat model hasApproximateTangentSpaceAt_submodule, which local_plane_tangent localizes. Mathlib has no polyhedral-chain or IMRep material, and no declaration or DAG node uses the prefix cmcdtfrpi_. Lean checks in the replayed comparator scope: all five child types elaborate; the assembly derives the selected frozen type from them and the frozen cmcdtfr_face_geometry type; all five children were proved against their exact strings; Final.lean re-checks everything from the final JSON strings. Every check uses only propext, Classical.choice and Quot.sound. Instance finding: ContinuousAdd (MultiVector P k) fails to synthesize, so finite_piece_imrep's orientation is a list fold, not a Finset sum.
