# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.flat_tangent_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.flat_tangent_density-a1.plane_ball_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Parent proof Step 1 ("Plane balls"): a linear isometry ι : ℝ^m → P carries L^m to H^m⌞P and ι^{-1}(P ∩ B_s(0)) = B_s(0), hence H^m(P ∩ B_s(0)) = ω_m s^m. It is stated here for open balls and an arbitrary m-dimensional linear subspace Q of an arbitrary ℝ^N (the siblings apply it with N = m + 1 and Q = P = (span{v})^⊥). Simon Ch. 3, Remark 1.5(3) (chapter-03.txt lines 91–107) uses that H^n restricted to an n-plane is n-dimensional Lebesgue measure.

Fix N, m, a linear subspace Q ⊆ ℝ^N with finrank Q = m, and a real s > 0. Write L^m := volume on Euclid m, so ω_m = unitBallVolume m = L^m(B_1(0)).

1. A linear isometry onto Q. With the inner product inherited from ℝ^N, Q is an m-dimensional real inner product space, so it has an orthonormal basis indexed by Fin m (Lean: (stdOrthonormalBasis ℝ Q).reindex (finCongr hm); for m = 0 it is the empty family). Its coordinate map e : Q → ℝ^m = Euclid m is a linear isometric isomorphism. Let ι : ℝ^m → ℝ^N be e^{-1} followed by the inclusion Q ↪ ℝ^N (Lean: Q.subtypeₗᵢ.comp e.symm.toLinearIsometry). Then ι is linear, ‖ι(a)‖ = ‖a‖ for every a (so ι is an isometry of metric spaces), ι(a) ∈ Q for every a, and ι(e(z)) = z for every z ∈ Q.

2. Image of the ball. ι(B_s(0)) = Q ∩ B_s(0). (⊆) If a ∈ ℝ^m and ‖a‖ < s, then ι(a) ∈ Q and ‖ι(a)‖ = ‖a‖ < s. (⊇) If z ∈ Q and ‖z‖ < s, put a := e(z) ∈ ℝ^m; then ‖a‖ = ‖z‖ < s and ι(a) = z.

3. Isometry invariance. μHE[m] is defined from the metric alone (it is a fixed positive multiple of the m-dimensional Hausdorff measure), so for the isometry ι and every S ⊆ ℝ^m, μHE[m](ι(S)) = μHE[m](S), the right side computed in ℝ^m (Mathlib Isometry.euclideanHausdorffMeasure_image). With 2: H^m(Q ∩ B_s(0)) = μHE[m](ι(B_s(0))) = μHE[m](B_s(0)), the last ball being the ball of ℝ^m.

4. Normalization. On ℝ^m = Euclid m, μHE[m] = L^m (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). Hence H^m(Q ∩ B_s(0)) = L^m(B_s(0)).

5. Haar scaling. L^m is an additive Haar measure on Euclid m and finrank ℝ (Euclid m) = m (finrank_euclideanSpace_fin), so for s > 0, L^m(B_s(0)) = ofReal(s^m) · L^m(B_1(0)) = ofReal(s^m) · ω_m (Mathlib Measure.addHaar_ball_of_pos; valid for every s > 0 and every m, including m = 0, where both sides equal ω_0).

6. Conclusion. By 3–5, H^m(Q ∩ B_s(0)) = ofReal(s^m) · ω_m = unitBallVolume m * ENNReal.ofReal (s ^ m), by commutativity of multiplication in [0, ∞]. ∎

Formalization notes (complete proof compiled in this session after import GMT.Ch07.Submission, /tmp/ftd3-check/Full.lean): let e : Q ≃ₗᵢ[ℝ] Euclid m := ((stdOrthonormalBasis ℝ Q).reindex (finCongr hm)).repr; let ι : Euclid m →ₗᵢ[ℝ] Euclid N := Q.subtypeₗᵢ.comp e.symm.toLinearIsometry; prove himage : ι '' ball 0 s = (Q : Set (Euclid N)) ∩ ball 0 s by ext, mem_ball_zero_iff, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map and LinearIsometryEquiv.symm_apply_apply; then rw [← himage, ι.isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_ball_of_pos (volume : Measure (Euclid m)) 0 hs, finrank_euclideanSpace_fin, unitBallVolume]; exact mul_comm _ _. Do not compute with `volume` on the subtype ↥Q (instance search would pick Subtype.measureSpace, the comap of Lebesgue measure on ℝ^N, which is not H^m⌞Q).

## Key steps

1. An orthonormal basis of Q (finrank Q = m) gives a linear isometry ι : ℝ^m → ℝ^N with range Q.
2. ι(B_s(0)) = Q ∩ B_s(0) because ‖ι a‖ = ‖a‖.
3. μHE[m] is isometry invariant and equals Lebesgue measure on ℝ^m = Euclid m.
4. Haar scaling: L^m(B_s(0)) = ofReal(s^m) · L^m(B_1(0)) = ofReal(s^m) · ω_m; commute the product.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean`
- `cmp <snapshot>/mathlib/<f> .lake/packages/mathlib/<f> for 14 cited Mathlib files (Geometry/Euclidean/Volume/Measure, Lebesgue/EqHaar, Bochner/{Basic,Set}, Lebesgue/{Markov,Basic}, IntegrableOn, MetricSpace/HausdorffDistance, Instances/ENNReal/Lemmas, InnerProductSpace/{Projection/FiniteDimensional,Orthogonal,Basic}, Basic/ENNReal/{Inv,Basic}): all identical`
- `rg -n "theorem (Isometry\.euclideanHausdorffMeasure_image|EuclideanSpace\.euclideanHausdorffMeasure_eq_volume|addHaar_ball_of_pos|IntegrableOn\.of_forall_sdiff_eq_zero|integral_mono_of_nonneg|integral_undef|integral_indicator_const|mem_orthogonal_singleton_iff_inner_left|abs_real_inner_le_norm|infDist_zero_of_mem|div_le_of_le_mul|lt_iff_exists_real_btwn|mul_meas_ge_le_lintegral₀|ofReal_integral_eq_lintegral_ofReal|lintegral_indicator_one_le|finrank_orthogonal_span_singleton|tendsto_nhds_zero|infDist_lt_iff)\b" <snapshot>/mathlib/Mathlib`
- `grep -n "μHE\|notation\|euclideanHausdorffMeasure_image" <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 440,452p <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `python3 scans of dag.json: target node (status decomposing, 'subproblem decomposition attempt 3', children []); lean_name reservations matching ftd|flat_tangent|subspace_ball|plane_ball|rdo_dg; status/candidate_commit of codim1_subspace_ball_euclideanHausdorff (accepted, 6fadc8de) and idtp_tdc_subspace_ball_measure (accepted, a029156d); collision check of the five fresh names (0 hits)`
- `rg/grep -rn codim1_rdo_dg_ftd_ over GMT, .lake/packages/simongmt, <snapshot>, run-directory JSON (only this node's decomposition-v1/v2 drafts); git log --all --oneline -S codim1_rdo_dg_ftd_ (no commits)`
- `sed -n runtime.py _existing_lean_name_problem/_accepted_checkpoint/_decompose/_reference_use_problem and models.py Subproblem/Decomposition/ScopedDecomposition (live flow gmt-claude-9a0895c8c5e1); swarm-project.json (max_depth 6, max_children 12)`
- `sed -n 85,110p book/chapter-03.txt (Simon Ch. 3, Remark 1.5(3)); cat this node's parent-child-handoff.json, parent-supplied-plan.md, decomposition-v1.json, decomposition-v2.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json`
- `lake env lean -DautoImplicit=false /tmp/ftd3-check/Types.lean (5 child types + exact parent assembly; sorry warnings only)`
- `lake env lean -DautoImplicit=false /tmp/ftd3-check/Full.lean (complete proofs of all children + parent; #print axioms = [propext, Classical.choice, Quot.sound])`
- `lake env lean -DautoImplicit=false /tmp/ftd3-check/Inst.lean (instance audit: BorelSpace (Euclid N), unitBallVolume rfl, inner product and smul coordinatewise, pp.explicit of μHE[m])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96896b0cee/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96896b0cee/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96896b0cee/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-96896b0cee/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/tmp/ftd3-check/Types.lean`
- `/tmp/ftd3-check/Full.lean`
- `/tmp/ftd3-check/Inst.lean`

Pins match: snapshot manifest project b4d606db / Mathlib 25730c7c equal workspace HEAD and .lake/packages/mathlib (simongmt 2b366308); snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…); the 14 cited Mathlib files are byte-identical to the snapshot. The snapshot supplies every library fact the children use: Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:131,187), Measure.addHaar_ball_of_pos (Lebesgue/EqHaar.lean:445), mul_meas_ge_le_lintegral₀ (Lebesgue/Markov.lean:52), ofReal_integral_eq_lintegral_ofReal and integral_undef (Bochner/Basic.lean), lintegral_indicator_one_le (Lebesgue/Basic.lean:563), IntegrableOn.of_forall_sdiff_eq_zero, infDist_lt_iff (HausdorffDistance.lean:513), ENNReal.tendsto_nhds_zero (ENNReal/Lemmas.lean:237), finrank_orthogonal_span_singleton (Projection/FiniteDimensional.lean:125). No snapshot declaration states the parent or any child, so none can be reused. Two plane-ball lemmas exist in other branches (codim1_subspace_ball_euclideanHausdorff, idtp_tdc_subspace_ball_measure). Per the correction, neither is reused: the plane-ball child gets the fresh name codim1_rdo_dg_ftd_plane_ball_measure. All five fresh names have 0 hits in the 1194-node DAG, GMT/, SimonGMT, the snapshot and the git history. Lean checks: Types.lean elaborates all five child types and proves the exact frozen parent type from them; Full.lean proves all five children and the parent sorry-free with axioms [propext, Classical.choice, Quot.sound]; Inst.lean confirms the Euclidean/Borel instances behind μHE[m], μ, unitBallVolume and inner.
