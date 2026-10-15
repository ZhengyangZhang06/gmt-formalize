# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.flat_tangent_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.flat_tangent_density-a1.ball_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Ch. 3, Remark 1.5(3) (chapter-03.txt lines 91–107), first assertion (choose f ∈ C_c^0 with f ≡ 1 on B_1(0), f ≡ 0 off B_{1+ε}(0), and let ε ↓ 0), applied to μ instead of H^n⌞M. This is parent proof Steps 1–2 with all details filled in. The parent bounds I(f₊) ≤ H^m(P ∩ B̄_{1+ε}(0)) and I(f₋) ≥ H^m(P ∩ B̄_{1−ε}(0)); here the open plane balls B_{1+ε}(0) and B_{1−ε}(0) are used instead (same values ω_m(1 ± ε)^m), so that the sibling plane_ball_measure (Submission.codim1_rdo_dg_ftd_plane_ball_measure, open balls) applies directly; and instead of "0 < r ≤ r₀/2" the sibling test lemmas supply the eventual radius restriction.

Notation. E := ℝ^{m+1}, P := (span{v})^⊥, H^m := μHE[m], ν := H^m⌞P (= μHE[m].restrict P), I(g) := ∫_P g dH^m = ∫ g dν, I_r(g) := r^{-m} ∫ g(r^{-1}(z − y)) dμ(z). The hypothesis says I_r(f) → I(f) as r ↓ 0 for every continuous compactly supported f. Fix r₀ > 0 with μ(B̄_{r₀}(y)) < ∞. (The hypothesis m ≥ 1 is not needed in this part.)

0. Preliminaries.
(a) v ≠ 0 because ‖v‖ = 1, and finrank E = m + 1; so the orthogonal complement P of the line span{v} has finrank P = m (Submodule.finrank_orthogonal_span_singleton).
(b) ω_m = L^m(B_1(0)) ∈ (0, ∞): the open unit ball of ℝ^m is nonempty and open, so it has positive Haar measure, and it is bounded, so its measure is finite. Put ω := toReal(ω_m) > 0; then ω_m = ofReal(ω).
(c) Plane balls. For s > 0, ν(B_s(0)) = H^m(B_s(0) ∩ P) (B_s(0) is open, hence measurable) = H^m(P ∩ B_s(0)) = ω_m · ofReal(s^m) = ofReal(ω s^m), by the sibling plane_ball_measure applied with N := m + 1, the same m, Q := P (finrank P = m by (a)) and s. In particular ν(B_s(0)) < ∞, the indicator 1_{B_s(0)} is ν-integrable, and ∫ 1_{B_s(0)} dν = toReal(ν(B_s(0))) = ω s^m.

1. Plane integral bounds.
(U) Let s > 0 and g : E → ℝ with 0 ≤ g ≤ 1 and g(w) = 0 whenever ‖w‖ ≥ s. Then g ≤ 1_{B_s(0)} pointwise (if ‖w‖ < s, g(w) ≤ 1; otherwise g(w) = 0). Since g ≥ 0 and 1_{B_s(0)} is ν-integrable, monotonicity of the Bochner integral (valid also if g is not integrable, its integral then being 0 ≤ the right side) gives I(g) ≤ ∫ 1_{B_s(0)} dν = ω s^m.
(L) Let s, S > 0 and g : E → ℝ continuous with 0 ≤ g ≤ 1, g(w) ≥ 1 whenever ‖w‖ < s, and g(w) = 0 whenever ‖w‖ ≥ S. Then g is ν-integrable: it is measurable, |g| ≤ 1 on B_S(0), which has finite ν-measure by 0(c), and g vanishes outside B_S(0). Also 1_{B_s(0)} ≤ g pointwise. Hence ω s^m = ∫ 1_{B_s(0)} dν ≤ I(g).

2. Cutoffs. For reals a < b let g_{a,b}(w) := min(1, max(0, (b − ‖w‖)/(b − a))). Then g_{a,b} is continuous, 0 ≤ g_{a,b} ≤ 1, g_{a,b}(w) = 1 if ‖w‖ ≤ a (then (b − ‖w‖)/(b − a) ≥ 1), and g_{a,b}(w) = 0 if ‖w‖ ≥ b (then (b − ‖w‖)/(b − a) ≤ 0). Hence g_{a,b} vanishes outside the compact ball B̄_b(0) and has compact support. For 0 < ε < 1, f₊ := g_{1,1+ε} and f₋ := g_{1−ε,1} are the parent's functions.

3. Set identities. For r > 0 and z ∈ E, ‖r^{-1}(z − y)‖ = r^{-1}‖z − y‖; hence {z : r^{-1}(z − y) ∈ B̄_1(0)} = B̄_r(y) and {z : r^{-1}(z − y) ∈ B_1(0)} = B_r(y).

4. Upper bound. Claim: for every real C > 1, eventually as r ↓ 0, μ(B̄_r(y)) ≤ ofReal(ω C r^m). Since t ↦ (1 + t)^m is continuous with value 1 at t = 0, choose ε > 0 with (1 + ε)^m < C. By 1(U) with s := 1 + ε and g := f₊ (f₊ vanishes for ‖w‖ ≥ 1 + ε), I(f₊) ≤ ω(1 + ε)^m < ωC, using ω > 0. Apply the sibling test_upper_bound (Submission.codim1_rdo_dg_ftd_test_upper_bound) with N := m + 1, the same m, μ, y, f := f₊, A := B̄_1(0), L := I(f₊), L' := ωC and the given r₀: f₊ is continuous, compactly supported and ≥ 0, f₊ = 1 ≥ 1 on B̄_1(0) (‖w‖ ≤ 1), I_r(f₊) → I(f₊) by hypothesis, and I(f₊) < ωC. It gives: eventually μ({z : r^{-1}(z − y) ∈ B̄_1(0)}) ≤ ofReal(ωC r^m). Intersecting with the eventual set {r > 0} and using 3, eventually μ(B̄_r(y)) ≤ ofReal(ωC r^m).

5. Lower bound. Claim: for every real c < 1, eventually ofReal(ω c r^m) ≤ μ(B_r(y)). Since t ↦ (1 − t)^m is continuous with value 1 at t = 0, choose ε ∈ (0, 1) with c < (1 − ε)^m. By 1(L) with s := 1 − ε > 0, S := 1 and g := f₋ (f₋ = 1 when ‖w‖ < 1 − ε, f₋ = 0 when ‖w‖ ≥ 1), I(f₋) ≥ ω(1 − ε)^m > ωc. Apply the sibling test_lower_bound (Submission.codim1_rdo_dg_ftd_test_lower_bound) with N := m + 1, f := f₋, A := B_1(0), L := I(f₋) and L' := ωc: f₋ is continuous with 0 ≤ f₋ ≤ 1, f₋(w) = 0 for w ∉ B_1(0) (i.e. ‖w‖ ≥ 1), I_r(f₋) → I(f₋) by hypothesis (f₋ has compact support), and ωc < I(f₋). It gives: eventually ofReal(ωc r^m) ≤ μ({z : r^{-1}(z − y) ∈ B_1(0)}), which by 3 equals μ(B_r(y)) for r > 0.

6. Ratio identity. Let r > 0 and c ≥ 0. Then ofReal(ω c r^m) = ofReal(c · (ω r^m)) = ofReal(c) · ofReal(ω) · ofReal(r^m) = ofReal(c) · (ω_m · ofReal(r^m)), and ω_m · ofReal(r^m) ∈ (0, ∞). Hence ofReal(ω c r^m)/(ω_m · ofReal(r^m)) = ofReal(c). Division by a fixed element of [0, ∞] is monotone in the numerator, and μ(B_r(y)) ≤ μ(B̄_r(y)).

7. Conclusion. In the order topology of [0, ∞], X_r → 1 iff for every a < 1 eventually a < X_r, and for every b > 1 eventually X_r < b.
- Let b > 1. Choose a real C ≥ 0 with 1 < ofReal(C) < b; then C > 1. By 4 and 6, eventually μ(B_r(y))/(ω_m r^m) ≤ μ(B̄_r(y))/(ω_m r^m) ≤ ofReal(ωCr^m)/(ω_m r^m) = ofReal(C) < b.
- Let a < 1. Choose a real c ≥ 0 with a < ofReal(c) < 1; then c < 1. By 5 and 6, eventually a < ofReal(c) = ofReal(ωcr^m)/(ω_m r^m) ≤ μ(B_r(y))/(ω_m r^m) ≤ μ(B̄_r(y))/(ω_m r^m).
Hence μ(B̄_r(y))/(ω_m r^m) → 1 and μ(B_r(y))/(ω_m r^m) → 1 as r ↓ 0, where ω_m r^m denotes unitBallVolume m * ENNReal.ofReal (r ^ m). ∎

Formalization notes (compiled in this session using only the frozen sibling statements, /tmp/ftd3-check/Full.lean): Step 0(a) haveI : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩ and Submodule.finrank_orthogonal_span_singleton hv0; 0(b) measure_ball_pos volume 0 one_pos and measure_ball_lt_top.ne; 0(c) rw [Measure.restrict_apply measurableSet_ball, inter_comm, Submission.codim1_rdo_dg_ftd_plane_ball_measure (m + 1) m _ hPdim s hs, hωeq, ← ENNReal.ofReal_mul hωpos.le]; integral_indicator_const _ measurableSet_ball with measureReal_def and ENNReal.toReal_ofReal; (integrableOn_const hfinite).integrable_indicator measurableSet_ball. Step 1: integral_mono_of_nonneg for (U), integral_mono for (L), with Measure.integrableOn_of_bounded, IntegrableOn.of_forall_sdiff_eq_zero MeasurableSet.univ and integrableOn_univ. Step 2: HasCompactSupport.intro (isCompact_closedBall 0 b). Step 3: simp only [mem_setOf_eq, mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_le_iff₀ hr, mul_one] (mem_ball / inv_mul_lt_iff₀ for open balls; mem_setOf_eq is deprecated in this Mathlib in favour of mem_ofPred_eq but still compiles with a warning). Steps 4–5: continuity of (1 ± t)^m by fun_prop, then ((hcont.eventually (gt_mem_nhds hC)).and self_mem_nhdsWithin).exists, resp. (lt_mem_nhds hc) with Ioo_mem_nhdsGT one_pos; the siblings are applied as Submission.codim1_rdo_dg_ftd_test_upper_bound (m + 1) m μ y f₊ (closedBall 0 1) _ (ω * C) hfin … and Submission.codim1_rdo_dg_ftd_test_lower_bound (m + 1) m μ y f₋ (ball 0 1) _ (ω * c) …. Steps 6–7: ENNReal.ofReal_mul, ENNReal.mul_div_cancel_right, ENNReal.div_le_div_right, ENNReal.lt_iff_exists_real_btwn, ENNReal.ofReal_lt_one, ENNReal.one_lt_ofReal and tendsto_order.

## Key steps

1. finrank P = m, 0 < ω_m < ∞, and by the sibling plane_ball_measure (H^m⌞P)(B_s(0)) = ofReal(ω s^m) for s > 0.
2. Plane bounds: I(g) ≤ ω s^m if 0 ≤ g ≤ 1 vanishes for ‖w‖ ≥ s; I(g) ≥ ω s^m if g is continuous, 0 ≤ g ≤ 1, g ≥ 1 on B_s(0), and g vanishes for ‖w‖ ≥ S.
3. Radial cutoffs f₊ = g_{1,1+ε} ≥ 1 on B̄_1(0) and f₋ = g_{1−ε,1} vanishing off B_1(0).
4. Sibling test_upper_bound with f₊, A = B̄_1(0): eventually μ(B̄_r(y)) ≤ ofReal(ωC r^m) for every C > 1.
5. Sibling test_lower_bound with f₋, A = B_1(0): eventually ofReal(ωc r^m) ≤ μ(B_r(y)) for every c < 1.
6. Divide by ω_m r^m (ratio identity) and apply tendsto_order, using μ(B_r) ≤ μ(B̄_r).

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
