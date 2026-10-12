# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.support_lower_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Sibling map: tangent_lower_density — Submission.doragm_approxTangent_lower_density.
Source: parent proof, Steps 4–5 (monotonicity; density ≥ 1 at approximate tangent points; upper semicontinuity of the density; support), in the form used by Step 6 (Simon Ch. 4, 3.8–3.11 and 4.10(1)). The upper-semicontinuity estimate (Simon 3.11: B_τ(y_j) ⊆ B_{τ+ε}(y)) and the support argument are combined into one contradiction argument, so the density Θ itself never has to be defined.
Notation: B̄_ρ(z) closed ball, B_ρ(z) open ball; f_z(ρ) := ofReal(e^{κρ}/ρⁿ)·μ(B̄_ρ(z)) ∈ [0, ∞]; ω_n := unitBallVolume n.
1. (Facts about μ.) (a) For every Borel set S, μ(S) = ∫⁻_{M∩S}θ dHⁿ ≥ Hⁿ(M ∩ S), because θ = R.mult is a positive integer, hence ≥ 1, on M (IMRep.mult_pos). (b) μ(K) < ∞ for every compact K ⊆ U (IMRep.locallyIntegrable_mult). (c) Let G be the set of x ∈ M at which M has an approximate tangent space Q (HasApproximateTangentSpaceAt n M x Q). By IMRep.orients and Hⁿ⌞M(ℝ^P ∖ M) = 0, Hⁿ⌞M-a.e. x lies in G; since μ ≪ Hⁿ⌞M (withDensity), μ(ℝ^P ∖ G) = 0.
2. (Contradiction hypothesis.) Fix y ∈ spt μ and t > 0 with B̄_t(y) ⊆ W, and suppose f_y(t) < ω_n.
3. (A slightly larger ball.) B̄_t(y) is compact and W is open, so B̄_{t+δ₀}(y) ⊆ W for some δ₀ > 0 (IsCompact.exists_cthickening_subset_open, cthickening_closedBall), and μ(B̄_{t+δ₀}(y)) < ∞ by 1(b). The balls B̄_{t+δ₀/(m+1)}(y), m ∈ ℕ, decrease with intersection B̄_t(y), so μ(B̄_{t+δ₀/(m+1)}(y)) → μ(B̄_t(y)) (continuity from above, tendsto_measure_iInter_atTop) and ofReal(e^{κt}/tⁿ)·μ(B̄_{t+δ₀/(m+1)}(y)) → f_y(t) < ω_n. Fix m such that, with δ := δ₀/(m + 1) ∈ (0, δ₀], b := ofReal(e^{κt}/tⁿ)·μ(B̄_{t+δ}(y)) < ω_n, and choose c ∈ [0, ∞] with b < c < ω_n.
4. (No good point near y.) Let x ∈ G with |x − y| < δ and let Q be an approximate tangent space of M at x. Then B̄_t(x) ⊆ B̄_{t+δ}(y) ⊆ W. By tangent_lower_density (n ≥ 1, c < ω_n), c·σⁿ ≤ Hⁿ(M ∩ B̄_σ(x)) for all sufficiently small σ > 0; fix such a σ with 0 < σ < t. Using e^{κσ} ≥ 1 (κ ≥ 0), 1(a), the monotonicity hypothesis at the centre x with radii σ < t (B̄_t(x) ⊆ W), and B̄_t(x) ⊆ B̄_{t+δ}(y):
   c = ofReal(1/σⁿ)·(c·ofReal(σⁿ)) ≤ ofReal(e^{κσ}/σⁿ)·Hⁿ(M ∩ B̄_σ(x)) ≤ f_x(σ) ≤ f_x(t) ≤ ofReal(e^{κt}/tⁿ)·μ(B̄_{t+δ}(y)) = b < c,
   a contradiction. Hence B_δ(y) ∩ G = ∅.
5. (Support.) By step 4, B_δ(y) ⊆ ℝ^P ∖ G, so μ(B_δ(y)) = 0 by 1(c). But y ∈ spt μ means μ(V) > 0 for every neighbourhood V of y (Measure.mem_support_iff_forall), and B_δ(y) is such a neighbourhood. This contradiction shows f_y(t) ≥ ω_n, i.e. ω_n ≤ ofReal(e^{κt}/tⁿ)·μ(B̄_t(y)). ∎
Reference: a Lean proof of exactly this statement, compiled during the decomposition review against import GMT.Ch07.Submission (axioms propext, Classical.choice, Quot.sound only), is in /tmp/mono-review/Full2.lean, theorem GMT.Ch07.MonoC6Check.child6_from_child5 (there the sibling statement is the hypothesis h5); it may be consulted if that file is available.

## Key steps

1. μ ≥ Hⁿ⌞M on Borel sets (θ ≥ 1 on M), μ is finite on compact subsets of U, and μ-a.e. point lies in M and has an approximate tangent plane.
2. Assume f_y(t) < ω_n; by continuity from above pick δ > 0 with b = e^{κt}t^{−n}μ(B̄_{t+δ}(y)) < c < ω_n.
3. For a good point x ∈ B_δ(y): tangent_lower_density, monotonicity at x on (σ, t) and B̄_t(x) ⊆ B̄_{t+δ}(y) give c ≤ b, a contradiction.
4. Hence μ(B_δ(y)) = 0, contradicting y ∈ spt μ.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project; project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical)`
- `rg -n -i 'monoton|radial|cutoff|density' project/GMT/Ch04/Submission.lean; rg -c sorry project/GMT/Ch0{3,4,5}/Submission.lean; rg -n doragm project (no match)`
- `rg -n 'def approxTangentPlane|def tangentialDivergence|def IMRep.firstVariation|def unitBallVolume|def IMRep.measure' project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le' mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean; rg -n 'theorem integral_withDensity_eq_integral_toReal_smul' mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `rg -n 'theorem cthickening_closedBall|exists_cthickening_subset_open' mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean mathlib/Mathlib/Topology/MetricSpace/Thickening.lean; rg -n 'theorem tendsto_measure_iInter_atTop|theorem tendsto_measure_iUnion_atTop' mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `rg -n 'theorem starProjection_orthogonal_val|theorem norm_starProjection_apply_le' mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean; rg -n 'lemma mem_support_iff_forall' mathlib/Mathlib/MeasureTheory/Measure/Support.lean; rg -n 'one_of_one_le|zero_of_nonpos|protected theorem monotone|protected theorem contDiff' mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n 'le_lintegral_ofReal|ofReal_integral_le' mathlib/Mathlib (no match); rg -n 'theorem integral_eq_lintegral_of_nonneg_ae|theorem ofReal_toReal_le' mathlib/Mathlib; rg -n 'euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_image' mathlib/Mathlib`
- `rg -n 'exp_normalizedBallMass_monotoneOn|cutoffMass_deriv_identity|hasDerivAt_integral_scaledRadialCutoff_mul|IsStationaryIn.cutoff_squeeze|one_le_density_of_approximateTangent|planeMeasure_unit_closedBall|hausdorff_blowUp_ball|trace_starProjection' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/*.lean; rg -n -l IMRep lake-packages-25730c7c/simongmt/Poincare/SimonGMT (no match)`
- `lean (contract scope) #check Chapter04.hausdorff_blowUp_ball (unknown: Chapter04 not imported), integral_withDensity_eq_integral_toReal_smul, hasDerivAt_integral_of_dominated_loc_of_deriv_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image, euclideanHausdorffMeasure_homothety_image (all in scope)`
- `python3 -I name-collision scan of the six doragm_* names over all workspaces' dag.json, ch07 node JSON files and GMT/**/*.lean (no hit)`
- `lean /tmp/mono-decomp-check/{Children,Comparator,Assembly,Child3,Child4,Child6}.lean and /tmp/mono-review/Full2.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/tmp/mono-decomp-check/Assembly.lean`
- `/tmp/mono-review/Full2.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c, and its GMT/Ch07/Contract.lean is byte-identical to the workspace Submission.lean, which is the compiler context of every child type.
Nothing in the snapshot proves any child:
- GMT/Ch04/Submission.lean only states StationaryMonotonicity and StationaryDensity as Props, for its own RectifiableVarifold type, behind a sorry-backed main theorem.
- No doragm_* declaration exists.
- The pinned SimonGMT Chapter04 library proves the analogous cutoff identity, exponential monotonicity, cutoff squeeze and density-one results only for its RectifiableVarifold structure; nothing in SimonGMT mentions IMRep. Chapter04 is not imported by the contract (#check fails in contract scope), so it served only as a template. Simon's chapter-04.txt 3.2–3.5 and 3.16–3.17 fixed the proof route.
The Mathlib lemmas the children's proofs cite exist at the pinned revision and are in contract scope:
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286);
- integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318);
- IsCompact.exists_cthickening_subset_open (Thickening.lean:426) and cthickening_closedBall (Ball/Pointwise.lean:318);
- tendsto_measure_iInter_atTop and tendsto_measure_iUnion_atTop (Continuity.lean:220, 198);
- Submodule.starProjection_orthogonal_val and norm_starProjection_apply_le (Projection/Basic.lean:203, 411);
- Measure.mem_support_iff_forall (Support.lean:75);
- the Real.smoothTransition lemmas;
- integral_eq_lintegral_of_nonneg_ae (Bochner/Basic.lean:515) and ENNReal.ofReal_toReal_le;
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume and Isometry.euclideanHausdorffMeasure_image (Volume/Measure.lean:187, 131).
There is no ofReal_integral_le_lintegral_ofReal (rg: no match), so tangent_lower_density uses integral_eq_lintegral_of_nonneg_ae with ofReal_toReal_le instead.
Lean checks: all six child types elaborate, and the exact parent type follows from them plus the uncle. An end-to-end file proves all six children and the parent assuming only the uncle, with axioms propext, Classical.choice and Quot.sound only. No identical comparator-approved declaration exists to reuse.
