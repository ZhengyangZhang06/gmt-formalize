# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1`
- Child DAG node: `root.lipschitz_graph_corollary-a1.hole_estimate-a1.hole_split_upper-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5: the splitting p_x^perp = Q + (P - p_x), the graph cone bound on Fhat (here replaced by the slope hypothesis on the measurable set F), the trivial bound off F, and integration over B_{3s}(zeta). Uses the sibling child hs_norm_bounds with m = k = n + l: A -> hsNormSq(A) is continuous, and 0 <= hsNormSq(A) <= (n + l)||A||^2 and |A v|^2 <= hsNormSq(A)|v|^2 for every linear map A of R^(n+l) and every v.

Notation. B := B_{3s}(zeta) (closed ball, measurable, mu(B) < infinity by hypothesis), P := T.starProjection (orthogonal projection onto T; T is finite-dimensional, hence complete, so P exists and ||P|| <= 1), h(x) := hsNormSq(p(x) - P), and 1_{F^c} is the indicator function of the complement F^c of F (equal to 1 off F and 0 on F). All integrals are Bochner integrals.

1. Integrability of the right-hand integrands.
   (i) x -> p(x) - P is a.e. strongly measurable (difference of an a.e. strongly measurable function and a constant), and hsNormSq is continuous (hs_norm_bounds), so h is a.e. strongly measurable.
   (ii) ||p(x) - P|| <= ||p(x)|| + ||P|| <= 1 + 1 = 2, so 0 <= h(x) <= (n + l)||p(x) - P||^2 <= 4(n + l) for every x (hs_norm_bounds).
   (iii) A bounded a.e. strongly measurable function is integrable on a set of finite measure, so h is integrable on B. The constant eps^2 is integrable on B, and so is 1_{F^c}, the indicator of the measurable set F^c applied to the integrable constant 1.
2. Pointwise splitting. Fix x ∈ B and put v := x - zeta, so |v| <= 3s. Since v - p(x)v = (v - Pv) + (-(p(x) - P)v), the triangle inequality gives |v - p(x)v| <= |v - Pv| + |(p(x) - P)v|. Both sides are nonnegative, so squaring and using (a + b)^2 <= 2a^2 + 2b^2 (equivalent to (a - b)^2 >= 0) gives
   |v - p(x)v|^2 <= 2|v - Pv|^2 + 2|(p(x) - P)v|^2.
   By hs_norm_bounds, |(p(x) - P)v|^2 <= h(x)|v|^2 <= 9 s^2 h(x), using h(x) >= 0.
3. The term |v - Pv|.
   (i) If x ∈ F, the slope hypothesis gives 0 <= |v - Pv| <= eps|v|; squaring (0 <= a <= b implies a^2 <= b^2) gives |v - Pv|^2 <= eps^2 |v|^2 <= 9 eps^2 s^2. No sign condition on eps is needed.
   (ii) If x ∉ F, then |v - Pv| = dist(v, Pv) = infDist(v, T) <= dist(v, 0) = |v|, because the orthogonal projection realises the distance to T and 0 ∈ T. So |v - Pv|^2 <= |v|^2 <= 9 s^2.
4. Pointwise bound. In case (i), 1_{F^c}(x) = 0 and |v - p(x)v|^2 <= 18 eps^2 s^2 + 18 s^2 h(x) = 18 s^2 (eps^2 + 1_{F^c}(x) + h(x)). In case (ii), 1_{F^c}(x) = 1 and |v - p(x)v|^2 <= 18 s^2 + 18 s^2 h(x) <= 18 s^2 (eps^2 + 1 + h(x)) = 18 s^2 (eps^2 + 1_{F^c}(x) + h(x)), since eps^2 >= 0. So for every x ∈ B:
   |(x - zeta) - p(x)(x - zeta)|^2 <= 18 s^2 (eps^2 + 1_{F^c}(x) + h(x)).
5. Integration.
   (i) The left integrand is nonnegative and the right integrand is integrable on B by step 1, and the inequality of step 4 holds at every point of B, hence mu-a.e. on B. For the Bochner integral this gives: integral over B of |(x - zeta) - p(x)(x - zeta)|^2 dmu <= integral over B of 18 s^2 (eps^2 + 1_{F^c} + h) dmu = 18 s^2 * integral over B of (eps^2 + 1_{F^c} + h) dmu.
   (ii) By linearity (all three summands are integrable on B), integral over B of (eps^2 + 1_{F^c} + h) = integral over B of eps^2 + integral over B of 1_{F^c} + integral over B of h.
   (iii) integral over B of eps^2 dmu = eps^2 mu(B).toReal.
   (iv) integral over B of 1_{F^c} dmu = (mu restricted to B)(F^c).toReal = mu(F^c ∩ B).toReal = mu(B minus F).toReal.
   (v) Substituting (ii)-(iv) into (i) gives exactly
   integral over B of |(x - zeta) - p(x)(x - zeta)|^2 dmu <= 18 s^2 [eps^2 mu(B).toReal + mu(B minus F).toReal + integral over B of hsNormSq(p(x) - P) dmu]. QED

Lean notes (Mathlib names that worked under the pinned toolchain; for convenience only):
- obtain the sibling as lgc_hsNormSq_bounds (n + ℓ) (n + ℓ) (inside namespace Submission);
- step 1: hcont.comp_aestronglyMeasurable (hp.sub aestronglyMeasurable_const), Submodule.starProjection_norm_le, Measure.integrableOn_of_bounded, integrableOn_const and IntegrableOn.indicator;
- step 3(ii): Submodule.dist_starProjection_eq_infDist and Metric.infDist_le_dist_of_mem (Submodule.zero_mem T);
- step 5: integral_mono_of_nonneg, integral_const_mul, integral_add (state the integrability facts with explicit lambdas first), setIntegral_const, integral_indicator, Measure.restrict_apply and measureReal_def;
- step 2: (a + b)^2 <= 2a^2 + 2b^2 via pow_le_pow_left₀ and nlinarith [sq_nonneg (a - b)].

Remark (verified Lean realization; not part of the mathematical argument). The declaration below was compiled in this decomposition session (attempt 5, fresh scratch root; Lean v4.35.0-rc3, Mathlib 25730c7c, simongmt 2b366308) inside `namespace GMT.Ch05` / `namespace Submission`, in a module importing a freshly compiled copy of the frozen GMT/Ch05/Submission.lean, with the contract's `open MeasureTheory Metric Set Filter Topology`, `open scoped ENNReal NNReal` and `open RectifiableVarifold` in effect. The candidate module compiled with no errors. Its only `sorry`s were the two sibling contracts lgc_tangent_plane_ae and lgc_density_monotonicity, which this child does not use. In the contract scope, `theorem _root_.HumanizeNodeComparator.target_<name> : (<frozen type>) := by exact Submission.<name>` type-checks against the compiled module, and `#print axioms` lists only propext, Classical.choice and Quot.sound. The declaration can be pasted into GMT/Ch05/Submission.lean inside `namespace Submission`, before `main_theorem` (after its dependency lgc_hsNormSq_bounds).

theorem lgc_hole_split_upper : ∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (p : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ)) (T : Submodule ℝ (Amb n ℓ)) (F : Set (Amb n ℓ)) (ζ : Amb n ℓ) (s ε : ℝ), 0 < s → AEStronglyMeasurable p μ → (∀ x, ‖p x‖ ≤ 1) → MeasurableSet F → μ (closedBall ζ (3 * s)) ≠ ⊤ → (∀ x ∈ F, ‖(x - ζ) - T.starProjection (x - ζ)‖ ≤ ε * ‖x - ζ‖) → ∫ x in closedBall ζ (3 * s), ‖(x - ζ) - p x (x - ζ)‖ ^ 2 ∂μ ≤ 18 * s ^ 2 * (ε ^ 2 * (μ (closedBall ζ (3 * s))).toReal + (μ (closedBall ζ (3 * s) \ F)).toReal + ∫ x in closedBall ζ (3 * s), hsNormSq (p x - T.starProjection) ∂μ) := by
  intro n ℓ μ p T F ζ s ε hs hp hpb hF hfin hslope
  obtain ⟨hcont, hHS⟩ := lgc_hsNormSq_bounds (n + ℓ) (n + ℓ)
  have hPn : ‖T.starProjection‖ ≤ 1 := Submodule.starProjection_norm_le T
  have hhm : AEStronglyMeasurable (fun x => hsNormSq (p x - T.starProjection)) μ :=
    hcont.comp_aestronglyMeasurable (hp.sub aestronglyMeasurable_const)
  have hhb : ∀ x, ‖hsNormSq (p x - T.starProjection)‖ ≤ 4 * ((n + ℓ : ℕ) : ℝ) := by
    intro x
    obtain ⟨h0, h1, -⟩ := hHS (p x - T.starProjection)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have h2 : ‖p x - T.starProjection‖ ≤ 2 := by
      calc ‖p x - T.starProjection‖ ≤ ‖p x‖ + ‖T.starProjection‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hpb x) hPn
        _ = 2 := by norm_num
    calc hsNormSq (p x - T.starProjection) ≤ ((n + ℓ : ℕ) : ℝ) * ‖p x - T.starProjection‖ ^ 2 := h1
      _ ≤ ((n + ℓ : ℕ) : ℝ) * 2 ^ 2 := by gcongr
      _ = 4 * ((n + ℓ : ℕ) : ℝ) := by ring
  have hhi : IntegrableOn (fun x => hsNormSq (p x - T.starProjection)) (closedBall ζ (3 * s)) μ :=
    Measure.integrableOn_of_bounded hfin hhm (Eventually.of_forall hhb)
  have hci : IntegrableOn (fun _ => (1:ℝ)) (closedBall ζ (3 * s)) μ :=
    integrableOn_const hfin
  have hii : IntegrableOn (Fᶜ.indicator (fun _ => (1:ℝ))) (closedBall ζ (3 * s)) μ :=
    hci.indicator hF.compl
  have hpt : ∀ x ∈ closedBall ζ (3 * s), ‖(x - ζ) - p x (x - ζ)‖ ^ 2 ≤
      18 * s ^ 2 * (ε ^ 2 + Fᶜ.indicator (fun _ => (1:ℝ)) x + hsNormSq (p x - T.starProjection)) := by
    intro x hx
    have hxz : ‖x - ζ‖ ≤ 3 * s := by rw [← dist_eq_norm]; exact hx
    have hsplit : (x - ζ) - p x (x - ζ) =
        ((x - ζ) - T.starProjection (x - ζ)) + (-((p x - T.starProjection) (x - ζ))) := by
      simp only [sub_apply]
      abel
    have h1 : ‖(x - ζ) - p x (x - ζ)‖ ^ 2 ≤
        2 * ‖(x - ζ) - T.starProjection (x - ζ)‖ ^ 2 + 2 * ‖(p x - T.starProjection) (x - ζ)‖ ^ 2 := by
      rw [hsplit]
      have h := norm_add_le ((x - ζ) - T.starProjection (x - ζ)) (-((p x - T.starProjection) (x - ζ)))
      rw [norm_neg] at h
      have hn := norm_nonneg ((x - ζ) - T.starProjection (x - ζ) + -((p x - T.starProjection) (x - ζ)))
      have hsq := pow_le_pow_left₀ hn h 2
      nlinarith [sq_nonneg (‖(x - ζ) - T.starProjection (x - ζ)‖ -
        ‖(p x - T.starProjection) (x - ζ)‖)]
    have h2 : ‖(p x - T.starProjection) (x - ζ)‖ ^ 2 ≤ hsNormSq (p x - T.starProjection) * (9 * s ^ 2) := by
      obtain ⟨h0, -, h3⟩ := hHS (p x - T.starProjection)
      calc ‖(p x - T.starProjection) (x - ζ)‖ ^ 2
          ≤ hsNormSq (p x - T.starProjection) * ‖x - ζ‖ ^ 2 := h3 (x - ζ)
        _ ≤ hsNormSq (p x - T.starProjection) * (3 * s) ^ 2 := by gcongr
        _ = hsNormSq (p x - T.starProjection) * (9 * s ^ 2) := by ring
    have hQ : ‖(x - ζ) - T.starProjection (x - ζ)‖ ≤ ‖x - ζ‖ := by
      rw [← dist_eq_norm, Submodule.dist_starProjection_eq_infDist]
      have := infDist_le_dist_of_mem (x := x - ζ) (Submodule.zero_mem T)
      rwa [dist_zero_right] at this
    by_cases hxF : x ∈ F
    · have hind : Fᶜ.indicator (fun _ => (1:ℝ)) x = 0 :=
        indicator_of_notMem (by simpa using hxF) _
      have h3 : ‖(x - ζ) - T.starProjection (x - ζ)‖ ^ 2 ≤ ε ^ 2 * (9 * s ^ 2) := by
        have h0 : 0 ≤ ‖(x - ζ) - T.starProjection (x - ζ)‖ := norm_nonneg _
        calc ‖(x - ζ) - T.starProjection (x - ζ)‖ ^ 2 ≤ (ε * ‖x - ζ‖) ^ 2 :=
              pow_le_pow_left₀ h0 (hslope x hxF) 2
          _ = ε ^ 2 * ‖x - ζ‖ ^ 2 := by ring
          _ ≤ ε ^ 2 * (3 * s) ^ 2 := by gcongr
          _ = ε ^ 2 * (9 * s ^ 2) := by ring
      rw [hind]
      nlinarith
    · have hind : Fᶜ.indicator (fun _ => (1:ℝ)) x = 1 := indicator_of_mem hxF _
      have h3 : ‖(x - ζ) - T.starProjection (x - ζ)‖ ^ 2 ≤ 9 * s ^ 2 := by
        calc ‖(x - ζ) - T.starProjection (x - ζ)‖ ^ 2 ≤ ‖x - ζ‖ ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hQ 2
          _ ≤ (3 * s) ^ 2 := by gcongr
          _ = 9 * s ^ 2 := by ring
      rw [hind]
      nlinarith [sq_nonneg ε, sq_nonneg s]
  have hsum : IntegrableOn (fun x => ε ^ 2 + Fᶜ.indicator (fun _ => (1:ℝ)) x +
      hsNormSq (p x - T.starProjection)) (closedBall ζ (3 * s)) μ :=
    ((integrableOn_const hfin).add hii).add hhi
  calc ∫ x in closedBall ζ (3 * s), ‖(x - ζ) - p x (x - ζ)‖ ^ 2 ∂μ
      ≤ ∫ x in closedBall ζ (3 * s), 18 * s ^ 2 * (ε ^ 2 + Fᶜ.indicator (fun _ => (1:ℝ)) x +
          hsNormSq (p x - T.starProjection)) ∂μ := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
          (hsum.const_mul (18 * s ^ 2))
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
        exact hpt x hx
    _ = 18 * s ^ 2 * (ε ^ 2 * (μ (closedBall ζ (3 * s))).toReal +
          (μ (closedBall ζ (3 * s) \ F)).toReal +
          ∫ x in closedBall ζ (3 * s), hsNormSq (p x - T.starProjection) ∂μ) := by
        have h12 : IntegrableOn (fun x => ε ^ 2 + Fᶜ.indicator (fun _ => (1:ℝ)) x)
            (closedBall ζ (3 * s)) μ := (integrableOn_const hfin).add hii
        have hc2 : IntegrableOn (fun _ => ε ^ 2) (closedBall ζ (3 * s)) μ := integrableOn_const hfin
        have e1 : ∫ x in closedBall ζ (3 * s), (ε ^ 2 + Fᶜ.indicator (fun _ => (1:ℝ)) x +
              hsNormSq (p x - T.starProjection)) ∂μ =
            ∫ x in closedBall ζ (3 * s), (ε ^ 2 + Fᶜ.indicator (fun _ => (1:ℝ)) x) ∂μ +
              ∫ x in closedBall ζ (3 * s), hsNormSq (p x - T.starProjection) ∂μ :=
          integral_add h12 hhi
        have e2 : ∫ x in closedBall ζ (3 * s), (ε ^ 2 + Fᶜ.indicator (fun _ => (1:ℝ)) x) ∂μ =
            ∫ x in closedBall ζ (3 * s), ε ^ 2 ∂μ +
              ∫ x in closedBall ζ (3 * s), Fᶜ.indicator (fun _ => (1:ℝ)) x ∂μ :=
          integral_add hc2 hii
        have e3 : ∫ x in closedBall ζ (3 * s), ε ^ 2 ∂μ = ε ^ 2 * (μ (closedBall ζ (3 * s))).toReal := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
        have e4 : ∫ x in closedBall ζ (3 * s), Fᶜ.indicator (fun _ => (1:ℝ)) x ∂μ =
            (μ (closedBall ζ (3 * s) \ F)).toReal := by
          rw [integral_indicator hF.compl, setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
            Measure.restrict_apply hF.compl, inter_comm, ← sdiff_eq]
        rw [integral_const_mul, e1, e2, e3, e4]

## Key steps

1. h(x) = hsNormSq(p(x) - P) is a.e. strongly measurable and bounded by 4(n + l); eps^2, 1_{F^c} and h are integrable on B
2. |v - p(x)v|^2 <= 2|v - Pv|^2 + 2|(p(x) - P)v|^2 and |(p(x) - P)v|^2 <= h(x)|v|^2 <= 9 s^2 h(x)
3. On F: |v - Pv|^2 <= eps^2 |v|^2 <= 9 eps^2 s^2; off F: |v - Pv| = infDist(v, T) <= |v| <= 3s
4. Pointwise on B: |v - p(x)v|^2 <= 18 s^2 (eps^2 + 1_{F^c}(x) + h(x))
5. Integrate over B: linearity, the constant integral and the indicator integral mu(B minus F) give the stated bound

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project ea5607598f3133b40a13241f2e51517a8c6423cd, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean (all c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12)`
- `rg -n 'lgc_|hsNormSq_bounds|support_closest_point|rotated_graph_slope|hole_annulus_lower|hole_split_upper' <snapshot>/project (no match)`
- `rg -n 'hsNormSq' <snapshot>/project (only the contract definition, Submission.lean:47, and its uses)`
- `rg -n 'lemma isClosed_support|lemma measure_compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'exists_infDist_eq_dist|theorem infDist_le_infDist_of_subset|theorem infDist_le_dist_of_mem' <snapshot>/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `rg -n 'dist_starProjection_eq_infDist|theorem starProjection_norm_le|HasOrthogonalProjection.ofCompleteSpace' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n 'integrableOn_of_bounded' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean; rg -n 'integral_mono_of_nonneg' .../Integral/Bochner/Basic.lean; rg -n 'theorem setIntegral_mono_set|theorem integral_indicator|theorem setIntegral_const' .../Integral/Bochner/Set.lean`
- `rg -n 'isClosed_range' .../Topology/MetricSpace/Antilipschitz.lean; rg -n 'sum_mul_sq_le_sq_mul_sq' .../Algebra/Order/BigOperators/Ring/Finset.lean; rg -n 'comp_aestronglyMeasurable₂' .../MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `python3: lean_name collision scan of <run>/dag.json for the five names; grep of <run>/nodes/*/decomposition-v*.json (other nodes), .humanize/math-wiki and .swarm-worktrees/*/gmt-ch05/GMT/Ch05/Submission.lean (159 files): no match`
- `python3: max_nodes in .humanize/swarm-configs/e7e4b943ce8d47d69f960d0598137f28.json (200) and 11abe17eae34407eb92f02a80299a0ca.json (1000); len(dag.json nodes); grep -n 'remaining = self.config.max_nodes' /runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/runtime.py`
- `grep -n '(9)|(10)' and sed -n 470,600p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt (printed proof of Simon 2.6, displays (9)-(10), pp. 112-113)`
- `lean -o /tmp/lgc-hole-v5-x104/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (fresh byte copy of the frozen Submission)`
- `lean -o /tmp/lgc-hole-v5-x104/olean/Cand/Cand.olean Cand/Cand.lean (sibling contracts sorry + five children + assembly)`
- `lean Cand/Types.lean; lean Cand/Exact.lean; lean Cand/Comparator.lean; lean Cand/AsmOnly.lean; lean Cand/Inst.lean (all exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-graph-corollary-a1-hole-estimate-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-lipschitz-approximation-a1-hole-estimate-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/e7e4b943ce8d47d69f960d0598137f28.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/swarm-configs/11abe17eae34407eb92f02a80299a0ca.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch05/e7e4b943ce8d47d69f960d0598137f28.log`
- `/runtime/flows/gmt-claude-a2c7949d39d0/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/lgc-hole-v5-x104/src/Cand/Cand.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/Types.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/Exact.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/Comparator.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/AsmOnly.lean`
- `/tmp/lgc-hole-v5-x104/src/Cand/Inst.lean`

Snapshot and contract. manifest.json pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean, the workspace Contract.lean and the snapshot Contract.lean are byte-identical (sha256 c966f51e…). The snapshot project contains none of the five proposed names; hsNormSq occurs only as the contract definition and its uses. No existing hsNormSq/operator-norm comparison for continuous linear maps exists to reuse. The accepted wiki theorem hsNorm_starProjection_trace_identities has a different type, so it cannot be reused by exact name.
Mathlib facts used by the child proofs, all present in the snapshot:
- isClosed_support and measure_compl_support (Measure/Support.lean:115, 202)
- IsClosed.exists_infDist_eq_dist, infDist_le_dist_of_mem and infDist_le_infDist_of_subset (HausdorffDistance.lean:615, 500, 505)
- HasOrthogonalProjection.ofCompleteSpace, dist_starProjection_eq_infDist and starProjection_norm_le (Projection/Basic.lean:53, 234, 386)
- Measure.integrableOn_of_bounded (IntegrableOn.lean:716) and integral_mono_of_nonneg (Bochner/Basic.lean:676)
- integral_indicator, setIntegral_const and setIntegral_mono_set (Bochner/Set.lean:185, 524, 737)
- AntilipschitzWith.isClosed_range (Antilipschitz.lean:175) and Finset.sum_mul_sq_le_sq_mul_sq (Ring/Finset.lean:171)
- Continuous.comp_aestronglyMeasurable₂ (AEStronglyMeasurable.lean:263)
The printed proof of Simon 2.6 (chapter-05.txt, displays (9)-(10), pp. 112-113) matches the supplied corrected steps.
Names and activation. None of the five names is reserved in dag.json, in other nodes' proposals, in the math wiki or in the 159 proof worktrees. The earlier accepted splits were blocked only by max_nodes = 200 in the previous worker's config. The current worker has max_nodes = 1000 and dag.json has fewer than 230 nodes.
Lean (this session). All six frozen types elaborate. The five child proofs compile with only standard axioms. The assembly proves the exact selected parent type from the five child types and the two sibling contracts.
