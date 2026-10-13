# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.product_support_density-a1.radial_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (supports), applied there to the nondecreasing profile f(r) = μ₀(B_r(y)); the two ball estimates μ(B_ε(t + y)) ≤ ω_d ε^d μ₀(B_ε(y)) and μ(B_ε(t + y)) ≥ ω_d (ε/2)^d μ₀(B_{ε/2}(y)) of the parent are used here in the form needed for the two implications. Notation: ℝ^k = Euclid k = EuclideanSpace ℝ (Fin k); L^k = volume on ℝ^k (Lebesgue measure); H^d = μHE[d] (Mathlib's normalized d-dimensional Hausdorff measure); ω_k = unitBallVolume k = L^k(B_1(0)); B_r(c) = Metric.ball c r (open; empty for r ≤ 0); √ = Real.sqrt (√c = 0 for c ≤ 0); integrals of [0, ∞]-valued functions are lower Lebesgue integrals (lintegral); ‖·‖ and ⟨·,·⟩ are the Euclidean norm and inner product.
1. (Radii.) For ε > 0 and σ ∈ ℝ^d: 0 ≤ √(ε² − ‖σ‖²) ≤ √(ε²) = ε, because ε² − ‖σ‖² ≤ ε², √ is monotone (Real.sqrt_le_sqrt) and √(ε²) = ε for ε ≥ 0 (Real.sqrt_sq).
2. (⇒.) Assume ∫_{ℝ^d} f(√(ε² − ‖σ‖²)) dσ ≠ 0 for every ε > 0, and let ε > 0. Suppose f(ε) = 0. By step 1 and monotonicity, 0 ≤ f(√(ε² − ‖σ‖²)) ≤ f(ε) = 0 for every σ ∈ ℝ^d, so the integrand is identically 0 and its integral is 0, contradicting the assumption at this ε. Hence f(ε) ≠ 0.
3. (⇐.) Assume f(ε) ≠ 0 for every ε > 0, let ε > 0, and suppose I := ∫_{ℝ^d} f(√(ε² − ‖σ‖²)) dσ = 0. Let B := B_{ε/2}(0) ⊂ ℝ^d. For σ ∈ B we have ‖σ‖² < ε²/4, hence (ε/2)² ≤ ε² − ‖σ‖² and ε² − ‖σ‖² ≥ 0, so √(ε² − ‖σ‖²) ≥ ε/2 (for a, c ≥ 0: a ≤ √c ⟺ a² ≤ c, Real.le_sqrt), and by monotonicity f(√(ε² − ‖σ‖²)) ≥ f(ε/2). Therefore the pointwise inequality f(ε/2)·1_B(σ) ≤ f(√(ε² − ‖σ‖²)) holds for every σ ∈ ℝ^d (off B the left side is 0). Integrating (lintegral_mono) and using ∫ c·1_B dL^d = c·L^d(B) for the measurable set B (lintegral_indicator_const): f(ε/2)·L^d(B) ≤ I = 0, so f(ε/2)·L^d(B) = 0. But f(ε/2) ≠ 0 by assumption (ε/2 > 0), and L^d(B) ≠ 0 because a nonempty open ball has positive Lebesgue measure (measure_ball_pos; for d = 0 the ball is the whole one-point space, of mass 1); a product of two nonzero elements of [0, ∞] is nonzero (mul_eq_zero). This contradiction shows I ≠ 0. ∎

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c, inside `namespace GMT.Ch07` with the contract's opens `open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`, `open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)`; #print axioms gives propext, Classical.choice, Quot.sound):
theorem Submission.dimred_cs_psd_radial_support : ∀ (d : ℕ) (f : ℝ → ℝ≥0∞), Monotone f → ((∀ ε : ℝ, 0 < ε → (∫⁻ σ : Euclid d, f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2))) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → f ε ≠ 0) := by
  intro d f hf
  constructor
  · intro h ε hε hfε
    apply h ε hε
    have hz : ∀ σ : Euclid d, f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2)) = 0 := by
      intro σ
      refine le_antisymm ?_ zero_le
      calc f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2)) ≤ f ε := by
            apply hf
            calc Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2) ≤ Real.sqrt (ε ^ 2) :=
                  Real.sqrt_le_sqrt (by nlinarith [norm_nonneg σ])
              _ = ε := Real.sqrt_sq hε.le
        _ = 0 := hfε
    simp [hz]
  · intro h ε hε h0
    have hε2 : 0 < ε / 2 := by linarith
    have hle : ∀ σ : Euclid d, (ball (0 : Euclid d) (ε / 2)).indicator (fun _ => f (ε / 2)) σ ≤
        f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2)) := by
      intro σ
      by_cases hσ : σ ∈ ball (0 : Euclid d) (ε / 2)
      · rw [indicator_of_mem hσ]
        apply hf
        rw [mem_ball_zero_iff] at hσ
        rw [Real.le_sqrt hε2.le (by nlinarith [norm_nonneg σ])]
        nlinarith [norm_nonneg σ]
      · rw [indicator_of_notMem hσ]
        exact zero_le
    have hint := lintegral_mono (μ := (volume : Measure (Euclid d))) hle
    rw [h0, lintegral_indicator_const measurableSet_ball] at hint
    have hprod : f (ε / 2) * volume (ball (0 : Euclid d) (ε / 2)) = 0 := le_antisymm hint zero_le
    rcases mul_eq_zero.1 hprod with hf0 | hv0
    · exact h _ hε2 hf0
    · exact (measure_ball_pos volume (0 : Euclid d) hε2).ne' hv0

## Key steps

1. Every radius √(ε² − ‖σ‖²) lies in [0, ε].
2. If f(ε) = 0, monotonicity makes the integrand vanish identically, so the integral is 0.
3. On B_{ε/2}(0) every radius is ≥ ε/2, so the integral is ≥ f(ε/2)·L^d(B_{ε/2}(0)), a product of two nonzero numbers.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-density-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}; cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md; cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `sed -n 200,600p GMT/Ch07/Contract.lean (IMRep.measure, unitBallVolume, HasMassDensity)`
- `python3 over dag.json: status/lean_statement/depends_on of im_mass_measure-a1, cone_splitting-a1, product_support_density-a1; accepted lean_statements mentioning HasMassDensity, unitBallVolume, Real.sqrt, 'volume (ball', μHE; regex for a density-uniqueness lemma; lean_name scan for psd|slice|radial|uniq`
- `python3 over nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json (reuse-child precedent: tangent_projection_measurable, orientation_norm)`
- `git show 045731be7c74a51a79d0c3895070d67408b82f53:GMT/Ch07/Submission.lean | grep theorem; git show 01ae2c59e8d725f9f3839402fe6fe9bf93c32c3a:GMT/Ch07/Submission.lean | grep -n dimred_im_mass_measure`
- `sed -n 1,400p local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -n 'addHaar_ball_of_pos|addHaar_ball ' Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; sed -n 736,810p Mathlib/MeasureTheory/Constructions/Pi.lean; sed -n 160,240p Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; sed -n 370,395p Mathlib/Analysis/InnerProductSpace/PiL2.lean; sed -n 985,1010p Mathlib/Analysis/Normed/Lp/PiLp.lean; grep prod_norm_sq_eq_of_L2 Mathlib/Analysis/Normed/Lp/ProdLp.lean; grep 'le_sqrt|lt_sqrt|sqrt_le_sqrt|sqrt_sq' Mathlib/Analysis/Real/Sqrt.lean (all in the snapshot mathlib)`
- `grep -c dimred_cs_psd dag.json; grep -rl dimred_cs_psd GMT .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes lake-packages-25730c7c/simongmt/Poincare; grep -rl --include=*.lean dimred_cs_psd workspaces/.swarm-worktrees (no match anywhere)`
- `LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/psd-decomp/{Smoke,Assembly,ProveA,ProveC,ProveFD,Final}.lean (#check with pp.coercions, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-density-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-product-support-density-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees`
- `/tmp/psd-decomp/Assembly.lean`
- `/tmp/psd-decomp/Final.lean`

Pins. The snapshot manifest gives project b4d606d and mathlib 25730c7c. All Lean checks used the matching workspace build, Lean v4.35.0-rc3.

Library.
- The snapshot Mathlib has everything the four new children need:
  - H^d on a d-plane equals Lebesgue measure: Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume.
  - Cavalieri slicing of balls: LinearIsometryEquiv.piLpCongrLeft with finSumFinEquiv, PiLp.sumPiLpEquivProdLpPiLp, WithLp.volume_preserving_ofLp, WithLp.prod_norm_sq_eq_of_L2 and Measure.prod_apply.
  - Ball volumes: Measure.addHaar_ball_of_pos.
  - Translation invariance: lintegral_sub_right_eq_self.
  - Square roots: Real.lt_sqrt and Real.le_sqrt.
- SimonGMT has no product or slicing results for currents.
- dag.json has no accepted lemma on ball slicing, radial densities or density uniqueness, so the only possible reuse is the mass–measure identity.

Reuse. dimred_im_mass_measure (node im_mass_measure-a1, status accepted, candidate 01ae2c59, Submission.lean line 1730) has a frozen type byte-identical to the child's. It is missing from this node's proof base 045731b, so it is listed as a reused child.

Names. dimred_cs_psd_* occurs nowhere: not in dag.json, GMT, the node records, SimonGMT or the 3004 worktrees.

Lean.
- All 5 child types elaborate after import GMT.Ch07.Submission, in namespace GMT.Ch07 with the contract opens.
- The 4 new children are fully proved, using only the axioms propext, Classical.choice and Quot.sound.
- The frozen parent type is assembled from the 5 children. Its only sorryAx comes from the stub of the accepted dimred_im_mass_measure.
