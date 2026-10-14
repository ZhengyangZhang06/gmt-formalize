# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.chart_bilipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof ("Bi-Lipschitz charts"), stated for an arbitrary compact K (the parent uses K = closure(Y_j) ⊆ V_j). The case a = b of the lower bound is closed with the reused child local_lower_lipschitz (codim1_rdo_c1cov_local_lower_lipschitz); this is the same estimate as the parent's integral form ψ(a_k) − ψ(b_k) = ∫₀¹ Dψ(b_k + τ(a_k − b_k))(a_k − b_k) dτ, packaged as a lower Lipschitz bound on a ball.
Notation: |·| is the Euclidean norm, ‖·‖ the operator norm, B_δ(a) the open ball, closedBall(c, R) the closed ball.

1. (Upper bound.) K is compact, hence bounded; choose R ≥ 0 with K ⊆ B̄ := closedBall(0, R). Since ψ is C¹, y ↦ Dψ(y) is continuous (ContDiff.continuous_fderiv, using 1 ≠ 0). B̄ is compact, so there is a constant C with ‖Dψ(y)‖ ≤ C for all y ∈ B̄ (IsCompact.exists_bound_of_continuousOn); put Λ := max(C, 0). ψ is differentiable at every point and B̄ is convex, so the mean value inequality (Convex.norm_image_sub_le_of_norm_fderiv_le) gives |ψ(a) − ψ(b)| ≤ Λ|a − b| for all a, b ∈ B̄, in particular for all a, b ∈ K.
2. (Lower bound: contradiction hypothesis.) Suppose that no m > 0 satisfies m|a − b| ≤ |ψ(a) − ψ(b)| for all a, b ∈ K. Applying this to m := 1/(k + 1) for each k ∈ ℕ gives a_k, b_k ∈ K with |ψ(a_k) − ψ(b_k)| < (k + 1)⁻¹|a_k − b_k|. In particular a_k ≠ b_k.
3. (Compactness.) K ×ˢ K is a compact subset of the metric space ℝ^d × ℝ^d, so (IsCompact.tendsto_subseq) there are a strictly increasing φ : ℕ → ℕ and (a, b) ∈ K × K with a_{φ(i)} → a and b_{φ(i)} → b as i → ∞. Also φ(i) → ∞, so (φ(i) + 1)⁻¹ → 0.
4. (Case a ≠ b.) For u, v ∈ K we have |u − v| ≤ 2R. Hence |ψ(a_{φ(i)}) − ψ(b_{φ(i)})| < (φ(i) + 1)⁻¹·2R → 0. By continuity of ψ and of the norm the left side tends to |ψ(a) − ψ(b)|, so |ψ(a) − ψ(b)| ≤ 0, i.e. ψ(a) = ψ(b). Since a, b ∈ K and a ≠ b this contradicts the injectivity of ψ on K.
5. (Case a = b.) a ∈ K, so Dψ(a) is injective; ψ is C¹. By local_lower_lipschitz (applied with G := ψ and the point a) there are δ > 0 and μ > 0 with μ|u − v| ≤ |ψ(u) − ψ(v)| for all u, v ∈ B_δ(a). Since a_{φ(i)} → a, b_{φ(i)} → a and (φ(i) + 1)⁻¹ → 0, there is an index i with a_{φ(i)}, b_{φ(i)} ∈ B_δ(a) and (φ(i) + 1)⁻¹ < μ. For this i put u := a_{φ(i)}, v := b_{φ(i)}; then u ≠ v and
 μ|u − v| ≤ |ψ(u) − ψ(v)| < (φ(i) + 1)⁻¹|u − v| < μ|u − v|,
a contradiction.
6. (Conclusion.) Both cases are impossible, so the hypothesis of step 2 fails: some m > 0 satisfies m|a − b| ≤ |ψ(a) − ψ(b)| for all a, b ∈ K. Together with Λ from step 1 this gives both inequalities. (If K = ∅ everything is vacuous; e.g. m = 1 works.) ∎

Lean realization note. The verified code below merges steps 4 and 5: since (φ(i)+1)⁻¹|a_{φ(i)} − b_{φ(i)}| → 0·|a − b| = 0, continuity gives ψ(a) = ψ(b), so a = b by injectivity on K; then step 5 applies verbatim (its chain μ|u − v| ≤ |ψ(u) − ψ(v)| < (φ(i)+1)⁻¹|u − v| ≤ μ|u − v| is already contradictory). It uses the bound C of step 1 directly as Λ.

Appendix (verified Lean realization of the proof above). The code below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b36630 when placed after `import GMT.Ch07.Submission` in the frozen contract scope (inside `namespace GMT.Ch07` with the contract's `open` commands, after the contract's `noncomputable section … end`), i.e. where accepted `theorem Submission.…` declarations live in GMT/Ch07/Submission.lean. It refers to the sibling declarations Submission.codim1_rdo_c1cov_local_lower_lipschitz (each with its exact frozen type, introduced by `have h_<key> : <type> := Submission.<name>` at the start of the proof). It was checked twice: (i) with the exact frozen sibling types as hypotheses, giving no errors and no warnings and `#print axioms` = [propext, Classical.choice, Quot.sound]; (ii) end to end, in one file containing all eight new children of dtc_bc_lc_sl_coarea in dependency order, the parent theorem proved from them, and `sorry` placeholders only for the reused accepted declarations and the parent's resolved dependencies (no warning from any child declaration). `Submission.dtc_bc_lc_sl_co_chart_bilipschitz` has exactly the frozen type of this child.

```lean
theorem Submission.dtc_bc_lc_sl_co_chart_bilipschitz : ∀ (P d : ℕ) (ψ : Euclid d → Euclid P) (K : Set (Euclid d)), ContDiff ℝ 1 ψ → IsCompact K → InjOn ψ K → (∀ y ∈ K, Injective (fderiv ℝ ψ y)) → ∃ m Λ : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖ψ a - ψ b‖ ∧ ‖ψ a - ψ b‖ ≤ Λ * ‖a - b‖ := by
  have h_local_lower_lipschitz : (∀ (P n : ℕ) (G : Euclid n → Euclid P) (x : Euclid n), ContDiff ℝ 1 G → Injective (fderiv ℝ G x) → ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ a ∈ ball x δ, ∀ b ∈ ball x δ, μ * ‖a - b‖ ≤ ‖G a - G b‖) := Submission.codim1_rdo_c1cov_local_lower_lipschitz
  intro P d ψ K hψ hK hinj hD
  -- Step 1: upper bound via the mean value inequality on a closed ball containing `K`
  obtain ⟨R, hR⟩ : ∃ R, K ⊆ closedBall (0 : Euclid d) R := hK.isBounded.subset_closedBall 0
  have hcont : Continuous (fun y => fderiv ℝ ψ y) := hψ.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid d) R).exists_bound_of_continuousOn
    hcont.continuousOn
  have hdiff : Differentiable ℝ ψ := hψ.differentiable one_ne_zero
  have hup : ∀ a ∈ K, ∀ b ∈ K, ‖ψ a - ψ b‖ ≤ C * ‖a - b‖ := fun a ha b hb =>
    (convex_closedBall (0 : Euclid d) R).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hdiff x) hC (hR hb) (hR ha)
  -- Steps 2-6: lower bound by contradiction
  have hlow : ∃ m : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖ψ a - ψ b‖ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ a ∈ K, ∃ b ∈ K, ‖ψ a - ψ b‖ < 1 / ((k : ℝ) + 1) * ‖a - b‖ :=
      fun k => hcon _ (by positivity)
    choose a ha b hb hab using hseq
    obtain ⟨⟨a0, b0⟩, ⟨ha0, hb0⟩, φ, hφ, hlim⟩ :=
      (hK.prod hK).tendsto_subseq (x := fun k => (a k, b k)) (fun k => Set.mk_mem_prod (ha k) (hb k))
    have hA : Tendsto (fun i => a (φ i)) atTop (𝓝 a0) := (continuous_fst.tendsto _).comp hlim
    have hB : Tendsto (fun i => b (φ i)) atTop (𝓝 b0) := (continuous_snd.tendsto _).comp hlim
    have hinv : Tendsto (fun i => 1 / ((φ i : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    -- the two limit points coincide (injectivity of `ψ` on `K`)
    have hψc : Continuous ψ := hψ.continuous
    have h1 : Tendsto (fun i => ‖ψ (a (φ i)) - ψ (b (φ i))‖) atTop (𝓝 ‖ψ a0 - ψ b0‖) :=
      (((hψc.tendsto a0).comp hA).sub ((hψc.tendsto b0).comp hB)).norm
    have h2 : Tendsto (fun i => 1 / ((φ i : ℝ) + 1) * ‖a (φ i) - b (φ i)‖) atTop
        (𝓝 (0 * ‖a0 - b0‖)) := hinv.mul (hA.sub hB).norm
    have h3 : ‖ψ a0 - ψ b0‖ ≤ 0 * ‖a0 - b0‖ :=
      le_of_tendsto_of_tendsto' h1 h2 (fun i => (hab (φ i)).le)
    have h4 : ψ a0 = ψ b0 := by
      rw [zero_mul] at h3
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h3)
    have hab0 : a0 = b0 := hinj ha0 hb0 h4
    rw [← hab0] at hB
    -- local lower Lipschitz bound near `a0`
    obtain ⟨δ, μ, hδ, hμ, hloc⟩ := h_local_lower_lipschitz P d ψ a0 hψ (hD a0 ha0)
    have e1 : ∀ᶠ i in atTop, a (φ i) ∈ ball a0 δ := hA.eventually_mem (ball_mem_nhds a0 hδ)
    have e2 : ∀ᶠ i in atTop, b (φ i) ∈ ball a0 δ := hB.eventually_mem (ball_mem_nhds a0 hδ)
    have e3 : ∀ᶠ i in atTop, 1 / ((φ i : ℝ) + 1) ∈ Iio μ := hinv.eventually_mem (Iio_mem_nhds hμ)
    obtain ⟨i, hi1, hi2, hi3⟩ := (e1.and (e2.and e3)).exists
    have k1 := hloc _ hi1 _ hi2
    have k2 := hab (φ i)
    have k3 : 1 / ((φ i : ℝ) + 1) * ‖a (φ i) - b (φ i)‖ ≤ μ * ‖a (φ i) - b (φ i)‖ :=
      mul_le_mul_of_nonneg_right (Set.mem_Iio.mp hi3).le (norm_nonneg _)
    linarith
  obtain ⟨m, hm, hm'⟩ := hlow
  exact ⟨m, C, hm, fun a ha b hb => ⟨hm' a ha b hb, hup a ha b hb⟩⟩
```

## Key steps

1. Upper bound: ‖Dψ‖ ≤ Λ on a closed ball containing K (continuity of Dψ on a compact set), then the mean value inequality on that convex ball.
2. Lower bound by contradiction: a_k ≠ b_k in K with |ψ(a_k) − ψ(b_k)| < (k+1)⁻¹|a_k − b_k|; extract a_{φ(i)} → a, b_{φ(i)} → b in K by compactness of K × K.
3. a ≠ b: continuity forces ψ(a) = ψ(b), contradicting injectivity on K.
4. a = b: the local lower Lipschitz bound of local_lower_lipschitz on a ball around a contradicts the quotient tending to 0.
5. Verified Lean realization supplied in the appendix (compiles warning-free; standard axioms only).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1, mathlib 25730c7c); diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat .lake/packages manifest (simongmt 2b36630)`
- `python3 -I scans of dag.json (1523 nodes): slicing-a1 subtree and statuses; frozen types of chart_pieces, chart_coarea, eilenberg, im_calculus; nodes matching bi-Lipschitz|immersion|density point|Lebesgue density|blowUpMap|tangential gradient|co-area|Injective (fderiv; the dor_lmb...slicing-a1.slice_family-a1 subtree (lipschitz_chart_pieces, density_directions, piece_coarea, piece_slice_tangent, tangential_gradient)`
- `git show <commit>:GMT/Ch07/Submission.lean and whitespace-normalised type comparison for cmc_imRep_locality_restrict_sub (2af75d6), codim1_rdo_c1cov_local_lower_lipschitz (12e74ed), rsd_tendsto_closedBall_density_of_approxTangent (dbef2c1), dor_lmb_approx_tangent_locality (53d4678): all MATCH; nodes/*/accepted-candidate.json comparator_passed = true`
- `grep -c dtc_bc_lc_sl_co_ dag.json (0); git log --all -S 'dtc_bc_lc_sl_co_' over 6410 refs (no match); survey of 400 accepted candidate commits: added declarations are theorem Submission.*`
- `grep in the snapshot Mathlib: Besicovitch.ae_tendsto_measure_inter_div, MeasurableSet.image_of_continuousOn_injOn, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_smul, Measure.addHaar_closedBall, measure_inter_add_sdiff, lintegral_iUnion, lintegral_tsum, ENNReal.Tendsto.sub, ContinuousOn.measurable_piecewise, Measurable.find, ContinuousOn.preimage_isClosed_of_isClosed, InjOn.leftInvOn_invFunOn, ae_restrict_iUnion_iff, ae_restrict_union_iff, ae_restrict_iff', ae_lt_top', NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint_inner_left, toDual_symm_apply, IsCompact.exists_bound_of_continuousOn, LinearMap.isUnit_iff_ker_eq_bot`
- `grep in SimonGMT: Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, .unique, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono); Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn); Chapter04/TangentDensity.lean; no nonlinear co-area, tangential gradient or slicing declarations`
- `sed book/chapter-03.txt lines 300-460 (Remark 1.8, 2.1-2.10) and book/chapter-06.txt lines 1140-1200 (Lemma 4.1)`
- `Lean checks through a persistent LSP worker: #check availability file under import GMT.Ch07.Submission; /tmp/coarea_split/v2/ch/Challenge_<key>.lean (11 modules from gmt-compare.py child_modules, contract mode); /tmp/coarea_split/asm/Assembly3.lean; /tmp/coarea_split/agents/{A,B,C,D,E} hypothesis-form proofs; /tmp/coarea_split/e2e2/E2E_from_json.lean and E2E_solution.lean (end to end, comparator form)`
- `sed /runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py (_decompose depth gate, _dependency_problem, _existing_lean_name_problem) and prompts.py (DECOMPOSITION_AUDIT, RLCR_LEAN_TASK, LEAN_AUDIT, SPECULATIVE_PARENT_TASK)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-772be56655/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-09907e06c7/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-ec0e4b9204/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-3b0b44b19c6a/_recursive_lean/prompts.py`
- `/tmp/coarea_split/v2/ch`
- `/tmp/coarea_split/asm/Assembly3.lean`
- `/tmp/coarea_split/e2e2/E2E_from_json.lean`
- `/tmp/coarea_split/e2e2/E2E_solution.lean`

Neither the pinned SimonGMT library nor Mathlib has a nonlinear co-area formula, a tangential gradient of Lipschitz functions on rectifiable sets, or slicing. They do supply every tool cited in the child proofs: the Lebesgue density theorem, Lusin–Souslin, the Lipschitz image bound, the mean value inequality, Haar scaling, adjoints, continuity of Ring.inverse, and the countable-rectifiability lemmas. Three comparator-accepted DAG declarations are reused with identical types: cmc_imRep_locality_restrict_sub, codim1_rdo_c1cov_local_lower_lipschitz and rsd_tendsto_closedBall_density_of_approxTangent. dor_lmbsf_density_directions (accepted) overlaps one step of density_gradient_bound but is not needed. The eight new names are unreserved. All 11 types elaborate in the exact comparator challenge modules. Every new child is proved in Lean exactly as typed, both in hypothesis form and end to end. The exact frozen parent type is proved from the children and its resolved dependencies, using only propext, Classical.choice and Quot.sound.
