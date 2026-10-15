# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.coarea-a1.tangent_complement_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3(a) of the parent proof ("Density of M ∖ A_j"). There the cut-off φ ∈ C_c with φ = 1 on closedBall(0, 1) is integrated over η_{x,r}(M) and η_{x,r}(A_j) and the two limits ∫_T φ cancel. Here the same cut-off computation is used through the reused child unweighted_density (rsd_tendsto_closedBall_density_of_approxTangent; Simon Ch. 3, Remarks 1.5(3), 1.8(2)): the normalised H^N-masses of M and of A in closed balls both tend to 1, so that of M ∖ A tends to 0.
Notation: μ := H^N = μHE[N]; ω := unitBallVolume N = L^N of the open unit ball of ℝ^N; B̄_ρ := closedBall(x, ρ), B_ρ := ball(x, ρ); for ρ > 0, D(ρ) := ω·ofReal(ρ^N).

1. (Constants.) 0 < ω < ∞ (measure_ball_pos, measure_ball_lt_top). For ρ > 0, 0 < ofReal(ρ^N) < ∞, so D(ρ) ∈ (0, ∞).
2. (Finiteness.) μ(M ∩ B̄_s) < ∞ by hypothesis, and A ∩ B̄_s ⊆ M ∩ B̄_s, so μ(A ∩ B̄_s) < ∞. For 0 < ρ ≤ s the quantities μ(M ∩ B̄_ρ), μ(A ∩ B̄_ρ) and μ((M ∖ A) ∩ B̄_ρ) are finite (monotonicity).
3. (Splitting.) For every ρ, since A is measurable, measure_inter_add_sdiff gives μ(M ∩ B̄_ρ) = μ((M ∩ B̄_ρ) ∩ A) + μ((M ∩ B̄_ρ) ∖ A). As A ⊆ M, (M ∩ B̄_ρ) ∩ A = A ∩ B̄_ρ and (M ∩ B̄_ρ) ∖ A = (M ∖ A) ∩ B̄_ρ. So μ(M ∩ B̄_ρ) = μ(A ∩ B̄_ρ) + μ((M ∖ A) ∩ B̄_ρ).
4. (Densities.) Apply unweighted_density to (M, x, Q, s) and to (A, x, Q, s): the hypotheses are s > 0, the finiteness of step 2, and the two approximate tangent space assumptions. Hence
 a(ρ) := μ(M ∩ B̄_ρ)/D(ρ) → 1 and b(ρ) := μ(A ∩ B̄_ρ)/D(ρ) → 1 as ρ ↓ 0.
5. (Difference.) Put c(ρ) := μ((M ∖ A) ∩ B̄_ρ)/D(ρ). Dividing step 3 by D(ρ) (ENNReal.add_div) gives a(ρ) = b(ρ) + c(ρ). For 0 < ρ ≤ s, b(ρ) < ∞, so c(ρ) = a(ρ) − b(ρ) (truncated subtraction in [0, ∞], ENNReal.add_sub_cancel_left). Since a → 1, b → 1 and 1 ≠ ∞, ENNReal.Tendsto.sub gives a(ρ) − b(ρ) → 1 − 1 = 0. The identity c = a − b holds on (0, s] ∈ 𝓝[>] 0, so c(ρ) → 0 as ρ ↓ 0 (Tendsto.congr').
6. (Open balls, normalisation.) For ρ > 0, B_ρ ⊆ B̄_ρ, hence
 μ((M ∖ A) ∩ B_ρ)/ofReal(ρ^N) ≤ μ((M ∖ A) ∩ B̄_ρ)/ofReal(ρ^N) = ω·c(ρ),
 the equality because D(ρ) = ω·ofReal(ρ^N) with 0 < ω < ∞ (ENNReal.mul_div_mul_left). Since ω < ∞, ω·c(ρ) → ω·0 = 0 (ENNReal.Tendsto.const_mul). By the squeeze theorem with lower bound 0 (tendsto_of_tendsto_of_tendsto_of_le_of_le'), μ((M ∖ A) ∩ B_ρ)/ofReal(ρ^N) → 0 as ρ ↓ 0. ∎

Lean realization note. The verified code below follows steps 1–6 literally (s is the given radius; the identity c = a − b is used on (0, s]).

Appendix (verified Lean realization of the proof above). The code below compiles with Lean v4.35.0-rc3, Mathlib 25730c7c and simongmt 2b36630 when placed after `import GMT.Ch07.Submission` in the frozen contract scope (inside `namespace GMT.Ch07` with the contract's `open` commands, after the contract's `noncomputable section … end`), i.e. where accepted `theorem Submission.…` declarations live in GMT/Ch07/Submission.lean. It refers to the sibling declarations Submission.rsd_tendsto_closedBall_density_of_approxTangent (each with its exact frozen type, introduced by `have h_<key> : <type> := Submission.<name>` at the start of the proof). It was checked twice: (i) with the exact frozen sibling types as hypotheses, giving no errors and no warnings and `#print axioms` = [propext, Classical.choice, Quot.sound]; (ii) end to end, in one file containing all eight new children of dtc_bc_lc_sl_coarea in dependency order, the parent theorem proved from them, and `sorry` placeholders only for the reused accepted declarations and the parent's resolved dependencies (no warning from any child declaration). `Submission.dtc_bc_lc_sl_co_tangent_complement_density` has exactly the frozen type of this child.

```lean
theorem Submission.dtc_bc_lc_sl_co_tangent_complement_density : ∀ (P N : ℕ) (A M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), MeasurableSet A → A ⊆ M → 0 < s → μHE[N] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt N M x Q → HasApproximateTangentSpaceAt N A x Q → Tendsto (fun r : ℝ => μHE[N] ((M \ A) ∩ ball x r) / ENNReal.ofReal (r ^ N)) (𝓝[>] 0) (𝓝 0) := by
  have h_unweighted_density : (∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → μHE[n] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → Tendsto (fun ρ : ℝ => μHE[n] (M ∩ closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1)) := Submission.rsd_tendsto_closedBall_density_of_approxTangent
  intro P N A M x Q s hA hAM hs hMs hTM hTA
  -- Step 1: constants
  have hω0 : unitBallVolume N ≠ 0 := by
    show (volume : Measure (Euclid N)) (ball 0 1) ≠ 0
    exact (measure_ball_pos volume (0 : Euclid N) one_pos).ne'
  have hωtop : unitBallVolume N ≠ ∞ := by
    show (volume : Measure (Euclid N)) (ball 0 1) ≠ ∞
    exact measure_ball_lt_top.ne
  -- Step 2: finiteness
  have hAs : μHE[N] (A ∩ closedBall x s) ≠ ∞ :=
    ne_top_of_le_ne_top hMs (measure_mono (inter_subset_inter_left _ hAM))
  -- Step 4: the two density limits
  have ha := h_unweighted_density P N M x Q s hs hMs hTM
  have hb := h_unweighted_density P N A x Q s hs hAs hTA
  -- Step 3: splitting
  have hsplit : ∀ ρ : ℝ, μHE[N] (M ∩ closedBall x ρ)
      = μHE[N] (A ∩ closedBall x ρ) + μHE[N] ((M \ A) ∩ closedBall x ρ) := by
    intro ρ
    have e1 : M ∩ closedBall x ρ ∩ A = A ∩ closedBall x ρ := by
      ext y
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨⟨_, hy⟩, hyA⟩
        exact ⟨hyA, hy⟩
      · rintro ⟨hyA, hy⟩
        exact ⟨⟨hAM hyA, hy⟩, hyA⟩
    have e2 : (M ∩ closedBall x ρ) \ A = (M \ A) ∩ closedBall x ρ := by
      ext y
      simp only [mem_inter_iff, Set.mem_sdiff]
      tauto
    rw [← measure_inter_add_sdiff (μ := μHE[N]) (M ∩ closedBall x ρ) hA, e1, e2]
  -- Step 5: the difference quotient on closed balls tends to `0`
  have hc : Tendsto (fun ρ : ℝ => μHE[N] ((M \ A) ∩ closedBall x ρ)
      / (unitBallVolume N * ENNReal.ofReal (ρ ^ N))) (𝓝[>] 0) (𝓝 0) := by
    have hsub := ENNReal.Tendsto.sub ha hb (Or.inl ENNReal.one_ne_top)
    rw [tsub_self] at hsub
    refine hsub.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hs] with ρ hρ
    have hD : unitBallVolume N * ENNReal.ofReal (ρ ^ N) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hρ.1 N)).ne'
    have hbfin : μHE[N] (A ∩ closedBall x ρ) / (unitBallVolume N * ENNReal.ofReal (ρ ^ N)) ≠ ∞ :=
      ENNReal.div_ne_top (ne_top_of_le_ne_top hAs
        (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hρ.2)))) hD
    rw [hsplit ρ, ENNReal.add_div, ENNReal.add_sub_cancel_left hbfin]
  -- Step 6: pass to open balls and renormalise
  have hlim := ENNReal.Tendsto.const_mul hc (Or.inr hωtop)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun ρ => ?_)
  rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hω0 hωtop]
  exact ENNReal.div_le_div_right (measure_mono (inter_subset_inter_right _ ball_subset_closedBall)) _
```

## Key steps

1. μ(M ∩ B̄_ρ) = μ(A ∩ B̄_ρ) + μ((M ∖ A) ∩ B̄_ρ) (A measurable, A ⊆ M), all finite for ρ ≤ s.
2. unweighted_density for M and for A: both normalised closed-ball densities tend to 1.
3. Subtract in [0, ∞] (finite limits): the normalised density of M ∖ A in closed balls tends to 0.
4. Pass to open balls (monotonicity) and multiply by ω: H^N((M ∖ A) ∩ B_r(x))/r^N → 0.
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
