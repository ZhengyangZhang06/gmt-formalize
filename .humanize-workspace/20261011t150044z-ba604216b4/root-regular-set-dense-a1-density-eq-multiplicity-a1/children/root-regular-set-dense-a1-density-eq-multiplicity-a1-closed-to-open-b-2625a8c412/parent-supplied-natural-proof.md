# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.density_eq_multiplicity-a1`
- Child DAG node: `root.regular_set_dense-a1.density_eq_multiplicity-a1.closed_to_open_ball_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 (Open balls) of the parent proof. Simon Ch. 1, 3.1-3.2 (chapter-01.txt lines 561-592) observes that the n-dimensional densities may be computed with closed balls B_ρ(x) or with open balls. The frozen contract's docstring for HasMassDensity says the same: open and closed balls give the same limit. The parent's argument is the sandwich B̄_{tρ}(x) ⊆ B_ρ(x) ⊆ B̄_ρ(x), followed by t ↑ 1. Here it is carried out in the order topology of [0, ∞], which also covers θ = ∞.

Notation: ω := unitBallVolume n and c(ρ) := ω·ofReal(ρ^n). Let g(ρ) := ν(B̄_ρ(x))/c(ρ) and h(ρ) := ν(B_ρ(x))/c(ρ), all in [0, ∞]. By hypothesis g(ρ) → θ as ρ → 0 within (0, ∞). Below, eventually always refers to ρ → 0 within (0, ∞). By the characterisation of convergence in the order topology of [0, ∞] (tendsto_order), it suffices to prove:
- (U) for every b > θ, eventually h(ρ) < b;
- (L) for every a < θ, eventually h(ρ) > a.

1. (Upper bound (U).) For every ρ, B_ρ(x) ⊆ B̄_ρ(x), so ν(B_ρ(x)) ≤ ν(B̄_ρ(x)). Dividing both by the same c(ρ) gives h(ρ) ≤ g(ρ). Given b > θ, eventually g(ρ) < b because g → θ. Hence eventually h(ρ) ≤ g(ρ) < b.

2. (Choice of a dilation factor.) Let a < θ.
- As t → 1 from below, ofReal(t^n) → ofReal(1) = 1, by continuity of t ↦ t^n and of ofReal.
- Hence ofReal(t^n)·θ → 1·θ = θ. Multiplication by the constant θ is continuous at the limit 1 because 1 ≠ 0 (ENNReal.Tendsto.mul_const).
- Since a < θ, eventually (as t → 1⁻) a < ofReal(t^n)·θ; also eventually t ∈ (0, 1). Pick such a t.
Put τ := ofReal(t^n). Since 0 < t, τ ∈ (0, ∞), i.e. τ ≠ 0 and τ ≠ ∞. From a < τ·θ we get a/τ < θ (ENNReal.div_lt_iff).

3. (Rescaled ratio.) The map ρ ↦ tρ sends (0, ∞) into (0, ∞) and tends to 0 as ρ → 0, so it tends to 0 within (0, ∞). Composing with g → θ gives g(tρ) → θ as ρ → 0 within (0, ∞). Since a/τ < θ, eventually g(tρ) > a/τ.

4. (Scaling identity.) Let ρ > 0. Then (tρ)^n = t^n ρ^n with t^n ≥ 0, so ofReal((tρ)^n) = τ·ofReal(ρ^n) (ENNReal.ofReal_mul) and c(tρ) = ω·τ·ofReal(ρ^n). Two facts finish the computation:
- (ω·ofReal(ρ^n)·τ)^{-1} = (ω·ofReal(ρ^n))^{-1}·τ^{-1} (ENNReal.mul_inv, valid as τ ≠ 0, ∞);
- τ^{-1}·τ = 1 (ENNReal.inv_mul_cancel).
Together they give g(tρ)·τ = ν(B̄_{tρ}(x))/c(ρ).

5. (Lower bound (L).) Let ρ > 0 with g(tρ) > a/τ; this holds eventually by step 3. Since 0 < t < 1, tρ < ρ, so B̄_{tρ}(x) ⊆ B_ρ(x). Therefore
 a = (a/τ)·τ < g(tρ)·τ = ν(B̄_{tρ}(x))/c(ρ) ≤ ν(B_ρ(x))/c(ρ) = h(ρ).
The four relations use, in order:
- (a/τ)·τ = a (ENNReal.div_mul_cancel, τ ≠ 0, ∞);
- strict monotonicity of multiplication by τ ∈ (0, ∞) (ENNReal.mul_lt_mul_iff_left);
- step 4;
- monotonicity of ν.
Hence eventually h(ρ) > a.

6. Steps 1 and 5 give (U) and (L) for all b > θ and all a < θ. Hence h(ρ) → θ as ρ ↓ 0. ∎

Appendix (verified Lean realization of the numbered proof above). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c. It was placed after `import GMT.Ch07.Submission` in the child comparator scope, i.e. inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after the contract's `noncomputable section ... end`. `exact Submission.rsd_tendsto_ball_density_of_closedBall` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.rsd_tendsto_ball_density_of_closedBall : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (x : Euclid P) (θ : ℝ≥0∞), Tendsto (fun ρ : ℝ => ν (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => ν (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) := by
  intro P n ν x θ hg
  set ω := unitBallVolume n with hω
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- choose `t ∈ (0,1)` with `a < tⁿ θ`
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n) * θ) (𝓝[<] 1) (𝓝 (1 * θ)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
      have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ n))) :=
        (ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    rw [one_mul] at hlim
    obtain ⟨t, hta, ht0, ht1⟩ : ∃ t : ℝ, a < ENNReal.ofReal (t ^ n) * θ ∧ 0 < t ∧ t < 1 := by
      have h1 := (tendsto_order.1 hlim).1 a ha
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
      obtain ⟨t, ht, ht'⟩ := (h1.and h2).exists
      exact ⟨t, ht, ht'.1, ht'.2⟩
    have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hctop : ENNReal.ofReal (t ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
    have ha' : a / ENNReal.ofReal (t ^ n) < θ := by
      rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop), mul_comm]; exact hta
    -- the rescaled closed-ball ratio
    have hmap : Tendsto (fun ρ : ℝ => t * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun ρ : ℝ => t * ρ) (𝓝 0) (𝓝 0) := by
          have := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul t
          simpa using this
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ hρ
        exact mul_pos ht0 hρ
    have hev := (tendsto_order.1 (hg.comp hmap)).1 _ ha'
    filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
    simp only [Function.comp] at hρ
    have hρpos' : (0 : ℝ) < ρ := hρpos
    -- `ν(B̄_{tρ}) / (ω ρⁿ) = tⁿ · ν(B̄_{tρ}) / (ω (tρ)ⁿ)`
    have hid : ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n)
        = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := by
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (t ^ n)),
        ← mul_assoc, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0),
        mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    calc a = a / ENNReal.ofReal (t ^ n) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.div_mul_cancel hc0 hctop).symm
      _ < ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.mul_lt_mul_iff_left hc0 hctop).2 hρ
      _ = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := hid
      _ ≤ ν (ball x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) := by
          gcongr
          exact closedBall_subset_ball (by nlinarith)
  · filter_upwards [(tendsto_order.1 hg).2 b hb] with ρ hρ
    refine lt_of_le_of_lt ?_ hρ
    gcongr
    exact ball_subset_closedBall
```

## Key steps

1. B_ρ(x) ⊆ B̄_ρ(x) gives h ≤ g, hence the upper bound.
2. For a < θ, choose t ∈ (0,1) with a < t^n θ, using t^n θ → θ as t ↑ 1.
3. B̄_{tρ}(x) ⊆ B_ρ(x) and c(tρ) = t^n c(ρ) give h(ρ) ≥ t^n g(tρ) > a eventually.
4. Conclude by the order-topology characterisation of convergence in [0, ∞].

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem ae_tendsto_rnDeriv|theorem rnDeriv_withDensity\b|theorem restrict_withDensity\b|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem Isometry.euclideanHausdorffMeasure_image|theorem addHaar_closedBall\b|theorem addHaar_ball\b|theorem integral_indicator_one' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -n 'theorem\|lemma\|def \|notation\|instance' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -n 'HasApproximateTangentSpaceAt\|^def \|^theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; rg -n 'def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n -t lean 'HasApproximateTangentSpaceAt' simongmt/Poincare; rg -n -t lean 'theorem [A-Za-z_.]*(density|Density)[A-Za-z_.]*' simongmt/Poincare/SimonGMT/Chapter03 simongmt/Poincare/SimonGMT/Chapter04`
- `rg -n -t lean 'theorem .*IMRep|IMRep\.measure.*≠ ∞|locallyIntegrable_mult' local-references/123e8435b4a2469b/project`
- `python3 -I scan of dag.json lean_statement fields for closedBall|HasApproximateTangentSpaceAt|withDensity|unitBallVolume (overlap check with other DAG nodes)`
- `grep -l '<four proposed names>' dag.json issue-workers.json DAG.md GMT/Ch07/*.lean; rg -l -t lean '<four proposed names>' simongmt GMT local-references/123e8435b4a2469b/project; git grep -l -E '<four proposed names>' over all 101 refs -- GMT`
- `sed -n 500,595p verifier/gmt-compare.py (contract_scope / child_modules: child statements elaborate after import GMT.Ch07.Submission with the replayed contract opens)`
- `lake env lean /tmp/dem-split/Children.lean (four child types elaborate in the replayed comparator scope)`
- `lake env lean /tmp/dem-split/ChildAFacts.lean (Hn(Q ∩ B̄_r(0)) = unitBallVolume n * r^n and Hn(blowUpMap x r '' A) = r^-n Hn(A))`
- `lake env lean /tmp/dem-split/AllChildren.lean (full proofs of the four children, exact-type checks `exact Submission.<name>`, conditional assembly of the selected type from the children plus rsd_massOn_eq_measure as hypothesis; #print axioms)`
- `lake env lean /tmp/dem-split/out/Solo_<name>.lean for each of the four children (standalone compilation, #print axioms)`
- `book: sed -n 77,101p chapter-03.txt; sed -n 280,325p chapter-03.txt; sed -n 561,592p chapter-01.txt; sed -n 760,975p chapter-01.txt; sed -n 730,770p chapter-06.txt; sed -n 335,360p chapter-04.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1/parent-supplied-natural-proof.md`
- `/tmp/dem-split/Children.lean`
- `/tmp/dem-split/Assembly.lean`
- `/tmp/dem-split/ChildAFacts.lean`
- `/tmp/dem-split/ChildA.lean`
- `/tmp/dem-split/ChildB.lean`
- `/tmp/dem-split/ChildC.lean`
- `/tmp/dem-split/ChildD.lean`
- `/tmp/dem-split/AllChildren.lean`
- `/tmp/dem-split/out/Solo_rsd_tendsto_closedBall_density_of_approxTangent.lean`
- `/tmp/dem-split/out/Solo_rsd_ae_tendsto_withDensity_div_closedBall.lean`
- `/tmp/dem-split/out/Solo_rsd_tendsto_ball_density_of_closedBall.lean`
- `/tmp/dem-split/out/Solo_rsd_imrep_compact_measure_ne_top.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No ready-made lemma exists in the Ch07 environment for any of the four child facts:
- the project has only the IMRep structure fields (e.g. locallyIntegrable_mult) and no IMRep local-finiteness lemma;
- there is no open/closed-ball density transfer lemma and no localized Besicovitch statement;
- simongmt Chapter04/TangentDensity.lean has related lemmas (hausdorff_blowUp_image, blowUp_image_inter_closedBall, one_le_density_of_approximateTangent). They concern simongmt varifold weights, give only the lower bound d ≥ 1, and Chapter04 is not imported by the Ch07 contract, so they are not reused.

Library facts reused, located in the snapshot and exercised in compiled proofs:
- Besicovitch.ae_tendsto_rnDeriv (Covering/Besicovitch.lean:1078), Measure.rnDeriv_withDensity (Decomposition/Lebesgue.lean:591), restrict_withDensity (WithDensity.lean:215);
- Measure.addHaar_closedBall (Lebesgue/EqHaar.lean:500), integral_indicator_one (Bochner/Set.lean:533);
- in Geometry/Euclidean/Volume/Measure.lean: Isometry.euclideanHausdorffMeasure_image (line 131), Measure.euclideanHausdorffMeasure_smul₀ (line 152), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (line 187);
- simongmt HasApproximateTangentSpaceAt (Rectifiable.lean:102) and blowUpMap (Rectifiable.lean:96).

Verification:
- All four child types elaborate in the comparator scope, i.e. import GMT.Ch07.Submission plus the replayed contract opens (verifier/gmt-compare.py, contract_scope).
- Full Lean proofs of all four children compile standalone with exact Submission.<name> type checks.
- The conditional assembly of the selected frozen type from the four children plus rsd_massOn_eq_measure compiles.
- #print axioms reports only propext, Classical.choice and Quot.sound in every case.

The four names occur nowhere in dag.json, issue-workers.json, DAG.md, GMT/, the simongmt sources, the snapshot project, or any of the 101 git refs, so they collide with no reserved declaration.
