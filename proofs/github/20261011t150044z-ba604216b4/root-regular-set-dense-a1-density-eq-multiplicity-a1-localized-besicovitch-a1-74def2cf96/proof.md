# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.density_eq_multiplicity-a1`
- Child DAG node: `root.regular_set_dense-a1.density_eq_multiplicity-a1.localized_besicovitch-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 (Lebesgue differentiation) of the parent proof. This is Simon Ch. 1, Theorem 3.16 and Corollary 3.17 (chapter-01.txt lines 907-975). By Remark 3.11(3) (lines 797-854, the Besicovitch covering lemma) they apply to every Borel measure on ℝ^P that is finite on compact sets. In Mathlib the differentiation theorem with closed balls is Besicovitch.ae_tendsto_rnDeriv. Since μ need not be locally finite near the boundary of U, the theorem is applied to the restrictions of μ and ν to a compact exhaustion of U, exactly as in the parent proof. The exhaustion used here also works when U = ℝ^P.

Notation: ν := μ.withDensity θ. All balls B̄_ρ(x) are closed and B_ρ(x) open; quotients are in [0, ∞].

1. (Exhaustion.) For j ∈ ℕ put r_j := 1/(j+1) and
 K_j := B̄_{j+1}(0) ∩ {y : dist(y, z) ≥ r_j for every z ∈ ℝ^P ∖ U}.
- The second set is the intersection, over z ∉ U, of the closed sets {y : r_j ≤ dist(y, z)}. So K_j is closed.
- K_j is bounded, hence compact (ℝ^P is proper), and Borel.
- K_j ⊆ U: if y ∈ K_j and y ∉ U, then taking z = y gives r_j ≤ dist(y, y) = 0 < r_j, a contradiction.
When U = ℝ^P the condition is vacuous and K_j = B̄_{j+1}(0).

2. (Every point of U lies inside some K_j.) Let x ∈ U. Choose δ > 0 with B_δ(x) ⊆ U, and j ∈ ℕ with j > max{2/δ, |x|}. Then j + 1 > 2/δ, i.e. 2r_j < δ, and |x| < j. Let y ∈ B_{r_j}(x).
- |y| ≤ |x| + dist(y, x) < |x| + r_j ≤ |x| + 1 < j + 1, so y ∈ B̄_{j+1}(0).
- For z ∉ U, dist(x, z) ≥ δ, since otherwise z ∈ B_δ(x) ⊆ U. So dist(y, z) ≥ dist(x, z) − dist(x, y) > δ − r_j > 2r_j − r_j = r_j.
Hence B_{r_j}(x) ⊆ K_j.

3. (Finite localized measures.) Fix j and set μ_j := μ⌞K_j and ν_j := ν⌞K_j.
- K_j is measurable, so ν_j = (μ.withDensity θ)⌞K_j = (μ⌞K_j).withDensity θ = μ_j.withDensity θ (restrict_withDensity).
- K_j is a compact subset of U (step 1), so by the hypotheses μ_j(ℝ^P) = μ(K_j) < ∞ and ν_j(ℝ^P) = ν(K_j) < ∞.
So μ_j and ν_j are finite measures; in particular they are locally finite and σ-finite.

4. (Differentiation on K_j.) By the Besicovitch differentiation theorem (Simon 3.16-3.17 with 3.11(3); Besicovitch.ae_tendsto_rnDeriv on the finite-dimensional space ℝ^P), for μ_j-a.e. x,
 ν_j(B̄_ρ(x))/μ_j(B̄_ρ(x)) → (dν_j/dμ_j)(x) as ρ ↓ 0.
Since μ_j is σ-finite and θ is measurable, dν_j/dμ_j = d(μ_j.withDensity θ)/dμ_j = θ μ_j-a.e. (Measure.rnDeriv_withDensity). Intersecting these two μ_j-full sets: for μ_j-a.e. x, ν_j(B̄_ρ(x))/μ_j(B̄_ρ(x)) → θ(x).

5. (Back to μ.) K_j is measurable, so a property holds μ⌞K_j-a.e. iff it holds μ-a.e. on K_j (ae_restrict_iff'). So for each j and μ-a.e. x, x ∈ K_j implies the convergence of step 4. There are countably many j, so for μ-a.e. x this implication holds simultaneously for all j (ae_all_iff).

6. (Conclusion.) Let x be such a point with x ∈ U. Choose j as in step 2, so B_{r_j}(x) ⊆ K_j. In particular x ∈ K_j, so ν_j(B̄_ρ(x))/μ_j(B̄_ρ(x)) → θ(x). For 0 < ρ < r_j we have B̄_ρ(x) ⊆ B_{r_j}(x) ⊆ K_j. Since closed balls are measurable (Measure.restrict_apply), this gives μ_j(B̄_ρ(x)) = μ(B̄_ρ(x) ∩ K_j) = μ(B̄_ρ(x)), and likewise ν_j(B̄_ρ(x)) = ν(B̄_ρ(x)). So the two ratio functions agree on the right-neighbourhood (0, r_j) of 0, and ν(B̄_ρ(x))/μ(B̄_ρ(x)) → θ(x) as ρ ↓ 0. ∎

Appendix (verified Lean realization of the numbered proof above). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c. It was placed after `import GMT.Ch07.Submission` in the child comparator scope, i.e. inside `namespace GMT.Ch07` with the frozen contract's `open` commands, after the contract's `noncomputable section ... end`. `exact Submission.rsd_ae_tendsto_withDensity_div_closedBall` closes the frozen type, and `#print axioms` reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.rsd_ae_tendsto_withDensity_div_closedBall : ∀ (P : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (θ : Euclid P → ℝ≥0∞), IsOpen U → Measurable θ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ.withDensity θ K ≠ ∞) → ∀ᵐ x ∂μ, x ∈ U → Tendsto (fun ρ : ℝ => μ.withDensity θ (closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 (θ x)) := by
  intro P U μ θ hU hθ hμK hνK
  -- the compact exhaustion `K j`
  set K : ℕ → Set (Euclid P) := fun j =>
    closedBall 0 ((j : ℝ) + 1) ∩ {y | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} with hKdef
  have hKclosed' : ∀ j : ℕ, IsClosed {y : Euclid P | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} := by
    intro j
    have : {y : Euclid P | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} =
        ⋂ z ∈ Uᶜ, {y | 1 / ((j : ℝ) + 1) ≤ dist y z} := by
      ext y; simp
    rw [this]
    exact isClosed_biInter fun z _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKclosed : ∀ j, IsClosed (K j) := fun j => isClosed_closedBall.inter (hKclosed' j)
  have hKcpt : ∀ j, IsCompact (K j) := fun j =>
    (isCompact_closedBall (0 : Euclid P) _).inter_right (hKclosed' j)
  have hKU : ∀ j, K j ⊆ U := by
    intro j y hy
    by_contra hyU
    have h := hy.2 y hyU
    rw [dist_self] at h
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  have hcover : ∀ x ∈ U, ∃ j : ℕ, ball x (1 / ((j : ℝ) + 1)) ⊆ K j := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨j, hj⟩ := exists_nat_gt (max (2 / δ) ‖x‖)
    have hj1 : 2 / δ < (j : ℝ) + 1 := by
      have := le_max_left (2 / δ) ‖x‖; linarith
    have hj2 : ‖x‖ < (j : ℝ) := lt_of_le_of_lt (le_max_right _ _) hj
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hsmall : 2 / ((j : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ hjpos]
      rw [div_lt_iff₀ hδ] at hj1
      linarith
    refine ⟨j, fun y hy => ⟨?_, ?_⟩⟩
    · rw [mem_closedBall, dist_zero_right]
      have h1 : ‖y‖ ≤ ‖x‖ + dist y x := by
        have := norm_le_norm_add_norm_sub' y x
        rw [dist_eq_norm]; linarith [norm_sub_rev y x]
      have h2 : dist y x < 1 / ((j : ℝ) + 1) := hy
      have h3 : 1 / ((j : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hjpos]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      linarith
    · intro z hz
      have hxz : δ ≤ dist x z := by
        by_contra h
        exact hz (hball (by rw [mem_ball, dist_comm]; linarith))
      have h2 : dist y x < 1 / ((j : ℝ) + 1) := hy
      have htri := dist_triangle x y z
      have h4 : 2 / ((j : ℝ) + 1) = 2 * (1 / ((j : ℝ) + 1)) := by ring
      rw [dist_comm] at h2
      linarith
  -- Besicovitch on each `K j`
  have hj : ∀ j : ℕ, ∀ᵐ x ∂μ, x ∈ K j → Tendsto (fun ρ : ℝ =>
      ((μ.withDensity θ).restrict (K j)) (closedBall x ρ) / (μ.restrict (K j)) (closedBall x ρ))
      (𝓝[>] 0) (𝓝 (θ x)) := by
    intro j
    have hKm : MeasurableSet (K j) := (hKclosed j).measurableSet
    have : IsFiniteMeasure (μ.restrict (K j)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hμK _ (hKcpt j) (hKU j)).lt_top⟩
    have : IsFiniteMeasure ((μ.withDensity θ).restrict (K j)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hνK _ (hKcpt j) (hKU j)).lt_top⟩
    have h1 := Besicovitch.ae_tendsto_rnDeriv ((μ.withDensity θ).restrict (K j)) (μ.restrict (K j))
    have h2 := Measure.rnDeriv_withDensity (μ.restrict (K j)) hθ
    rw [← restrict_withDensity hKm] at h2
    have h3 : ∀ᵐ x ∂(μ.restrict (K j)), Tendsto (fun ρ : ℝ =>
        ((μ.withDensity θ).restrict (K j)) (closedBall x ρ) / (μ.restrict (K j)) (closedBall x ρ))
        (𝓝[>] 0) (𝓝 (θ x)) := by
      filter_upwards [h1, h2] with x hx1 hx2
      rwa [hx2] at hx1
    exact (ae_restrict_iff' hKm).1 h3
  filter_upwards [ae_all_iff.2 hj] with x hx hxU
  obtain ⟨j, hjK⟩ := hcover x hxU
  have hr : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hxK : x ∈ K j := hjK (mem_ball_self hr)
  refine (hx j hxK).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ
  have hsub : closedBall x ρ ⊆ K j := (closedBall_subset_ball hρ.2).trans hjK
  rw [Measure.restrict_apply measurableSet_closedBall, Measure.restrict_apply measurableSet_closedBall,
    inter_eq_left.2 hsub]
```

## Key steps

1. Take the compact exhaustion K_j = B̄_{j+1}(0) ∩ {y : dist(y, z) ≥ 1/(j+1) for all z ∉ U} ⊆ U. Each x ∈ U has B_{1/(j+1)}(x) ⊆ K_j for some j.
2. μ⌞K_j and ν⌞K_j = (μ⌞K_j).withDensity θ are finite measures.
3. Besicovitch.ae_tendsto_rnDeriv and Measure.rnDeriv_withDensity give ν_j(B̄_ρ)/μ_j(B̄_ρ) → θ for μ_j-a.e. x.
4. Combine the countably many null sets. Small closed balls around x lie in K_j, so the localized ratios equal the global ones.

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
