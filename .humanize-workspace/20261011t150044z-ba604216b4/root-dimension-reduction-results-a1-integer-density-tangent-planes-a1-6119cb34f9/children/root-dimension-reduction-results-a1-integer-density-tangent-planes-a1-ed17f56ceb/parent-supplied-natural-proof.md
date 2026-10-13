# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.density_eq_multiplicity_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.density_eq_multiplicity_ae-a1.density_on_carrier-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1 and 4–7 of the parent proof. These are Simon Ch. 3, Remarks 1.8(1)–(2) and Theorem 1.9 (chapter-03.txt lines 298–325), with the Upper Density Theorem of Ch. 1, 3.6 and 3.7(2) (chapter-01.txt lines 698–721).

The parent's argument is specialized in two ways:
- θ is ℕ-valued. So the Lusin sets M_j of parent step 4 (compact, with θ|M_j continuous) are replaced by the level sets M_k := M ∩ θ^{-1}(k), k ∈ ℕ. These are Borel, θ ≡ k on M_k is trivially continuous, and they cover M exactly, so Lusin's theorem is not needed. Parent steps 5–7 then apply with M_j := M_k; in step 7 the ε of continuity is 0.
- ν := H^n⌞M ≤ μ_R (step 1 below). So the vanishing of D(μ_R⌞(M ∖ M_k), x) implies that of D(ν⌞(M ∖ M_k), x), and the upper density theorem is applied once for each k, with λ = μ_R.
The parent's hypothesis n ≥ 1 is not needed.

Siblings used:
- upper_density_zero (Submission.idtp_dema_upper_density_zero). For every measure λ on ℝ^P that is finite on compact sets and every Borel A ⊆ ℝ^P: for H^n-a.e. x with x ∉ A, λ(A ∩ B_ρ(x))/c(ρ) → 0.
- tangent_density_one (Submission.rsd_tendsto_closedBall_density_of_approxTangent). If s > 0, H^n(M ∩ B̄_s(x)) ≠ ∞ and HasApproximateTangentSpaceAt n M x Q, then H^n(M ∩ B̄_ρ(x))/c(ρ) → 1.
- closed_to_open_ball_density (Submission.rsd_tendsto_ball_density_of_closedBall). For every measure ν', point x and θ' ∈ [0, ∞]: if ν'(B̄_ρ(x))/c(ρ) → θ', then ν'(B_ρ(x))/c(ρ) → θ'.

Notation.
- H^n := μHE[n] on ℝ^P.
- M := R.carrier, Borel by the field measurableSet_carrier.
- θ := R.mult : ℝ^P → ℕ, measurable by the field measurable_mult.
- ν := H^n⌞M and μ := R.measure = ν.withDensity θ.
- c(ρ) := ω·ofReal(ρ^n) with ω := unitBallVolume n.
- B_ρ(x) is the open ball and B̄_ρ(x) the closed ball.
- All limits are taken as ρ ↓ 0 (filter 𝓝[>] 0) in [0, ∞].
For every Borel S: μ(S) = ∫_{S∩M} θ dH^n (withDensity_apply, Measure.restrict_restrict), and ν(S) = H^n(S ∩ M) (Measure.restrict_apply).

1. (Local finiteness, parent step 1.) For every Borel S, ν(S) ≤ μ(S). Indeed θ(y) ≥ 1 for y ∈ M (field mult_pos, θ ℕ-valued), so
 ν(S) = ∫_{S∩M} 1 dH^n ≤ ∫_{S∩M} θ dH^n = μ(S) (setLIntegral_mono').
In particular, for every x, H^n(M ∩ B̄_1(x)) = ν(B̄_1(x)) ≤ μ(B̄_1(x)) < ∞, since B̄_1(x) is compact.

2. (Level sets; parent step 4 specialized.) For k ∈ ℕ let A_k := M ∩ θ^{-1}(ℕ ∖ {k}) = M ∖ M_k. It is Borel, since M is Borel and θ is measurable.

3. (Upper densities; parent steps 2 and 4.) Apply upper_density_zero with λ := μ, which is finite on compact sets by hypothesis, and the Borel set A_k. For each k this gives: for H^n-a.e. x, if x ∉ A_k then e_k(ρ) := μ(A_k ∩ B_ρ(x))/c(ρ) → 0. As there are countably many k (ae_all_iff), for H^n-a.e. x this holds simultaneously for all k with x ∉ A_k.

4. (Density of ν; parent steps 5–6.) The field orients of R says: for ν-a.e. x there is a subspace Q with HasApproximateTangentSpaceAt n M x Q (and IsUnitOrientationOf (R.orient x) Q, which is not needed). Since M is Borel, this means: for H^n-a.e. x, if x ∈ M then such a Q exists (ae_restrict_iff'). Fix such x ∈ M and Q.
- By step 1, H^n(M ∩ B̄_1(x)) ≠ ∞. So tangent_density_one with s = 1 gives H^n(M ∩ B̄_ρ(x))/c(ρ) → 1.
- Since ν(B̄_ρ(x)) = H^n(B̄_ρ(x) ∩ M) = H^n(M ∩ B̄_ρ(x)), this says ν(B̄_ρ(x))/c(ρ) → 1.
- closed_to_open_ball_density, applied to the measure ν with θ' = 1, gives b(ρ) := ν(B_ρ(x))/c(ρ) → 1.

5. (Splitting the ball; parent step 7.) Let x ∈ M be a point at which steps 3 and 4 hold; this is the case for H^n-a.e. x ∈ M. Let k := θ(x) and T := θ^{-1}(k), a Borel set. Then x ∉ A_k, so e_k(ρ) → 0 by step 3. Fix ρ and write B := B_ρ(x). The set B ∩ M is the disjoint union of (B ∩ M) ∩ T and (B ∩ M) ∖ T = (A_k ∩ B) ∩ M, and θ ≡ k on T. Hence (lintegral_inter_add_sdiff, setLIntegral_congr_fun, lintegral_const)
 μ(B) = ∫_{(B∩M)∩T} θ dH^n + ∫_{(B∩M)∖T} θ dH^n = k·H^n((B ∩ M) ∩ T) + μ(A_k ∩ B).
Similarly (measure_inter_add_sdiff)
 ν(B) = H^n((B ∩ M) ∩ T) + ν(A_k ∩ B).
Now use H^n((B ∩ M) ∩ T) ≤ H^n(B ∩ M) = ν(B), and ν(A_k ∩ B) ≤ μ(A_k ∩ B) (step 1). This gives
 (U) μ(B) ≤ k·ν(B) + μ(A_k ∩ B);
 (L) k·ν(B) ≤ μ(B) + k·μ(A_k ∩ B).

6. (Limits.) Let a(ρ) := μ(B_ρ(x))/c(ρ). Divide (U) and (L) by c(ρ) (ENNReal.div_le_div_right, ENNReal.add_div, mul_div_assoc). This gives
 k·b(ρ) − k·e_k(ρ) ≤ a(ρ) ≤ k·b(ρ) + e_k(ρ),
where the left inequality is (L) rewritten with truncated subtraction (tsub_le_iff_right). Since k ∈ ℕ is finite, b(ρ) → 1 and e_k(ρ) → 0:
- k·b(ρ) + e_k(ρ) → k·1 + 0 = k (ENNReal.Tendsto.const_mul, Tendsto.add);
- k·b(ρ) − k·e_k(ρ) → k − 0 = k (ENNReal.Tendsto.sub, the limit k being finite).
By the squeeze theorem, a(ρ) → k = θ(x).

7. (Conclusion.) The set of x ∈ M at which the conclusion fails lies in the union of the H^n-null exceptional sets of steps 3 and 4. Hence for H^n-a.e. x with x ∈ M, μ(B_ρ(x))/c(ρ) → θ(x). ∎

Appendix (verified Lean realization of the numbered proof above; context, not part of the numbered proof). The declaration below compiles with Lean v4.35.0-rc3 and Mathlib 25730c7c in the same scope as the frozen contract (after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open` commands), once the three sibling declarations Submission.idtp_dema_upper_density_zero, Submission.rsd_tendsto_closedBall_density_of_approxTangent and Submission.rsd_tendsto_ball_density_of_closedBall are present. It is a single declaration and `#print axioms` (with the siblings' verified proofs) reports only propext, Classical.choice and Quot.sound.

```lean
theorem Submission.idtp_dema_density_on_carrier : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), (∀ K : Set (Euclid P), IsCompact K → R.measure K ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ R.carrier → Tendsto (fun ρ : ℝ => R.measure (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (R.mult x : ℝ≥0∞)) := by
  intro P n U R hfin
  set M := R.carrier with hM
  have hMm : MeasurableSet M := R.measurableSet_carrier
  set ν : Measure (Euclid P) := (μHE[n] : Measure (Euclid P)).restrict M with hν
  -- the weight as a set integral
  have hmeas : ∀ S : Set (Euclid P), MeasurableSet S →
      R.measure S = ∫⁻ y in S ∩ M, (R.mult y : ℝ≥0∞) ∂μHE[n] := by
    intro S hS
    simp only [IMRep.measure]
    rw [withDensity_apply _ hS, Measure.restrict_restrict hS]
  -- Step 1: ν ≤ μ_R on measurable sets (θ ≥ 1 on M)
  have hνle : ∀ S : Set (Euclid P), MeasurableSet S → ν S ≤ R.measure S := by
    intro S hS
    rw [hmeas S hS, hν, Measure.restrict_apply hS]
    calc μHE[n] (S ∩ M) = ∫⁻ _y in S ∩ M, (1 : ℝ≥0∞) ∂μHE[n] := by simp
      _ ≤ ∫⁻ y in S ∩ M, (R.mult y : ℝ≥0∞) ∂μHE[n] := by
        apply setLIntegral_mono' (hS.inter hMm)
        intro y hy
        have h := R.mult_pos y hy.2
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr h.ne'
  -- Step 2: the level sets
  set A : ℕ → Set (Euclid P) := fun k => M ∩ R.mult ⁻¹' ({k}ᶜ) with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hMm.inter (R.measurable_mult (measurableSet_singleton k).compl)
  -- Step 3: upper density of μ_R ⌞ A k vanishes off A k
  have hUD : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ k : ℕ, x ∉ A k →
      Tendsto (fun ρ : ℝ => R.measure (A k ∩ ball x ρ) /
        (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 0) :=
    ae_all_iff.2 fun k => Submission.idtp_dema_upper_density_zero P n R.measure (A k) (hAm k) hfin
  -- Step 4: tangent planes
  have htan : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M →
      ∃ Q, HasApproximateTangentSpaceAt n M x Q := by
    have h := R.orients
    rw [ae_restrict_iff' hMm] at h
    filter_upwards [h] with x hx hxM
    obtain ⟨Q, hQ, -⟩ := hx hxM
    exact ⟨Q, hQ⟩
  filter_upwards [hUD, htan] with x hxUD hxtan hxM
  obtain ⟨Q, hQ⟩ := hxtan hxM
  set k : ℕ := R.mult x with hk
  have hxA : x ∉ A k := fun h => h.2 (by simp [hk])
  have he := hxUD k hxA
  -- density of ν is one
  have hfinball : μHE[n] (M ∩ closedBall x 1) ≠ ∞ := by
    have h1 := hνle (closedBall x 1) measurableSet_closedBall
    have h2 := hfin (closedBall x 1) (isCompact_closedBall x 1)
    rw [hν, Measure.restrict_apply measurableSet_closedBall] at h1
    rw [inter_comm]
    exact ne_top_of_le_ne_top h2 h1
  have hTD := Submission.rsd_tendsto_closedBall_density_of_approxTangent P n M x Q 1 one_pos
    hfinball hQ
  have hTD' : Tendsto (fun ρ : ℝ => ν (closedBall x ρ) /
      (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
    refine hTD.congr fun ρ => ?_
    rw [hν, Measure.restrict_apply measurableSet_closedBall, inter_comm]
  have hb := Submission.rsd_tendsto_ball_density_of_closedBall P n ν x 1 hTD'
  -- Step 5: the two inequalities
  set T : Set (Euclid P) := R.mult ⁻¹' {k} with hT
  have hTm : MeasurableSet T := R.measurable_mult (measurableSet_singleton k)
  have hsplit : ∀ ρ : ℝ, R.measure (ball x ρ) =
      (k : ℝ≥0∞) * μHE[n] ((ball x ρ ∩ M) ∩ T) + R.measure (A k ∩ ball x ρ) := by
    intro ρ
    rw [hmeas _ measurableSet_ball, hmeas _ ((hAm k).inter measurableSet_ball),
      ← lintegral_inter_add_sdiff (B := T) _ _ hTm]
    congr 1
    · rw [setLIntegral_congr_fun ((measurableSet_ball.inter hMm).inter hTm)
        (g := fun _ => (k : ℝ≥0∞)) (fun y hy => by
          have : R.mult y = k := hy.2
          simp [this])]
      simp
    · have hset : (ball x ρ ∩ M) \ T = (A k ∩ ball x ρ) ∩ M := by
        ext y
        simp only [hA, hT, mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_compl_iff,
          mem_singleton_iff]
        tauto
      rw [hset]
  have hνsplit : ∀ ρ : ℝ, ν (ball x ρ) =
      μHE[n] ((ball x ρ ∩ M) ∩ T) + ν (A k ∩ ball x ρ) := by
    intro ρ
    rw [hν, Measure.restrict_apply measurableSet_ball,
      Measure.restrict_apply ((hAm k).inter measurableSet_ball),
      ← measure_inter_add_sdiff (ball x ρ ∩ M) hTm]
    have hset : (ball x ρ ∩ M) \ T = (A k ∩ ball x ρ) ∩ M := by
      ext y
      simp only [hA, hT, mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_compl_iff,
        mem_singleton_iff]
      tauto
    rw [hset]
  have hup : ∀ ρ : ℝ, R.measure (ball x ρ) ≤
      (k : ℝ≥0∞) * ν (ball x ρ) + R.measure (A k ∩ ball x ρ) := by
    intro ρ
    rw [hsplit ρ]
    have h1 : μHE[n] ((ball x ρ ∩ M) ∩ T) ≤ ν (ball x ρ) := by
      rw [hν, Measure.restrict_apply measurableSet_ball]
      exact measure_mono inter_subset_left
    exact add_le_add (mul_le_mul_right h1 _) le_rfl
  have hlow : ∀ ρ : ℝ, (k : ℝ≥0∞) * ν (ball x ρ) ≤
      R.measure (ball x ρ) + (k : ℝ≥0∞) * R.measure (A k ∩ ball x ρ) := by
    intro ρ
    rw [hνsplit ρ, mul_add, hsplit ρ, add_assoc]
    have h2 := hνle (A k ∩ ball x ρ) ((hAm k).inter measurableSet_ball)
    exact add_le_add le_rfl ((mul_le_mul_right h2 _).trans le_add_self)
  -- limits
  set c : ℝ → ℝ≥0∞ := fun ρ => unitBallVolume n * ENNReal.ofReal (ρ ^ n) with hc
  have hk_top : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  have hupper : Tendsto (fun ρ => (k : ℝ≥0∞) * (ν (ball x ρ) / c ρ) +
      R.measure (A k ∩ ball x ρ) / c ρ) (𝓝[>] 0) (𝓝 (k : ℝ≥0∞)) := by
    have := (ENNReal.Tendsto.const_mul hb (Or.inr hk_top)).add he
    simpa using this
  have hlower : Tendsto (fun ρ => (k : ℝ≥0∞) * (ν (ball x ρ) / c ρ) -
      (k : ℝ≥0∞) * (R.measure (A k ∩ ball x ρ) / c ρ)) (𝓝[>] 0) (𝓝 (k : ℝ≥0∞)) := by
    have h1 := ENNReal.Tendsto.const_mul hb (Or.inr hk_top)
    have h2 := ENNReal.Tendsto.const_mul he (Or.inr hk_top)
    have := ENNReal.Tendsto.sub h1 h2 (Or.inl (by simp))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun ρ => ?_) (fun ρ => ?_)
  · -- lower bound
    simp only
    rw [tsub_le_iff_right, ← mul_div_assoc, ← mul_div_assoc, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hlow ρ) _
  · simp only
    rw [← mul_div_assoc, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hup ρ) _
```

## Key steps

1. θ ≥ 1 on M gives ν := H^n⌞M ≤ μ_R on Borel sets; hence H^n(M ∩ B̄_1(x)) < ∞ for every x.
2. The level sets M ∩ θ^{-1}(k) replace the Lusin sets of the parent; sibling upper_density_zero with λ = μ_R and A_k = M ∩ θ^{-1}(ℕ ∖ {k}) gives μ_R(A_k ∩ B_ρ(x)) = o(ρ^n) for H^n-a.e. x ∉ A_k, for all k at once.
3. Field orients with siblings tangent_density_one (s = 1) and closed_to_open_ball_density gives ν(B_ρ(x))/(ω_nρ^n) → 1 for H^n-a.e. x ∈ M.
4. At such x with k = θ(x) and B = B_ρ(x): μ_R(B) = k·H^n(B ∩ M ∩ θ^{-1}(k)) + μ_R(A_k ∩ B), whence μ_R(B) ≤ kν(B) + μ_R(A_k ∩ B) and kν(B) ≤ μ_R(B) + kμ_R(A_k ∩ B).
5. Divide by ω_nρ^n and squeeze: μ_R(B_ρ(x))/(ω_nρ^n) → θ(x).

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `python3 scan of dag.json: accepted lean_names; accepted lean_statements matching density|dilation|lusin|ApproximateTangent|withDensity|ball; statements with 'x ∉' + Tendsto … (𝓝 0) or '.measure (ball x'; dependency closure of root.dimension_reduction_results-a1 and of integer_density_tangent_planes-a1`
- `grep -rl 'so the controller reuses that node|reused here by exact name and frozen type|reused at its byte-identical frozen type' nodes/*/decomposition-v*.json (cross-branch reuse precedent); grep -l rsd_tendsto_closedBall_density_of_approxTangent nodes/*/decomposition-v*.json`
- `git show 1d91497901e9a040bb92dab7cea2968379e0e3a2:GMT/Ch07/Submission.lean (proof base = bare contract); git show dbef2c15948a21d9574315bea458a9edb4f708e3 / c3ca64f29e6259bb0947d084036f55b096f91e3f / 031b5125695febe04a82aacb729a15164ef02960:GMT/Ch07/Submission.lean (accepted rsd_* and regcomp_atl_upper_density_zero proofs); accepted-candidate.json and isolated-comparator-result.json of the two reused nodes`
- `grep -n 'theorem|def' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{DensityComparison,Densities,Basic,Hausdorff}.lean (ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite, simon_theorem_3_6, dimensionalUpperDensity, simonHausdorffMeasureReal, IsBorelRegularOuterMeasure, IsOpenSigmaFinite); grep realUnitBallVolume_pos|realUnitBallVolume_ne_top; sed Chapter04/WeightedDensity.lean`
- `grep -n 'def HasApproximateTangentSpaceAt' -A 14 .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn euclideanHausdorffMeasure local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep add_div|div_le_div_right in Mathlib/Basic/ENNReal/Inv.lean; grep mul_le_mul_right in Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean; grep mul_div_assoc in Mathlib/Algebra/Group/DivInvMonoid.lean`
- `sed -n 575,740p book/chapter-01.txt (Simon 1.3.2–3.8); sed -n 240,345p book/chapter-03.txt (Simon 3.1.7–1.9)`
- `grep -rl idtp_dema over the run directory and .swarm-worktrees/*/gmt-ch07/GMT (no match)`
- `lake env lean /tmp/idtp_dema_check/{Probe,OnCarrier,UpperDensity,FullCheck,FromJsonStubs,FromJsonFull}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-6119cb34f9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-6119cb34f9/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-scope-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invariance-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-unweighted-density-one-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1-closed-to-open-b-2625a8c412/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-density-eq-multiplicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Group/DivInvMonoid.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/idtp_dema_check/FromJsonStubs.lean`
- `/tmp/idtp_dema_check/FromJsonFull.lean`

Pins match: workspace HEAD b4d606d equals the snapshot's project commit, mathlib is 25730c7c and SimonGMT is 2b36630; Contract.lean, Submission.lean and the snapshot contract are byte-identical. The proof base 1d91497 contains only the contract. Reusable accepted declarations (other branch, byte-identical types, isolated comparator passed): rsd_tendsto_closedBall_density_of_approxTangent (density one at approximate-tangent points, closed balls; candidate dbef2c1) and rsd_tendsto_ball_density_of_closedBall (closed to open balls; candidate c3ca64f). Both are already prerequisites of the accepted dimred_mono_ae_ball_density_ge_one in this branch. No accepted declaration gives the upper density theorem for a general locally finite measure: regcomp_atl_upper_density_zero, regcomp_atl_local_density_zero and doraggt_local_density_zero cover only H^n⌞S. Its Vitali-based Lean proof (031b512) was adapted to arbitrary μ finite on compacts, with localization and normalization; the result compiles sorry-free with standard axioms. SimonGMT ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite (Simon 3.6/3.7(2)) is an alternative route, needing outer-measure and normalization conversions. HasApproximateTangentSpaceAt uses Bochner integrals over blow-up images, hence the finiteness hypothesis of the reused tangent lemma. In Mathlib, μHE[n] is a finite positive multiple of μH[n]. No idtp_dema_* name exists anywhere. Lean: all child statements elaborate; the stubs imply the frozen parent type; the full chain (new-child appendices, accepted reused proofs, assembly) has axioms propext, Classical.choice and Quot.sound only.
