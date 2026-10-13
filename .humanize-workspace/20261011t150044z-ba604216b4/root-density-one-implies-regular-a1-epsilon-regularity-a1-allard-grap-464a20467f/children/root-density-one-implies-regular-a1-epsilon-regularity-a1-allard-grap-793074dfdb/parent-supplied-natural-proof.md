# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.bad_set-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 4, the bound μ(B_{3σ₀/4}(ξ) ∖ G) ≤ C_bβ^{−2}L^{−2}∫_{B_{σ₀}(ξ)}|p_x − P|²dμ, whose proof is Simon Ch. 5, proof of 2.6, (2) and the estimate leading to (6). In the parent's application e(x) = |p_x − p_{T₀}|², a = β²L², and C_bβ^{−2}L^{−2} = 2ω_n(5/2)ⁿ/(β²L²). It uses the sibling vitali_bound (Submission.dorag_lip_vitali_two_measure_bound).
1. Reduction to the support. Let A' := (B_{3σ₀/4}(ξ) ∖ G') ∩ spt μ. Then B_{3σ₀/4}(ξ) ∖ G' ⊆ A' ∪ (E ∖ spt μ), and μ(E ∖ spt μ) = 0 (Measure.measure_compl_support; E = ℝ^{n+k} is second countable). Hence μ(B_{3σ₀/4}(ξ) ∖ G') ≤ μ(A').
2. Bad radii. Let y ∈ A'. Then y ∈ spt μ and y ∉ G', so some t ∈ (0, σ₀/2] has ofReal(a·tⁿ) < ∫_{B_{t/2}(y)} e⁺ dμ; this is Simon's (2). Choose such t_y (choose!) and put r(y) := t_y/2.
3. Applying vitali_bound. Use the measures μ and ν := μ.withDensity(e⁺), so that ν(B) = ∫_B e⁺ dμ for every closed ball B (withDensity_apply). Take the set A', the set B := B_{σ₀}(ξ), the radii r, the bound R₀ := σ₀/4 and c := ofReal(2(5/2)ⁿ/a)·ω_n. Check the hypotheses for y ∈ A':
   - 0 < r(y) ≤ σ₀/4.
   - B_{r(y)}(y) ⊆ B_{σ₀}(ξ), because dist(y, ξ) ≤ 3σ₀/4 and r(y) ≤ σ₀/4.
   - μ(A' ∩ B_{5r(y)}(y)) ≤ μ(B_{5t_y/2}(y)) ≤ 2ω_n·ofReal((5t_y/2)ⁿ), by the hypothesis, since y ∈ B_{3σ₀/4}(ξ) and 0 < 5t_y/2 ≤ 5σ₀/4.
   - 2ω_n·ofReal((5t_y/2)ⁿ) = ofReal(2(5/2)ⁿ/a)·ω_n·ofReal(a·t_yⁿ), because (2(5/2)ⁿ/a)·(a t_yⁿ) = 2(5t_y/2)ⁿ and ofReal of a product of nonnegatives is the product of the ofReals.
   - ofReal(2(5/2)ⁿ/a)·ω_n·ofReal(a·t_yⁿ) ≤ c·∫_{B_{t_y/2}(y)} e⁺ dμ = c·ν(B_{r(y)}(y)), by step 2.
4. Conclusion. vitali_bound gives μ(A') ≤ c·ν(B_{σ₀}(ξ)) = ofReal(2(5/2)ⁿ/a)·ω_n·∫_{B_{σ₀}(ξ)} e⁺ dμ. Together with step 1 this proves the claim. ∎
Formal check. The following compiles against the frozen type as Submission.dorag_lip_bad_set_measure_bound, using the sibling Submission.dorag_lip_vitali_two_measure_bound. Axioms: propext, Classical.choice, Quot.sound.
  intro n k μ e ξ σ₀ a hσ₀ ha hdens
  classical
  set Gs := {y | y ∈ μ.support ∧ ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 →
    ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ ≤ ENNReal.ofReal (a * t ^ n)} with hGs
  set A' := (closedBall ξ (3 * σ₀ / 4) \ Gs) ∩ μ.support with hA'
  have hsplit : μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ A' := by
    calc μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ (A' ∪ μ.supportᶜ) := by
          apply measure_mono
          intro x hx
          by_cases h : x ∈ μ.support
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr h
      _ ≤ μ A' + μ μ.supportᶜ := measure_union_le _ _
      _ = μ A' := by rw [Measure.measure_compl_support, add_zero]
  have hbad : ∀ y ∈ A', ∃ t : ℝ, 0 < t ∧ t ≤ σ₀ / 2 ∧
      ENNReal.ofReal (a * t ^ n) < ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ := by
    intro y hy
    have hyG : y ∉ Gs := hy.1.2
    simp only [hGs, Set.mem_ofPred_eq, not_and, not_forall, not_le] at hyG
    obtain ⟨t, ht, ht', hlt⟩ := hyG hy.2
    exact ⟨t, ht, ht', hlt⟩
  choose! T hT0 hTσ hTlt using hbad
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n with hc
  have key := Submission.dorag_lip_vitali_two_measure_bound (n + k) μ (μ.withDensity (fun x => ENNReal.ofReal (e x))) A' (closedBall ξ σ₀)
    (fun y => T y / 2) (σ₀ / 4) c (by
    intro y hy
    have hT0y := hT0 y hy
    have hTσy := hTσ y hy
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · intro x hx
      rw [mem_closedBall] at hx ⊢
      have := dist_triangle x y ξ
      have hyξ := mem_closedBall.1 hy.1.1
      linarith
    · calc μ (A' ∩ closedBall y (5 * (T y / 2))) ≤ μ (closedBall y (5 * (T y / 2))) :=
            measure_mono inter_subset_right
        _ ≤ 2 * unitBallVolume n * ENNReal.ofReal ((5 * (T y / 2)) ^ n) :=
            hdens y hy.1.1 _ (by linarith) (by linarith)
        _ = c * ENNReal.ofReal (a * T y ^ n) := by
            have hreal : 2 * (5 / 2) ^ n / a * (a * T y ^ n) = 2 * (5 * (T y / 2)) ^ n := by
              field_simp
              ring
            have h2 : ENNReal.ofReal (2 * (5 / 2) ^ n / a) * ENNReal.ofReal (a * T y ^ n) =
                2 * ENNReal.ofReal ((5 * (T y / 2)) ^ n) := by
              rw [← ENNReal.ofReal_mul (by positivity), hreal, ENNReal.ofReal_mul (by norm_num),
                ENNReal.ofReal_ofNat]
            rw [hc]
            calc 2 * unitBallVolume n * ENNReal.ofReal ((5 * (T y / 2)) ^ n)
                = unitBallVolume n * (2 * ENNReal.ofReal ((5 * (T y / 2)) ^ n)) := by ring
              _ = unitBallVolume n * (ENNReal.ofReal (2 * (5 / 2) ^ n / a) *
                    ENNReal.ofReal (a * T y ^ n)) := by rw [h2]
              _ = ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n *
                    ENNReal.ofReal (a * T y ^ n) := by ring
        _ ≤ c * ∫⁻ x in closedBall y (T y / 2), ENNReal.ofReal (e x) ∂μ := by
            gcongr
            exact (hTlt y hy).le
        _ = c * (μ.withDensity fun x => ENNReal.ofReal (e x)) (closedBall y (T y / 2)) := by
            rw [withDensity_apply _ measurableSet_closedBall])
  calc μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ A' := hsplit
    _ ≤ c * (μ.withDensity fun x => ENNReal.ofReal (e x)) (closedBall ξ σ₀) := key
    _ = _ := by rw [withDensity_apply _ measurableSet_closedBall]

## Key steps

1. reduce to A' = (B_{3σ₀/4}(ξ) ∖ G') ∩ spt μ since μ(spt μᶜ) = 0
2. choose a bad radius t_y ∈ (0, σ₀/2] with a t_yⁿ < ∫_{B_{t_y/2}(y)} e⁺ dμ
3. density bound gives μ(A' ∩ B_{5t_y/2}(y)) ≤ (2(5/2)ⁿ/a)ω_n·ν(B_{t_y/2}(y)) with ν = μ.withDensity e⁺
4. vitali_bound with B = B_{σ₀}(ξ) and R₀ = σ₀/4 yields the claim

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; the workspace lake-manifest.json pins the same mathlib rev and simongmt 2b3663083f3fe399b6296fb8eaee52169170e197)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'lipschitz.?approx|LipschitzApproximationLemma|LipschitzGraphCorollary|dorag_lip_' local-references/123e8435b4a2469b/project/GMT`
- `rg -c 'dorag_lip_' local-references/123e8435b4a2469b  (no match)`
- `rg -n "theorem exists_disjoint_subfamily_covering_enlargement_closedBall|theorem LipschitzOnWith.extend_real|lemma measure_compl_support|countable_of_nonempty_interior|lemma exp_le_two_add_div_two_sub|theorem withDensity_apply |theorem lintegral_add_left'|theorem lintegral_const_mul'|theorem setLIntegral_mono'|IsClosed.exists_infDist_eq_dist|lemma isClosed_support|theorem measure_toMeasurable|euclideanHausdorffMeasure_eq_volume|theorem addHaar_closedBall |norm_starProjection_apply_le|starProjection_orthogonal_val" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lean CheckNames.lean: #check of the 37 Mathlib/SimonGMT declarations cited by the children (all resolve, including Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `python3: frozen lean_statement of the four sibling prerequisites (dorag_approxTangent_starProjection_aesm, dorag_monotonicity_density, dorag_standing_density_bounds, dorag_affine_approximation) and of dorag_lipschitz_approximation from dag.json, compared with the assembly's hypotheses and conclusion (all equal)`
- `python3 -I lean_contract.validate_lean_statement on the 8 lean_statements; scan of all 8 workspace dag.json files and GMT/ for dorag_lip_* and the dorag_lip_cone_estimate_aux_/dorag_lip_off_support_aux_ prefixes (no collision)`
- `lean ChallengeAll.lean (8 child types and the frozen parent type elaborate); lean FromFinal.lean (8 child proofs + LipApxAssembly + LipApxFromChildren regenerated from the submitted JSON, exit 0); lean perchild/Child_<key>.lean (each child with only its declared dependency); gmt-compare.py contract_scope emulation cmp/Sol_<key>.lean and cmp/Chal_<key>.lean (all exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Exponential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/lipapx-v2-work/FromFinal.lean`
- `/tmp/lipapx-v2-work/ChallengeAll.lean`
- `/tmp/lipapx-v2-work/CheckNames.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. The workspace builds against the same Mathlib revision. The snapshot's Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which form the compiler context of every child.

Nothing in the snapshot proves the selected theorem or any child:
- GMT/Ch05 Contract/Submission (lines 272–309) define LipschitzApproximationLemma and LipschitzGraphCorollary only as Props for a different varifold type. They are used solely in the sorry-backed main_theorem (line 461).
- No dorag_lip_* name occurs in the snapshot.
So no comparator-approved declaration can be reused.

The tools the children cite exist at the pinned revision:
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (MeasureTheory/Covering/Vitali.lean:158);
- Set.PairwiseDisjoint.countable_of_nonempty_interior (Topology/Bases.lean:493);
- LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308);
- IsClosed.exists_infDist_eq_dist (Topology/MetricSpace/HausdorffDistance.lean:615);
- Measure.isClosed_support and Measure.measure_compl_support (MeasureTheory/Measure/Support.lean:115, 202);
- withDensity_apply (WithDensity.lean:44);
- measure_toMeasurable (MeasureSpaceDef.lean:348);
- lintegral_add_left' and lintegral_const_mul' (Integral/Lebesgue/Add.lean:326, 420);
- setLIntegral_mono' (Integral/Lebesgue/Basic.lean:254);
- Real.exp_le_two_add_div_two_sub (Analysis/Complex/Exponential.lean:676);
- Submodule.starProjection_orthogonal_val and norm_starProjection_apply_le (InnerProductSpace/Projection/Basic.lean:203, 411);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187);
- Measure.addHaar_closedBall (Lebesgue/EqHaar.lean:500);
- SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, which lies in the contract's import closure.

Lean checks:
- All 8 child types and the frozen parent type elaborate in comparator scope.
- All 8 children are fully proved, warning-free.
- The exact frozen parent type is derived from the 4 frozen sibling types plus the 8 children, using only propext, Classical.choice and Quot.sound.
- No name collides with any DAG reservation.
