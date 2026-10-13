# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.graph_geometry-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Steps 8 and 9.
- Step 8: for x ∈ F ∩ B_{3s}(η), x = Φ_f(v) and η = Φ_f(v_η), and |Q(x − η)| = |f(v) − f(v_η)| ≤ (Lip f)|v − v_η|.
- Step 9: since |v − v'| ≤ |Φ_f(v) − Φ_f(v')| and Φ_f is √2-Lipschitz (Lip f ≤ 1), F ∩ B_{15s_j}(η_j) ⊆ Φ_f(Bⁿ_{15s_j}(v_{η_j})) and Hⁿ(F ∩ B_{15s_j}(η_j)) ≤ 2^{n/2}ω_n(15s_j)ⁿ.
- Book: Simon Ch. 5, proof of 2.6, 'Hⁿ(B_{5σ_j}(ξ_j) ∩ F) ≤ Cσ_jⁿ'.
Notation: Φ(v) := ξ + ιv + ι'f(v), F := range Φ, P := T₀.starProjection, Qu := u − Pu.
1. Difference formula. For v, v' ∈ ℝⁿ, linearity gives Φ(v) − Φ(v') = ι(v − v') + ι'(f(v) − f(v')).
2. Pythagoras. For a ∈ ℝⁿ and b ∈ ℝᵏ, ‖ιa + ι'b‖² = ‖ιa‖² + 2⟨ιa, ι'b⟩ + ‖ι'b‖² = ‖a‖² + ‖b‖², by norm_add_sq_real, orthogonality and the isometry property. In particular ‖a‖ ≤ ‖ιa + ι'b‖.
3. Cone condition (conclusion (i)). Let x = Φ(v) and x' = Φ(v'). By step 1 and the projection hypothesis, P(x − x') = ι(v − v'). Hence Q(x − x') = ι'(f(v) − f(v')) and, since Λ ≥ 0 and by step 2, ‖Q(x − x')‖ = ‖f(v) − f(v')‖ ≤ Λ‖v − v'‖ ≤ Λ‖x − x'‖.
4. Lipschitz bound for Φ. By steps 1, 2 and the hypothesis with 0 ≤ Λ ≤ 1, ‖Φ(v) − Φ(v')‖² = ‖v − v'‖² + ‖f(v) − f(v')‖² ≤ (1 + Λ²)‖v − v'‖² ≤ 2‖v − v'‖². So Φ is √2-Lipschitz, with constant NNReal.sqrt 2.
5. Localisation. Let x = Φ(v₀) and r > 0. If x' = Φ(v) ∈ F ∩ B_r(x), then ‖v − v₀‖ ≤ ‖Φ(v) − Φ(v₀)‖ ≤ r by steps 1–2. Hence F ∩ B_r(x) ⊆ Φ(Bⁿ_r(v₀)).
6. Image measure. By the Lipschitz image inequality for the normalised Hausdorff measure, μHE[n](Φ(Bⁿ_r(v₀))) ≤ (√2)ⁿ·μHE[n](Bⁿ_r(v₀)). Source: Simon Ch. 2, 1.8(i); in Lean, Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, which is in the contract's import closure via Chapter03.Rectifiable.
7. Ball volume. On ℝⁿ, μHE[n] is Lebesgue measure (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). The closed ball has volume rⁿ·vol(open unit ball) = ω_n rⁿ (Measure.addHaar_closedBall with finrank ℝⁿ = n; ω_n = unitBallVolume n is the volume of the open unit ball). Also (√2)ⁿ = 2^{n/2} (Real.sqrt_eq_rpow, Real.rpow_natCast, Real.rpow_mul), so ((√2 : ℝ≥0) : ℝ≥0∞)ⁿ = ofReal(2^{n/2}).
8. Combining steps 5–7: μHE[n](F ∩ B_r(x)) ≤ ofReal(2^{n/2})·ω_n·ofReal(rⁿ), which is conclusion (ii). ∎
Formal check. The following compiles against the frozen type in the comparator scope. Axioms: propext, Classical.choice, Quot.sound.
  intro n k T₀ ι ι' ξ f Λ horth hproj hΛ0 hΛ1 hf
  have hdiff : ∀ v v' : Euclid n, (ξ + ι v + ι' (f v)) - (ξ + ι v' + ι' (f v')) =
      ι (v - v') + ι' (f v - f v') := by
    intro v v'; rw [map_sub, map_sub]; abel
  have hpyth : ∀ (a : Euclid n) (b : Euclid k), ‖ι a + ι' b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    intro a b
    rw [norm_add_sq_real, horth a b, LinearIsometry.norm_map, LinearIsometry.norm_map]
    ring
  have hlow : ∀ (a : Euclid n) (b : Euclid k), ‖a‖ ≤ ‖ι a + ι' b‖ := by
    intro a b
    have h := hpyth a b
    have h2 : ‖a‖ ^ 2 ≤ ‖ι a + ι' b‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖b‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hQ : ∀ (a : Euclid n) (b : Euclid k),
      (ι a + ι' b) - T₀.starProjection (ι a + ι' b) = ι' b := by
    intro a b; rw [hproj]; abel
  constructor
  · rintro x ⟨v, rfl⟩ x' ⟨v', rfl⟩
    simp only []
    rw [hdiff, hQ, LinearIsometry.norm_map]
    exact (hf v v').trans (mul_le_mul_of_nonneg_left (hlow _ _) hΛ0)
  · rintro x ⟨v₀, rfl⟩ r hr
    set Φ : Euclid n → Euclid (n + k) := fun v => ξ + ι v + ι' (f v) with hΦ
    have hdiffΦ : ∀ v v', Φ v - Φ v' = ι (v - v') + ι' (f v - f v') := fun v v' => hdiff v v'
    have hsub : range Φ ∩ closedBall (Φ v₀) r ⊆ Φ '' closedBall v₀ r := by
      rintro x ⟨⟨v, rfl⟩, hx⟩
      refine ⟨v, ?_, rfl⟩
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      calc ‖v - v₀‖ ≤ ‖ι (v - v₀) + ι' (f v - f v₀)‖ := hlow _ _
        _ = ‖Φ v - Φ v₀‖ := by rw [hdiffΦ]
        _ ≤ r := hx
    have hLip : LipschitzOnWith (NNReal.sqrt 2) Φ (closedBall v₀ r) := by
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro v v'
      rw [dist_eq_norm, dist_eq_norm, Real.coe_sqrt, NNReal.coe_ofNat]
      have h := hpyth (v - v') (f v - f v')
      have hfv := hf v v'
      have hsq : ‖Φ v - Φ v'‖ ^ 2 ≤ (Real.sqrt 2 * ‖v - v'‖) ^ 2 := by
        rw [hdiffΦ, h, mul_pow, Real.sq_sqrt (by norm_num)]
        have h1 : ‖f v - f v'‖ ^ 2 ≤ (Λ * ‖v - v'‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hfv 2
        have h2 : (Λ * ‖v - v'‖) ^ 2 ≤ ‖v - v'‖ ^ 2 := by
          rw [mul_pow]
          have : Λ ^ 2 ≤ 1 := by nlinarith
          nlinarith [sq_nonneg ‖v - v'‖]
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    have hpow : ((NNReal.sqrt 2 : NNReal) : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) := by
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, NNReal.coe_ofNat,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      ring_nf
    calc μHE[n] (range Φ ∩ closedBall (Φ v₀) r) ≤ μHE[n] (Φ '' closedBall v₀ r) := measure_mono hsub
      _ ≤ ((NNReal.sqrt 2 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (closedBall v₀ r) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
      _ = ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n * ENNReal.ofReal (r ^ n) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
            Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, hpow]
          unfold unitBallVolume
          ring

## Key steps

1. Φ(v) − Φ(v') = ι(v − v') + ι'(f v − f v')
2. Pythagoras ‖ιa + ι'b‖² = ‖a‖² + ‖b‖², so ‖a‖ ≤ ‖ιa + ι'b‖
3. Q(x − x') = ι'(f v − f v') gives the cone condition with constant Λ
4. Φ is √2-Lipschitz since Λ ≤ 1
5. F ∩ B_r(Φ(v₀)) ⊆ Φ(Bⁿ_r(v₀))
6. Lipschitz image bound for μHE[n], μHE[n] = Lebesgue on ℝⁿ, ball volume ω_n rⁿ, (√2)ⁿ = 2^{n/2}

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
