# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.coordinates-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 2 (Coordinates). Choose orthonormal bases a₁,…,aₙ of T₀ and b₁,…,b_k of T₀^⊥ and put ι(v) := Σ vᵢaᵢ, ι'(w) := Σ w_j b_j. Then ι, ι' are linear isometries, ι(v) ∈ T₀, ⟨ιv, ι'w⟩ = 0, Px = ι(ι*x) and Qx = ι'(ι'*x). Notation: E := ℝ^{n+k} = Euclid (n + k), P := T₀.starProjection.
1. dim T₀^⊥ = k. By Submodule.finrank_add_finrank_orthogonal and finrank_euclideanSpace_fin, dim T₀ + dim T₀^⊥ = dim E = n + k. Since dim T₀ = n, dim T₀^⊥ = k.
2. Construction. Let b be an orthonormal basis of T₀ indexed by Fin n (stdOrthonormalBasis ℝ T₀ reindexed along finCongr, using dim T₀ = n). Let b' be an orthonormal basis of T₀^⊥ indexed by Fin k (using step 1). Their coordinate maps b.repr : T₀ → ℝⁿ and b'.repr : T₀^⊥ → ℝᵏ are linear isometric equivalences. Define ι := (inclusion T₀ ⊆ E) ∘ b.repr⁻¹ and ι' := (inclusion T₀^⊥ ⊆ E) ∘ b'.repr⁻¹; that is, ι(v) = Σᵢ vᵢaᵢ and ι'(w) = Σⱼ wⱼbⱼ. Compositions of linear isometries are linear isometries. For all v, w we have ιv ∈ T₀ (this is conclusion (b)) and ι'w ∈ T₀^⊥.
3. Orthogonality (a). For all v, w, ⟨ιv, ι'w⟩ = 0, because ιv ∈ T₀ and ι'w ∈ T₀^⊥ (Submodule.inner_right_of_mem_orthogonal).
4. Spanning (c). Let x ∈ E. Then Px ∈ T₀ (Submodule.starProjection_apply_mem) and x − Px ∈ T₀^⊥ (Submodule.sub_starProjection_mem_orthogonal). Put v := b.repr(Px) and w := b'.repr(x − Px). Then ιv = Px and ι'w = x − Px, so x = ιv + ι'w.
5. Projection identity (d). P is linear. P(ιv) = ιv because ιv ∈ T₀ (Submodule.starProjection_eq_self_iff). P(ι'w) = 0 because ι'w ∈ T₀^⊥ (Submodule.starProjection_apply_eq_zero_iff T₀; T₀ is an explicit argument). Hence P(ιv + ι'w) = ιv + 0 = ιv. ∎
Formal check. The following tactic proof of the exact frozen type compiles after import GMT.Ch07.Submission in the comparator scope, declared as Submission.dorag_lip_orthonormal_coordinates. #print axioms gives propext, Classical.choice, Quot.sound.
  intro n k T₀ hT₀
  have hTo : Module.finrank ℝ T₀ᗮ = k := by
    have h := Submodule.finrank_add_finrank_orthogonal T₀
    rw [finrank_euclideanSpace_fin, hT₀] at h
    omega
  let b := (stdOrthonormalBasis ℝ T₀).reindex (finCongr hT₀)
  let b' := (stdOrthonormalBasis ℝ T₀ᗮ).reindex (finCongr hTo)
  let ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k) := T₀.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k) := T₀ᗮ.subtypeₗᵢ.comp b'.repr.symm.toLinearIsometry
  have hιmem : ∀ v, ι v ∈ T₀ := fun v => (b.repr.symm v).2
  have hι'mem : ∀ w, ι' w ∈ T₀ᗮ := fun w => (b'.repr.symm w).2
  refine ⟨ι, ι', fun v w => Submodule.inner_right_of_mem_orthogonal (hιmem v) (hι'mem w), hιmem,
    ?_, ?_⟩
  · intro x
    refine ⟨b.repr ⟨T₀.starProjection x, Submodule.starProjection_apply_mem _ _⟩,
      b'.repr ⟨x - T₀.starProjection x, Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
    simp [ι, ι']
  · intro v w
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr (hιmem v),
      (Submodule.starProjection_apply_eq_zero_iff T₀).mpr (hι'mem w), add_zero]

## Key steps

1. dim T₀^⊥ = k from dim T₀ + dim T₀^⊥ = n + k
2. ι, ι' := inclusions of T₀, T₀^⊥ composed with inverse coordinate maps of orthonormal bases indexed by Fin n, Fin k
3. orthogonality from ιv ∈ T₀ and ι'w ∈ T₀^⊥
4. spanning: x = Px + (x − Px) with Px ∈ T₀ = range ι and x − Px ∈ T₀^⊥ = range ι'
5. projection identity P(ιv + ι'w) = ιv + 0 by linearity

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
