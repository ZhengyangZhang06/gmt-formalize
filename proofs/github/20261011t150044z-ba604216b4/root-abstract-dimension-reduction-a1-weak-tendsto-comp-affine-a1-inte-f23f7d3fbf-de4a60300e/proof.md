# Parent-supplied natural-language proof

- Parent DAG node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1`
- Child DAG node: `root.abstract_dimension_reduction-a1.weak_tendsto_comp_affine-a1.integral_comp_affine-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof of `adr_weak_tendsto_comp_affine` (facts (b)–(c) of the A.4 decomposition, departure [D2]). It is the change of variables behind Simon's rescalings φ_{x,λ}(z) = φ(x + λz) (chapter-A.txt lines 125–133). For scaling and translation invariance of Hausdorff measure see e.g. Evans–Gariepy, Measure Theory and Fine Properties of Functions, §2.1; in Mathlib, `hausdorffMeasure_smul₀` and `map_homothety_hausdorffMeasure`. Throughout, μ := μH[d] with d := (n : ℝ) ≥ 0, and ∫ is the Bochner integral, which is 0 for non-integrable integrands.
1. The scaling map S(x) := c·x is a homeomorphism of ℝ^P because c ≠ 0; its inverse is x ↦ c⁻¹·x. Hence S is a measurable embedding for the Borel σ-algebra.
2. Push-forward of μ under S. For every Borel set B, S⁻¹(B) = c⁻¹·B. The scaling law μH[d](r·A) = |r|^d·μH[d](A) holds for r ≠ 0, d ≥ 0 and arbitrary A. So (S_#μ)(B) = μ(c⁻¹·B) = c^{−n}·μ(B). Measures that agree on all measurable sets are equal, so S_#μ = a·μ with the finite constant a := c^{−n} ∈ (0, ∞). In Mathlib, `map_homothety_hausdorffMeasure` applied to the homothety with centre 0 and ratio c (the map x ↦ c • x) gives `Measure.map (fun x => c • x) μH[d] = ‖c‖₊⁻¹ ^ d • μH[d]`.
3. Change of variables along a measurable embedding holds for every integrand: for every φ : ℝ^P → ℝ^Q, ∫ φ d(S_#μ) = ∫ φ(S x) dμ(x). Here φ is S_#μ-integrable iff φ∘S is μ-integrable, and otherwise both integrals are 0 (Mathlib `MeasurableEmbedding.integral_map`).
4. Multiplying the measure by a finite constant a ≥ 0 multiplies every Bochner integral by a: ∫ φ d(a·μ) = a·∫ φ dμ for every φ (Mathlib `integral_smul_nnreal_measure`).
5. Translation invariance. For fixed y, the map w ↦ y + w is an isometry of ℝ^P onto itself. It therefore preserves μH[d], which is defined from diameters only. Hence ∫ φ(y + w) dμ(w) = ∫ φ dμ for every φ (Mathlib: μH[d] is `IsAddLeftInvariant`; `integral_add_left_eq_self`).
6. Conclusion. Put φ(w) := h(y + w), so that h(y + c·x) = φ(S x). By steps 3, 2, 4 and 5,
∫ h(y + c·x) dμ(x) = ∫ φ d(S_#μ) = ∫ φ d(a·μ) = a·∫ h(y + w) dμ(w) = a·∫ h dμ.
Since c > 0, ‖c‖ = c and the real power c^{(n:ℝ)} equals the natural power c^n, so a = c^{−n} = (c^n)⁻¹. This is the identity ∫ h(y + c • x) dμH[n] = (c^n)⁻¹ • ∫ h dμH[n]. ∎
Formalization notes (verified in a scratch build of exactly this statement; standard axioms only; no additional imports):
- `(Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding`.
- `map_homothety_hausdorffMeasure (Nat.cast_nonneg n) (0 : Euclid P) hc.ne'`, adapted by `convert this using 2; funext x; simp [AffineMap.homothety_apply]`.
- Then `hemb.integral_map`, `integral_smul_nnreal_measure` and `integral_add_left_eq_self`.
- The scalar by `simp [Real.norm_of_nonneg hc.le, inv_pow]`.

## Key steps

1. x ↦ c·x is a homeomorphism (c ≠ 0), hence a measurable embedding
2. scaling law of Hausdorff measure: the push-forward of μH[n] under x ↦ c·x is c^{−n}·μH[n]
3. change of variables along a measurable embedding, valid for every integrand
4. a finite scalar multiple of the measure multiplies every Bochner integral by that scalar
5. translation invariance of μH[n] removes y; ‖c‖₊⁻¹^n = (c^n)⁻¹ since c > 0

## Reference use

### local-project

Queries:
- `cmp GMT/Ch07/Submission.lean local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean; cmp of the 11 cited snapshot Mathlib files against lake-packages-25730c7c/mathlib (all byte-identical)`
- `grep -n 'hausdorffMeasure_smul|map_homothety|IsAddLeftInvariant|hausdorffMeasure_image|map_hausdorffMeasure|hausdorffMeasure_preimage|isometry' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n 'theorem|lemma' mathlib/Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`
- `grep -rn 'integrable_smul_left_of_hasCompactSupport|integrableOn_isCompact' mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `grep -rn 'uniformContinuous_of_continuous' mathlib/Mathlib --include=*.lean`
- `grep -rn 'MeasurableEmbedding.integral_map|integral_smul_measure|integral_add_left_eq_self|completeSpace_coe|isBounded_range_of_tendsto|tendstoUniformly_iff|mkContinuous_norm_le|def mkOfBound|norm_le' mathlib/Mathlib --include=*.lean`
- `grep -rn 'def LinearMap.mkContinuous' mathlib/Mathlib --include=*.lean (variable context in Analysis/Normed/Operator/ContinuousLinearMap.lean)`
- `grep -n 'continuous_eval_const|theorem continuous_coe' mathlib/Mathlib/Topology/ContinuousMap/Bounded/*.lean`
- `grep -rln 'banach_steinhaus|hausdorffMeasure_smul₀|map_homothety_hausdorffMeasure|TendstoUniformly' lake-packages-25730c7c/simongmt --include=*.lean`
- `grep -c <each proposed lean_name> runs/20261011T150044Z-ba604216b4/dag.json; grep -rl <name> gmt-ch07/GMT .swarm-worktrees/*/gmt-ch07/GMT`
- `grep -n 'byte|Submission|candidate_inputs' verifier/gmt-compare.py; grep '^import' .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean`
- `sed -n 110,140p book/chapter-A.txt`
- `lake env lean /tmp/wtca-decomp/Final.lean (four exact child types + parent proved from their stubs + #print axioms)`
- `lake env lean /tmp/wtca-decomp/AllFinal.lean (complete proofs of the four children and of the parent; #print axioms each)`
- `lake env lean /tmp/wtca-decomp/Exp4.lean, Exp7.lean (trace.Meta.synthInstance), Exp8.lean, Exp9.lean (Submodule ℝ (Euclid P →ᵇ ℝ) instance probes; BaireSpace availability without extra imports)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/Bounded/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1-weak-tendsto-comp-affine-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-A.txt`
- `/tmp/wtca-decomp/Final.lean`
- `/tmp/wtca-decomp/AllFinal.lean`
- `/tmp/wtca-decomp/ChildA.lean`
- `/tmp/wtca-decomp/ChildBC.lean`
- `/tmp/wtca-decomp/ChildD.lean`
- `/tmp/wtca-decomp/Exp7.lean`
- `/tmp/wtca-decomp/Exp9.lean`

The snapshot Contract.lean is byte-identical to the workspace Submission.lean, and the 11 cited snapshot Mathlib files are byte-identical to the build packages.

Mathlib supplies every tool the children need:
- integral_comp_affine: map_homothety_hausdorffMeasure, hausdorffMeasure_smul₀ and the IsAddLeftInvariant instance for μH[d] (Hausdorff.lean); MeasurableEmbedding.integral_map, integral_smul_nnreal_measure, integral_add_left_eq_self.
- weak_uniform_bound: banach_steinhaus (BanachSteinhaus.lean); IsClosed.completeSpace_coe, BoundedContinuousFunction.continuous_coe/mkOfBound/norm_le/norm_coe_le_norm, LinearMap.mkContinuous, ContinuousLinearMap.le_of_opNorm_le; LocallyIntegrable.integrable_smul_left_of_hasCompactSupport and integrableOn_isCompact.
- weak_tendsto_moving_tests: Metric.isBounded_range_of_tendsto, Metric.tendstoUniformly_iff.
- rescaled_translate_converge: HasCompactSupport.uniformContinuous_of_continuous (HeineCantor.lean).

BanachSteinhaus.lean is not imported by the contract header. Its olean exists in the package tree, and adding the import to Submission.lean compiles and is allowed by gmt-compare.py, which byte-checks only frozen inputs other than Submission.lean. Baire's nonempty_interior_of_iUnion_of_closed and BaireSpace for complete metric spaces are available without it.

Instance pitfall: for X : Submodule ℝ (Euclid P →ᵇ ℝ), typeclass search does not find SeminormedAddCommGroup ↥X inside Norm (↥X →L[ℝ] Euclid Q). letI Submodule.seminormedAddCommGroup X and Submodule.normedSpace X fix this, together with explicit (E := X) arguments to mkContinuous and banach_steinhaus.

simongmt has no Banach–Steinhaus or Hausdorff change-of-variables lemma; its only TendstoUniformly hits are test-form topology for currents in Chapter06, so it has no relevant match.

The four exact child types elaborate in the contract scope, and the parent compiles from their stubs. Complete scratch proofs of all four children and of the parent use only propext, Classical.choice and Quot.sound. The proposed names collide with nothing in dag.json or any worktree.
