# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.directional_gauss_green-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 5(a)/(b) ('g := ζw has div g = Dζ(w)'), i.e. printed (8) of Simon Ch. 3, 4.3 applied to the field φ e_i.
1. The vector field. Define g : E → E by g(x) := ζ(x)·w. As ζ is C¹ and w is constant, g is C¹. support g ⊆ support ζ, hence tsupport g ⊆ tsupport ζ ⊆ B_R(0); tsupport g is a closed subset of the compact set tsupport ζ, so g has compact support.
2. Its divergence. For all x, h ∈ E, Dg(x)(h) = (Dζ(x)(h))·w, i.e. Dg(x) is the rank-one map h ↦ ℓ(h)·w with ℓ := Dζ(x). The trace of h ↦ ℓ(h)·w equals ℓ(w) (for a basis e_i with dual basis e^i: Σ_i e^i(ℓ(e_i)w) = ℓ(Σ_i e^i(w) e_i) = ℓ(w)). Hence div g(x) = Dζ(x)(w) for every x.
3. Its pairing with ν. For every z, ⟨g(r^{-1}(z − y)), ν(z)⟩ = ⟨ζ(r^{-1}(z − y))·w, ν(z)⟩ = ζ(r^{-1}(z − y))·⟨w, ν(z)⟩.
4. Conclusion. By step 1, g satisfies all hypotheses of the sibling theorem rescaled_gauss_green (same m, D, F, μ, ν, y, r, R; F Borel, (GG), r > 0, B̄_{rR}(y) ⊆ D, g C¹ with compact support and tsupport g ⊆ B_R(0)). It gives ∫_{F_{y,r}} div g dL = −(r^m)^{-1} ∫⟨g(r^{-1}(z − y)), ν(z)⟩ dμ(z). The integrands are pointwise equal to Dζ(·)(w) (step 2) and to ζ(r^{-1}(z − y))⟨w, ν(z)⟩ (step 3), so the integrals agree and the claim follows. ∎
Formalization pointers (verified): hζ.smul contDiff_const; hζc.smul_right (f' := fun _ => w); tsupport_smul_subset_left ζ (fun _ => w); fderiv_smul_const ((hζ.differentiable one_ne_zero) z) w; identify ↑((fderiv ℝ ζ z).smulRight w) with (↑(fderiv ℝ ζ z) : E →ₗ[ℝ] ℝ).smulRight w by ext/simp, then LinearMap.trace_smulRight; real_inner_smul_left; simp_rw both pointwise identities into the sibling equation.

Appendix (an optional aid; the numbered argument above is the proof). The Lean 4 script below proves exactly the frozen statement. It compiled against the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c, project b4d606db) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open Filter Function Set MeasureTheory Metric` and `open scoped ENNReal Topology`. Compiled together with the other eight child proofs, `#print axioms` reported only propext, Classical.choice and Quot.sound. The exact compiled source of all nine children, plus the parent assembly, is saved at .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/bh-split-v2-lean-prototype.lean.txt. It uses the sibling declaration Submission.codim1_rdo_dg_bh_rescaled_gauss_green at its frozen type.
```lean
theorem Submission.codim1_rdo_dg_bh_directional_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r R : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → closedBall y (r * R) ⊆ D → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid (m + 1)) R → ∀ w : Euclid (m + 1), ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z w = -(r ^ m)⁻¹ * ∫ z, ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ := by
  intro m D F μ ν y r R hF hGG hr hball ζ hζ hζc hζs w
  have hg : ContDiff ℝ 1 (fun z => ζ z • w) := hζ.smul contDiff_const
  have hgc : HasCompactSupport (fun z => ζ z • w) := hζc.smul_right (f' := fun _ => w)
  have hgs : tsupport (fun z => ζ z • w) ⊆ ball (0 : Euclid (m + 1)) R :=
    (tsupport_smul_subset_left ζ (fun _ => w)).trans hζs
  have key := Submission.codim1_rdo_dg_bh_rescaled_gauss_green m D F μ ν y r R hF hGG hr hball
    (fun z => ζ z • w) hg hgc hgs
  have h1 : ∀ z, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ (fun z => ζ z • w) z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = fderiv ℝ ζ z w := by
    intro z
    rw [fderiv_smul_const ((hζ.differentiable one_ne_zero) z) w]
    have : ((fderiv ℝ ζ z).smulRight w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) =
        (fderiv ℝ ζ z : Euclid (m + 1) →ₗ[ℝ] ℝ).smulRight w := by
      ext x; simp
    rw [this, LinearMap.trace_smulRight]
    rfl
  have h2 : ∀ z, inner ℝ (ζ (r⁻¹ • (z - y)) • w) (ν z) = ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) :=
    fun z => real_inner_smul_left _ _ _
  simp_rw [h1, h2] at key
  exact key
```

## Key steps

1. g := ζ·w is C¹ with compact support and tsupport g ⊆ tsupport ζ ⊆ B_R(0).
2. div(ζ·w) = Dζ(·)(w) (trace of the rank-one map h ↦ Dζ(h)w).
3. ⟨ζ(..)w, ν⟩ = ζ(..)⟨w, ν⟩.
4. Apply rescaled_gauss_green to g and rewrite both integrands.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD`
- `sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 over dag.json: selected node record (status, message, attempts, children); frozen lean_statement of cutoff_estimates-a1, volume_density_lower-a1, bv_compactness-a1 and halfspace_rigidity-a1; name-collision and identical-type scan of the nine codim1_rdo_dg_bh_* children (1010 nodes, re-run at 1119 nodes)`
- `grep -l '"child_id": "...blowup_halfspace-a1.' nodes/*/parent-child-handoff.json; grep -rl codim1_rdo_dg_bh_ nodes/ .humanize/publication-intents .humanize/issue-claims (no match outside decomposition-v1.json)`
- `sed -n runtime.py: _solve loop (960-1060), _decompose (1388-1560), _parent_supplied_child_checkpoint (1741-1799), _solve_children (1801-1990), _existing_lean_name_problem (6532-6575); cat swarm-project.json; cat run.json`
- `rg -n 'blowUp|blowup|symmDiff|GaussGreen|gaussGreen|reducedBoundary|rescal|L1loc|halfspace' <snapshot>/project/GMT/Ch07; rg -n 'DeGiorgi|reducedBoundary|symmDiff|blow' <snapshot>/project/GMT/Ch03/Contract.lean; rg -ln 'blowUp|blowUpMap|reducedBoundary|GaussGreen|gaussGreen|symmDiff' simongmt/Poincare; rg -n '^theorem|^lemma|^def|^structure' simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `rg -n in <snapshot>/mathlib: tendsto_of_subseq_tendsto | integral_comp_smul | addHaar_preimage_smul | trace_smulRight | fderiv_smul_const | symmDiff_triangle | norm_setIntegral_le_of_norm_le_const | setIntegral_eq_integral_of_forall_compl_eq_zero | norm_integral_le_of_norm_le | integral_mul_left_eq_self | mulTSupport_comp_subset_preimage | HasCompactMulSupport.comp_homeomorph | HasCompactSupport.fderiv_apply | ContDiff.continuous_fderiv | ENNReal.tendsto_nhds | Integrable.of_bound | integral_inner | integral_indicator_const | isFiniteMeasure_restrict | measure_preimage_mul | toReal_le_of_le_ofReal | integrableOn_const`
- `sed -n 560,760p book/chapter-03.txt (Simon Ch. 3, 4.3 printed proof)`
- `git show <last 200 commits>:GMT/Ch07/Submission.lean | grep ^import (import practice of candidate submissions); sed -n 1,28p verifier/gmt-compare.py`
- `lake env lean -DautoImplicit=false /tmp/bh-split-v2/{Types,Assembly,Checks,Rescaled,NormalDefect,L1loc,FirstVariation,Full,SavedCopy}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/SymmDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/run.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-632b252050/bh-split-v2-lean-prototype.lean.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/bh-split-v2/Types.lean`
- `/tmp/bh-split-v2/Assembly.lean`
- `/tmp/bh-split-v2/Checks.lean`
- `/tmp/bh-split-v2/Rescaled.lean`
- `/tmp/bh-split-v2/NormalDefect.lean`
- `/tmp/bh-split-v2/L1loc.lean`
- `/tmp/bh-split-v2/FirstVariation.lean`
- `/tmp/bh-split-v2/Full.lean`

Pins: the snapshot manifest (project b4d606db, Mathlib 25730c7c) equals workspace HEAD and .lake/packages/mathlib. Snapshot Contract.lean, workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).

Reuse: nothing in the snapshot is reusable. The project's only blow-up is the current-level GMT.Ch07.blowUp (Contract.lean:184). The snapshot's GMT/Ch03 has a DeGiorgiTheorem Prop (Contract.lean:325), but its main_theorem is `by sorry` (:339). SimonGMT Chapter03/FinitePerimeter.lean supplies only the reducedBoundary data. No local declaration states the rescaled Gauss–Green identity, the normal-defect estimate, the blow-up perimeter bound, the L¹_loc transfer or the offset lemma, so all become children.

API: snapshot Mathlib supplies everything the child proofs use: CountablyGenerated.lean:125, Haar/NormedSpace.lean:92, Lebesgue/EqHaar.lean:352, LinearAlgebra/Trace.lean:272, FDeriv/Mul.lean:153, FDeriv/Const.lean:393, ContDiff/Defs.lean:1271, Order/SymmDiff.lean:210, Bochner/Set.lean:486/528/613, Bochner/Basic.lean:985, Group/Integral.lean:91, Group/Measure.lean:236, Topology/Algebra/Support.lean:99/562, ENNReal/Lemmas.lean:233, IntegrableOn.lean:119/171, Typeclasses/Finite.lean:40, Basic/ENNReal/Real.lean:283. One exception: integral_inner (Function/L2Space.lean:89) is outside the frozen header's import closure, so normal_defect's pointer uses innerSL ℝ v with integral_comp_comm. Recent candidate commits do add Mathlib imports, so importing it is also an option.

Lean checks (from the workspace root):
- All 13 types elaborate.
- The parent's frozen type is proved from the 9 children and the 4 sibling contracts.
- All 9 children are proved with only propext, Classical.choice, Quot.sound.
- The saved prototype recompiles identically.

DAG and runtime: v1 (identical contract) was accepted at 11:14Z, but its children were never activated before the 11:42Z restart. The node has no children, and there are no leftover handoffs or publication intents. The nine names are unused across the 1119 nodes, and no identical type exists. Config: max_depth 6, max_children 12.
