# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.carried_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 2 of the selected proof ("supports in G^⊥", parts (b), (d), (e)), with the closed set G^⊥ replaced by an arbitrary closed set F, S₀ by S₂ and S₀′ by S₁. Two simplifications of the selected proof: part (b) is obtained from the accepted measure criterion for the support instead of a direct test-form computation, and part (d) uses the zero-region intersection argument directly, so the integer multiplicity of S₁ − S₂ (parts (a), (c)) is not needed. The selected proof is the project's argument for Simon, Lemma 7.3.5 (book/chapter-07.txt, lines 407–417), whose proof Simon leaves to the reader.
Inherited accepted results cited by exact Lean name (dependencies of ancestors of this node):
 (MC) Submission.dimred_im_mass_measure, part (b): if U ⊆ ℝ^P is open, T ∈ 𝒟_j(U) and R represents T, then for every x ∈ U: x ∈ spt T ⟺ R.measure(B_ε(x)) ≠ 0 for every ε > 0.
 (F6) Submission.imrep_carrier_sdiff_support_null: if U is open and R = (M, θ, ξ) represents T ∈ 𝒟_j(U), then H^j(M ∖ spt T) = 0.
Notation. μ_i := R_i.measure = (H^j⌞M_i).withDensity θ_i, M_i := R_i.carrier (a Borel set), θ_i := R_i.mult, H^j := μHE[j]. For T ∈ 𝒟_j(ℝ^P), Z_T := T.zeroRegion is the union of all open W ⊆ ℝ^P with closure W compact and closure W ⊆ ℝ^P such that T vanishes on W (T(ω) = 0 for every test form ω with tsupport ω ⊆ W); spt T = ℝ^P ∖ Z_T.

1. (spt S₂ ⊆ F.) Let x ∈ spt S₂ and suppose x ∉ F. As F is closed, ℝ^P ∖ F is open, so there is ε > 0 with B_ε(x) ⊆ ℝ^P ∖ F. Then μ₂(B_ε(x)) ≤ μ₂(ℝ^P ∖ F) = 0. On the other hand (MC) with U := ℝ^P (open), T := S₂, R := R₂ and x ∈ ℝ^P gives μ₂(B_ε(x)) ≠ 0, because x ∈ spt S₂. This contradiction shows x ∈ F.
2. (spt S₁ ⊆ F.) Let x ∈ spt S₁ and suppose x ∉ F. By step 1, x ∉ spt S₂, and by hypothesis x ∉ spt(S₁ − S₂); since x ∈ ℝ^P, this means x ∈ Z_{S₂} and x ∈ Z_{S₁−S₂}. Choose open sets W₁ ∋ x and W₂ ∋ x, each with compact closure contained in ℝ^P, such that S₂ vanishes on W₁ and S₁ − S₂ vanishes on W₂. Put W := W₁ ∩ W₂. Then W is open, x ∈ W, closure W ⊆ closure W₁, so closure W is a closed subset of a compact set, hence compact, and closure W ⊆ ℝ^P. For every test form ω with tsupport ω ⊆ W we have S₂(ω) = 0 (tsupport ω ⊆ W₁) and S₁(ω) − S₂(ω) = (S₁ − S₂)(ω) = 0 (tsupport ω ⊆ W₂), hence S₁(ω) = 0. Thus S₁ vanishes on W, so x ∈ Z_{S₁}, contradicting x ∈ spt S₁ = ℝ^P ∖ Z_{S₁}. Hence spt S₁ ⊆ F.
3. (μ₁ vanishes off spt S₁.) μ₁ = (H^j⌞M₁).withDensity θ₁ is absolutely continuous with respect to H^j⌞M₁ (withDensity_absolutelyContinuous). Since M₁ is Borel (R₁.measurableSet_carrier), (H^j⌞M₁)(ℝ^P ∖ spt S₁) = H^j((ℝ^P ∖ spt S₁) ∩ M₁) = H^j(M₁ ∖ spt S₁) (Measure.restrict_apply'), which is 0 by (F6) with U := ℝ^P, T := S₁, R := R₁. Therefore μ₁(ℝ^P ∖ spt S₁) = 0.
4. (Conclusion.) By step 2, ℝ^P ∖ F ⊆ ℝ^P ∖ spt S₁, hence μ₁(ℝ^P ∖ F) ≤ μ₁(ℝ^P ∖ spt S₁) = 0 by step 3 (measure_mono_null). ∎

Formalization sketch (context, not part of the numbered proof). The following Lean proof of exactly the frozen type compiled during decomposition (Lean v4.35.0-rc3, Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract opens), with every cited Submission.* dependency present as a stub of its exact frozen type:
theorem Submission.dimred_cs_sos_mt_cm_carried_transfer : ∀ (P j : ℕ) (S₁ S₂ : GeometricCurrentOn (univ : Set (Euclid P)) j) (R₁ R₂ : IMRep (univ : Set (Euclid P)) j) (F : Set (Euclid P)), R₁.Represents S₁ → R₂.Represents S₂ → IsClosed F → R₂.measure Fᶜ = 0 → (S₁ - S₂).support ⊆ F → R₁.measure Fᶜ = 0 := by
  intro P j S₁ S₂ R₁ R₂ F hR₁ hR₂ hF hR₂F hsupp
  -- (1) spt S₂ ⊆ F, via the measure criterion for the support
  have h2 : S₂.support ⊆ F := by
    intro x hx
    by_contra hxF
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hF.isOpen_compl x hxF
    exact ((Submission.dimred_im_mass_measure P j univ S₂ R₂ isOpen_univ hR₂).2.1 x (mem_univ x)).1
      hx ε hε (measure_mono_null hball hR₂F)
  -- (2) spt S₁ ⊆ F, since S₁ = S₂ + (S₁ - S₂) vanishes near every point off F
  have h1 : S₁.support ⊆ F := by
    intro x hx
    by_contra hxF
    have hz2 : x ∈ S₂.zeroRegion := by
      by_contra hc; exact hxF (h2 ⟨mem_univ x, hc⟩)
    have hz3 : x ∈ (S₁ - S₂).zeroRegion := by
      by_contra hc; exact hxF (hsupp ⟨mem_univ x, hc⟩)
    obtain ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, hW₁v⟩, hxW₁⟩ := mem_sUnion.mp hz2
    obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hxW₂⟩ := mem_sUnion.mp hz3
    have hcl : closure (W₁ ∩ W₂) ⊆ closure W₁ := closure_mono inter_subset_left
    apply hx.2
    refine mem_sUnion.mpr ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o, hW₁c.of_isClosed_subset isClosed_closure hcl,
      hcl.trans hW₁U, ?_⟩, hxW₁, hxW₂⟩
    intro ω hω
    have e1 : S₂ ω = 0 := hW₁v ω (hω.trans inter_subset_left)
    have e2 : S₁ ω - S₂ ω = 0 := hW₂v ω (hω.trans inter_subset_right)
    linarith
  -- (3) μ₁ vanishes off spt S₁
  have hnull := Submission.imrep_carrier_sdiff_support_null P j univ S₁ R₁ isOpen_univ hR₁
  have h3 : R₁.measure (S₁.support)ᶜ = 0 := by
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply' R₁.measurableSet_carrier]
    have : (S₁.support)ᶜ ∩ R₁.carrier = R₁.carrier \ S₁.support := by
      ext y; simp [and_comm]
    rw [this]; exact hnull
  exact measure_mono_null (compl_subset_compl.mpr h1) h3

## Key steps

1. spt S₂ ⊆ F: a point off the closed set F has a ball of μ₂-measure 0, so by Submission.dimred_im_mass_measure (b) it is not in spt S₂.
2. spt S₁ ⊆ F: off F both S₂ and S₁ − S₂ vanish on open sets with compact closure; on their intersection S₁ = S₂ + (S₁ − S₂) vanishes, so the point lies in the zero region of S₁.
3. μ₁(ℝ^P ∖ spt S₁) = 0, because μ₁ ≪ H^j⌞M₁ and H^j(M₁ ∖ spt S₁) = 0 by Submission.imrep_carrier_sdiff_support_null.
4. Monotonicity: ℝ^P ∖ F ⊆ ℝ^P ∖ spt S₁ gives μ₁(ℝ^P ∖ F) = 0.

## Reference use

### local-project

Queries:
- `cat manifest.json (project b4d606db1 = workspace HEAD, mathlib 25730c7c); cmp snapshot project/GMT/Ch07/Contract.lean and Submission.lean with the workspace copies (identical)`
- `python3 over dag.json: the selected node, its ancestors' depends_on and statuses, the exact lean_statement of all 14 dependency/reuse declarations, accepted nodes whose lean_statement mentions '.support', 'ᶜ = 0', 'cycle', 'competitor' (found dimred_mbl_lc_rc_cycle_competitor, dtc_bc_lc_rc_cycle_competitor, cbrld_ns_support_sub_subset, dimred_mbl_pf_imrep_carrier_mass_support, rsd_imrep_compact_measure_ne_top), and grep -c of the five new dimred_cs_sos_mt_cm_* names (0 hits)`
- `git show 35e359955ef6bac37033306b3f33a12c284b7174:GMT/Ch07/Submission.lean: Submission.dimred_mbl_lc_rc_cycle_competitor present with a type byte-identical to dag.json; its import lines equal the contract's`
- `grep -n over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean: GeometricCurrentOn, boundary(_apply), zero_apply, ext, massOn, mass, massOn_mono, massAdmissibleOn, VanishesOn, zeroRegion, support, testFormOnInclusion, restrictDomain, IsTestForm`
- `grep -rn over the snapshot mathlib: setIntegral_sdiff, integral_sub, measure_sdiff (measure_diff deprecated), ENNReal.le_of_add_le_add_left, withDensity_absolutelyContinuous, withDensity_apply, Measure.restrict_apply', Measure.restrict_restrict, starProjection_add_starProjection_orthogonal, inner_starProjection_left_eq_right, starProjection_apply_mem, starProjection_eq_self_iff, Submodule.isClosed_orthogonal, Submodule.closed_of_finiteDimensional, Submodule.mem_span_range_iff_exists_fun, Orthonormal.inner_right_fintype, isBounded_iff_subset_ball, isBounded_iff_subset_closedBall, Bornology.IsBounded.isCompact_closure`
- `grep -n '3.5\|left to the reader' book/chapter-07.txt; sed -n 405,420p (Lemma 3.5, proof left to the reader)`
- `lake env lean /tmp/cm-decomp/{T0,Assembly,A,B,D,E,F,Final}.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-8a972d0014/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-7f270cb1eb/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-local-compariso-4725781174/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`

Pins match. The manifest records project b4d606db1 (= workspace HEAD) and mathlib 25730c7c, and the snapshot Contract.lean and Submission.lean are byte-identical to the workspace files. Simon leaves Lemma 7.3.5 to the reader, so the children are extracted from the supplied project proof. Neither SimonGMT nor the snapshot mathlib contains the five new statements, and their names are unused in dag.json and the snapshot. One accepted declaration fits exactly: Submission.dimred_mbl_lc_rc_cycle_competitor (accepted; candidate 35e35995; type byte-identical; contract imports). It is reused as the Step 4 child. Other accepted lemmas found (cbrld_ns_support_sub_subset, dimred_mbl_pf_imrep_carrier_mass_support, rsd_imrep_compact_measure_ne_top) are not ancestor dependencies. Their content is covered in a few lines inside carried_transfer and box_cancellation, so they are not added. The snapshot mathlib supplies every library fact the child proofs use, under the names cited, including setIntegral_sdiff, measure_sdiff, ENNReal.le_of_add_le_add_left, starProjection_add_starProjection_orthogonal, inner_starProjection_left_eq_right, Submodule.mem_span_range_iff_exists_fun, Orthonormal.inner_right_fintype and Bornology.IsBounded.isCompact_closure. Lean check (Final.lean): the 5 new children are proved from stubs of exactly their cited dependencies, and the frozen parent type is proved from the child and dependency stubs. It compiles with no errors; sorry occurs only in the 14 stubs.
