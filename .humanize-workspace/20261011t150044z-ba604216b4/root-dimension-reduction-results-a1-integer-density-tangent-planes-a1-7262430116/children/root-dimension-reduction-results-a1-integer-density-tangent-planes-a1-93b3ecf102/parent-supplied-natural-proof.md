# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.cone_chart-a1.radial_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 8 (radial structure), with the data produced in steps 5–7 of the parent proof turned into hypotheses. Conventions: J := (r₀ − s, r₀ + s), I := (−s, s); for w ∈ Euclid 2, w₀, w₁ are its coordinates (Lean w 0, w 1); ⟨⟨t, α⟩⟩ ∈ Euclid 2 is the point with coordinates (t, α) (Lean !₂[t, α]); R := {w : w₀ ∈ J, w₁ ∈ I}; B_r(y) is the open ball. Note ⟨⟨t, α⟩⟩ ∈ R iff t ∈ J and α ∈ I (simp), r₀ − s > 0 (as s < r₀), and r₀ ∈ J (as s > 0).
1. Fix α ∈ I and let A := {t ∈ ℝ : t ∈ J and G(⟨⟨t, α⟩⟩) = tγ(α)}. The map t ↦ ⟨⟨t, α⟩⟩ is continuous (each coordinate is continuous; PiLp.continuous_toLp) and maps J into R, so φ₁(t) := G(⟨⟨t, α⟩⟩) is continuous on J (ContinuousOn.comp); φ₂(t) := tγ(α) is continuous on ℝ.
2. (r₀ ∈ A.) r₀ ∈ J, and G(⟨⟨r₀, α⟩⟩) = r₀γ(α) by hypothesis.
3. (A is open.) Let t ∈ A and x := tγ(α) = G(⟨⟨t, α⟩⟩). Since ⟨⟨t, α⟩⟩ ∈ R, x ∈ G(R) = M ∩ N. As N is open, choose η₀ > 0 with B_{η₀}(x) ⊆ N (Metric.isOpen_iff), and put η := min(η₀, t − (r₀ − s)) > 0 (t ∈ J). Let t′ ∈ ℝ with |t′ − t| < η. Then t′ ≥ t − |t′ − t| > t − (t − (r₀ − s)) = r₀ − s > 0, and t > r₀ − s > 0.
 (a) y := t′γ(α) ∈ N: ‖y − x‖ = ‖(t′ − t)γ(α)‖ = |t′ − t|·‖γ(α)‖ = |t′ − t| < η ≤ η₀, so y ∈ B_{η₀}(x) ⊆ N; in particular y ∈ B_ρ(p).
 (b) y ∈ M: x ∈ M and x ∈ N ⊆ B_ρ(p), so x ∈ M ∩ B_ρ(p); c := t′/t > 0 and c·x = (t′/t)·tγ(α) = y ∈ B_ρ(p); the radial hypothesis gives y ∈ M.
 (c) Hence y ∈ M ∩ N = G(R), so y = G(w) for some w ∈ R. Then w = F(G(w)) = F(y) = F(t′γ(α)) = ⟨⟨t′, α⟩⟩ (t′ > 0). Therefore ⟨⟨t′, α⟩⟩ = w ∈ R, i.e. t′ ∈ J, and G(⟨⟨t′, α⟩⟩) = G(w) = y = t′γ(α). So t′ ∈ A.
 Thus the ball of radius η about t lies in A, and A is open.
4. (closure(A) ∩ J ⊆ A.) Let t ∈ closure(A) ∩ J. As J is open and contains t, φ₁ and φ₂ are continuous at t (ContinuousOn.continuousAt with isOpen_Ioo.mem_nhds). Since t ∈ closure(A), the filter 𝓝[A] t is nontrivial (mem_closure_iff_nhdsWithin_neBot). Along 𝓝[A] t we have φ₁ → φ₁(t) and φ₂ → φ₂(t) (nhdsWithin_le_nhds); since φ₁ = φ₂ on A, also φ₁ → φ₂(t) (Tendsto.congr' with eventually_nhdsWithin_of_forall). Limits in the Hausdorff space Euclid P are unique (tendsto_nhds_unique), so φ₁(t) = φ₂(t), i.e. t ∈ A.
5. (Connectedness.) J is preconnected (isPreconnected_Ioo), A is open (step 3), J ∩ A ∋ r₀ is nonempty (step 2) and closure(A) ∩ J ⊆ A (step 4). Hence J ⊆ A (IsPreconnected.subset_of_closure_inter_subset). Since α ∈ I was arbitrary: G(⟨⟨t, α⟩⟩) = tγ(α) for all t ∈ J and α ∈ I.
6. (First conclusion.) Let w ∈ R. Then w = ⟨⟨w₀, w₁⟩⟩ (both sides have the same coordinates; extensionality over Fin 2), w₀ ∈ J and w₁ ∈ I, so G(w) = G(⟨⟨w₀, w₁⟩⟩) = w₀γ(w₁) by step 5.
7. (Second conclusion.) M ∩ N = G(R). If x ∈ G(R), x = G(w) with w ∈ R, then x = w₀γ(w₁) by step 6 with (w₀, w₁) ∈ J × I. Conversely, if (t, α) ∈ J × I, then ⟨⟨t, α⟩⟩ ∈ R and tγ(α) = G(⟨⟨t, α⟩⟩) ∈ G(R) by step 5. Hence M ∩ N = {tγ(α) : (t, α) ∈ J × I}, the image of J ×ˢ I under q ↦ q.1·γ(q.2). ∎

## Key steps

1. Fix α ∈ I; A := {t ∈ J : G(t,α) = tγ(α)} contains r₀ by hypothesis.
2. A is open: near t ∈ A, y = t′γ(α) stays in the open set N, lies in M by radial invariance (y = (t′/t)·tγ(α)), so y = G(w) with w ∈ R, and F∘G = id with F(t′γ(α)) = (t′,α) forces w = (t′,α), t′ ∈ A.
3. closure(A) ∩ J ⊆ A because t ↦ G(t,α) and t ↦ tγ(α) are continuous on the open interval J and limits are unique.
4. J is preconnected, so J ⊆ A; hence G(w) = w₀γ(w₁) on R.
5. M ∩ N = G(R) is therefore the image of J × I under (t,α) ↦ tγ(α).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `sed -n 215,240p GMT/Ch07/Contract.lean (IsEmbeddedSubmanifold, tangentSpace); grep -n 'namespace|^open' GMT/Ch07/Contract.lean`
- `python3 -I scan of dag.json: sibling lean_statements under ...stationary_cone_sheet_planar-a1 (tangent_plane_mem, local_inverse, angle_curve); grep -o 'idtp_ccd_scsp_[a-z_]*' dag.json; grep -c 'idtp_ccd_scsp_cc_' dag.json (0); grep -rl idtp_ccd_scsp_cc_ ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean and run nodes (no match)`
- `python3 -I scan of dag.json lean_statements for: arctan with fderiv/ContDiffOn | 'inner ℝ u e = 0 ∧ ∀ v' (orthonormal completion) | IsPreconnected | 'w 0 ∈' | 'deriv γ' with Set.range | 'q.1 • γ q.2'`
- `grep -rn 'theorem IsPreconnected.subset_of_closure_inter_subset|theorem hasStrictFDerivAt_norm_sq|theorem HasFDerivAt.sqrt|theorem HasFDerivAt.arctan|theorem contDiffOn_piLp|theorem finrank_span_eq_card|theorem exists_of_lt|theorem eq_of_le_of_finrank_eq|theorem mem_closure_iff_nhdsWithin_neBot|theorem ContinuousOn.isOpen_inter_preimage|theorem Filter.EventuallyEq.fderiv_eq|theorem HasFDerivAt.smul|theorem contDiffAt_norm|theorem contDiff_arctan|theorem hasDerivAt_inv|theorem HasFDerivAt.unique|theorem mem_span_pair|theorem tendsto_nhds_unique|theorem isPreconnected_Ioo|theorem sqrt_lt'|theorem orthonormal_iff_ite|theorem range_cons' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/cc_chart_dec_q41/{Probe,Probe2,Stubs,Assembly,C1,C2,C3,C4,C6,Combined}.lean and /tmp/cc_chart_dec_q41/out/FromJson.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7262430116/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7262430116/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Connected/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/SetLike/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ClusterPt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/IntermediateValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/VecNotation.lean`
- `/tmp/cc_chart_dec_q41/Combined.lean`
- `/tmp/cc_chart_dec_q41/Assembly.lean`
- `/tmp/cc_chart_dec_q41/out/FromJson.lean`

Pins match: snapshot project_commit b4d606d = workspace HEAD and mathlib 25730c7c = .lake/packages/mathlib HEAD. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (namespace GMT.Ch07; opens Filter Function Set MeasureTheory Metric, scoped ENNReal Topology, Poincare.SimonGMT.Chapter06, and Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)).

The frozen sibling types tangent_plane_mem, local_inverse and angle_curve were read from dag.json; the parent assembly uses them verbatim.

No accepted DAG declaration states any child:
- The only near match is idtp_tdc_dlc_ld_orthonormal_partner, which is alpha-equivalent to plane_orthonormal. It is in another branch and still decomposing, so it is not reusable.
- idtp_cse_fa_sector_open_contDiffOn and idtp_cse_rc_angle_fderiv concern a different ℝ×ℝ-valued map and are not accepted.
- The prefix idtp_ccd_scsp_cc_ is unused.

Every Mathlib lemma cited in the child proofs exists in the pinned snapshot, e.g. IsPreconnected.subset_of_closure_inter_subset (Topology/Connected/Basic.lean:434), hasStrictFDerivAt_norm_sq (InnerProductSpace/Calculus.lean:197), HasFDerivAt.sqrt, HasFDerivAt.arctan, contDiffOn_piLp (ContDiff/WithLp.lean:58), finrank_span_eq_card, IsConcreteLE.exists_of_lt (Basic/SetLike/Basic.lean:284), Submodule.eq_of_le_of_finrank_eq, mem_closure_iff_nhdsWithin_neBot, ContinuousOn.isOpen_inter_preimage, Filter.EventuallyEq.fderiv_eq, HasFDerivAt.smul, contDiffAt_norm, Real.contDiff_arctan, hasDerivAt_inv, HasFDerivAt.unique, Submodule.mem_span_pair, tendsto_nhds_unique, isPreconnected_Ioo, Real.sqrt_lt', orthonormal_iff_ite and Matrix.range_cons. Names that do not exist here and are not cited: HasFDerivAt.norm, HasFDerivAt.div, HasFDerivAt.inv and hasFDerivAt_piLp. SetLike.exists_of_lt is deprecated.

Lean checks:
- All five child types elaborate after import GMT.Ch07.Submission.
- Each child has a complete Lean proof with axioms propext, Classical.choice and Quot.sound only.
- The parent's exact frozen type is proved from the five children plus the three sibling stubs; sorryAx appears only through the sibling stubs.
