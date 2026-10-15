# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.blowup_scale-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 (blow-ups) of the parent proof for one scale λ, together with the identity Γ(ω) = ∫ζ(ω)dμ of its step 0. The hypotheses (h2), (h4), (h5) are parts (2), (4), (5) of the parent's sibling dilation_calculus (dmcbr_ci_dilation_calculus) specialized to X := Γ, X' := Γ'; the parent supplies them, so they are simply hypotheses here. The only sibling used is blowup_measure (Submission.cbr_ci_bl_blowUp_restrict_scaling).
Notation: η := blowUpMap a λ, c := ofReal(λ^{−n}) = ENNReal.ofReal(λ⁻¹ ^ n), so μ' = c·D_#μ; ω̂ denotes the underlying form of a test form ω.
1. (The map and the rescaled mass measure.) η = D as functions (unfold blowUpMap, dilation, dilationCLM; smul_sub; abel). D is the homeomorphism e := (y ↦ λ⁻¹y) followed by (z ↦ −λ⁻¹a + z) (Homeomorph.smulOfNeZero, Homeomorph.addLeft), so D is a measurable embedding, surjective and injective, and a + λ·D(x) = x for every x. By the sibling blowup_measure (cbr_ci_bl_blowUp_restrict_scaling) applied to M, θ, a, λ: η(M) is Borel, and (part (iii), after rewriting μ by its hypothesis) μ' = c·D_#((Hⁿ⌞M) with density ofReal∘θ) = (Hⁿ⌞η(M)) with density y ↦ ofReal θ(a + λy).
2. (P0.) For a test n-form ω: since x ↦ ofReal θ(x) is measurable and finite, ∫ ζ(x)(ω̂(x)) dμ = ∫ (ofReal θ(x)).toReal·ζ(x)(ω̂(x)) d(Hⁿ⌞M) (integral_withDensity_eq_integral_toReal_smul). For x ∈ M, θ(x) > 0, so (ofReal θ(x)).toReal = θ(x) (ENNReal.toReal_ofReal); as M is Borel, setIntegral_congr_fun turns the last integral into ∫_M θ(x)·ζ(x)(ω̂(x)) dHⁿ, which equals Γ(ω) by hypothesis.
3. (P7.) Let ω be a test d-form and ω' := ω̂∘D. ω' is smooth, because ω̂ is smooth and D = (constant) + dilationCLM P λ is C^∞ (ContDiff.comp, contDiff_const.add, ContinuousLinearMap.contDiff), and it has compact support (HasCompactSupport.comp_homeomorph with e, since e = D); trivially tsupport ω' ⊆ ℝ^P. So ω' is a test d-form with ω'(y) = ω̂(D(y)) for all y, and (h2) gives ∂Γ'(ω) = λ^{−d}·∂Γ(ω') = λ^{−d}·0 = 0. Hence ∂Γ' = 0 (GeometricCurrentOn.ext, GeometricCurrentOn.zero_apply).
4. (P1.) For every K: μ'(K) = c·μ(D⁻¹K) (Measure.smul_apply, MeasurableEmbedding.map_apply) ≤ c·μ(ℝ^P) < ∞, as c < ∞ and μ(ℝ^P) < ∞ (ENNReal.mul_lt_top).
5. (P2.) Let W be open. W₀ := D⁻¹(W) is open (D is continuous) and D(W₀) = W (Set.image_preimage_eq, D surjective). By (h5) and the mass hypothesis for Γ: M_W(Γ') = M_{D(W₀)}(Γ') = c·M_{W₀}(Γ) = c·μ(W₀) = c·μ(D⁻¹W) = μ'(W) (Measure.smul_apply, MeasurableEmbedding.map_apply).
6. (P3.) y ↦ a + λy is measurable, so y ↦ ζ(a + λy) is strongly measurable (StronglyMeasurable.comp_measurable), hence μ'-a.e. strongly measurable.
7. (P5.) Apply (h4) to (P0).
8. (P6.) μ'(η(M)ᶜ) = c·μ(D⁻¹(η(M)ᶜ)) (MeasurableEmbedding.map_apply), and D⁻¹(η(M)ᶜ) = (D⁻¹(D(M)))ᶜ = Mᶜ (Set.preimage_compl, η = D, Function.Injective.preimage_image). Further μ(Mᶜ) = ∫⁻_{Mᶜ} ofReal θ d(Hⁿ⌞M) (withDensity_apply, Mᶜ Borel) = 0, because (Hⁿ⌞M)⌞Mᶜ = Hⁿ⌞(Mᶜ ∩ M) = Hⁿ⌞∅ = 0 (Measure.restrict_restrict, compl_inter_self, Measure.restrict_empty, lintegral_zero_measure). So μ'(η(M)ᶜ) = c·0 = 0.
9. (P8.) By (P5) and step 1, Γ'(ω) = ∫ ζ(a + λy)(ω̂(y)) d((Hⁿ⌞η(M)) with density ofReal θ(a + λ·)) = ∫_{η(M)} (ofReal θ(a + λy)).toReal·ζ(a + λy)(ω̂(y)) dHⁿ(y) (integral_withDensity_eq_integral_toReal_smul; y ↦ ofReal θ(a + λy) is measurable and finite). For y ∈ η(M), y = η(x) with x ∈ M, and a + λy = a + λD(x) = x, so (ofReal θ(a + λy)).toReal = θ(x) = θ(a + λy) and the integrand equals (θ(a + λy)·ζ(a + λy))(ω̂(y)) (smul_apply, smul_eq_mul). Since η(M) is Borel, setIntegral_congr_fun yields (P8). ∎

## Key steps

1. dilation a λ = blowUpMap a λ is a homeomorphism with inverse y ↦ a + λy; blowup_measure gives ofReal(λ^{−n})·D_#μ = (Hⁿ⌞η(M)) with density θ(a + λ·).
2. Γ(ω) = ∫ζ(ω)dμ (withDensity and θ > 0 on M); then (h4) gives the representation of Γ'.
3. ∂Γ' = 0 from (h2) applied to the pulled-back test form ω∘D.
4. Mass identity on open W from (h5) with W₀ = D⁻¹W; finiteness from μ(ℝ^P) < ∞; concentration on η(M) from μ(Mᶜ) = 0.
5. Rewrite the representation through the withDensity identity to get Γ'(ω) = ∫_{η(M)} θ(a + λy)ζ(a + λy)(ω(y)) dHⁿ.

## Reference use

### local-project

Queries:
- `cat SNAP/manifest.json -> mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; git log -1 (workspace HEAD b4d606db1); cmp SNAP/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean -> identical`
- `python3 -I scans of RUN/dag.json (2102 nodes): dmcbr_ci_blowup_limit vs cbr_ci_blowup_limit (identical lean_statement and natural_proof; statements differ only in sibling names); twin subtree statuses (blowup_measure accepted ef60a96f, covector_norm rlcr-lean, blowup_scale/density_bounds/rescaled_bounds/constant_limit/mass_bound/pairing_tendsto speculative-ready, other depth-6 leaves decomposing); frozen types of dmcbr_ci_dilation_calculus, dmcbr_ci_dilation_slice_property (identical to the accepted cbr_ci_* twins), cbr_ci_const_vector_massOn (accepted bc226ec6), cmcs_restrict_current (accepted a7cb2361), cbr_ci_bl_blowUp_restrict_scaling; lean_name lookup of the ten proposed dmcbr_ci_bl_* names -> none present`
- `read NODES/<twin>/decomposition-v1.json and decomposition-audit-v1.json for d8eab44069 (blowup_limit), 2a563f59dd (density_bounds), 6264bc6f37 (rescaled_bounds), 5981b082bc (constant_limit): all acceptable, every node natural_proof_acceptable; atomic decisions 9d402d3e08 (covector_norm, ~60-line scratch proof) and 6da3570ebf (blowup_scale, ~90-line scratch proof)`
- `git show 89c100ef / c23d5415 / a0358e1b / 84ebb489 / 80516330 / e4102347 / 7ebe5255 (twin speculative drafts); git show ef60a96f:, a7cb2361:, bc226ec6:GMT/Ch07/Submission.lean -> accepted declarations cbr_ci_bl_blowUp_restrict_scaling, cmcs_restrict_current, cbr_ci_const_vector_massOn with types identical to dag.json`
- `sed /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose: node.depth >= max_depth stops splitting; _existing_lean_name_problem: only accepted identical-type names are shareable; _leaf_author_task: a child adds only its single theorem, no helper declarations; child proof_base_commit = parent dispatch commit) and swarm-project.json (max_depth 6, max_children 12)`
- `rg -c dmcbr_ci_bl SNAP/project (no match, exit 1); rg -l dmcbr_ci_bl GMT .lake/packages/simongmt (no match, exit 1); rg -c 'cbr_ci_bl_blowUp_restrict_scaling|cmcs_restrict_current' SNAP/project (no match: DAG-accepted, not in the frozen base)`
- `rg -n in SNAP/mathlib/Mathlib: integral_withDensity_eq_integral_toReal_smul (MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:318, root namespace), ENNReal.limsup_const_mul_of_ne_top (Order/Filter/ENNReal.lean:165), tendsto_measure_cthickening_of_isClosed (MeasureTheory/Constructions/BorelSpace/Metric.lean:143), enorm_integral_le_lintegral_enorm (MeasureTheory/Integral/Bochner/Basic.lean:333), ContinuousAlternatingMap.opNorm_le_bound (Analysis/Normed/Module/Alternating/Basic.lean:241)`
- `lake env lean Names.lean: #check of 165 library names cited by the child proofs -> all resolve (integral_withDensity_eq_integral_toReal_smul is root-level, measure_ball_pos is Metric.measure_ball_pos); deprecated ContinuousLinearMap.smul_apply (use smul_apply) and ofReal_norm_eq_enorm (use ofReal_norm)`
- `lake env lean Remarks.lean: ContinuousAlternatingMap.map_perm unknown (AlternatingMap.map_perm on toAlternatingMap exists); Finset.prod_le_prod needs MulLeftMono; push_neg deprecated (push Not); ofReal_norm d : ofReal ‖d‖ = ‖d‖ₑ for d : MultiVector P n; dilation a lam y = blowUpMap a lam y by simp [dilation, dilationCLM, blowUpMap, smul_sub]; abel`
- `lake env lean Types.lean (the 12 child types as theorems after import GMT.Ch07.Submission in namespace GMT.Ch07 with the contract opens: sorry warnings only)`
- `lake env lean Assembly.lean (exact frozen parent type proved from the 12 child types and the 3 sibling types as axioms, no sorry; #print axioms: propext, Classical.choice, Quot.sound plus 14 of the 15 stubs, pairing_error entering only through pairing_tendsto and mass_bound)`
- `python3 -I: _recursive_lean.lean_contract.validate_lean_statement on all 12 child types -> valid and unchanged`
- `sed SimonGMT Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn = sSup ofReal T ω), Chapter06/Currents.lean (TestFormOn, GeometricCurrentOn, WeaklyConvergesOn, boundary, WeaklyConvergesOn.boundary), Chapter06/Forms.lean (Covector, IsTestForm)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-e02ee74e03/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-e02ee74e03/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/speculative-process-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2a563f59dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-2a563f59dd/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6264bc6f37/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6264bc6f37/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5981b082bc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-5981b082bc/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-9d402d3e08/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6da3570ebf/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-d8eab44069/speculative-prompt-v1.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/tmp/dmcbr_bl_decomp/Types.lean`
- `/tmp/dmcbr_bl_decomp/Assembly.lean`
- `/tmp/dmcbr_bl_decomp/Names.lean`
- `/tmp/dmcbr_bl_decomp/Remarks.lean`

The snapshot is compatible: its pins match and its contract is byte-identical to Submission.lean. The snapshot and SimonGMT contain no blow-up-limit declaration and no dmcbr_ci_bl name. The selected node has the same frozen type and supplied proof as the twin cbr_ci_blowup_limit, whose split and sub-splits were all audited acceptable. Because this node sits at depth 5 of 6, the twin's audited leaf statements are lifted to give 12 children with identical types. Two of them reuse the accepted cbr_ci_bl_blowUp_restrict_scaling and cmcs_restrict_current; the other ten have fresh dmcbr_ci_bl_* names. Every library name the child proofs cite resolves at the pinned revisions under the non-deprecated name given. All 12 child types elaborate and pass the validator. A sorry-free assembly proves the exact parent type from them and the three sibling types, using only propext, Classical.choice and Quot.sound beyond the stubs.
