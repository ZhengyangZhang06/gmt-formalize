# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.ambient_calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the 'Conventions' paragraph and basic fact (F3) of the parent proof (η_{a,t} is an affine homeomorphism and measurable embedding with inverse v ↦ a + tv; η_{y,s}∘η_{a,t} = η_{a+ty,ts}; η_{a,t}^{−1}(B_ρ(w)) = B_{tρ}(a + tw); η_{a,t}(B_ρ(v)) = B_{ρ/t}(η_{a,t}(v)); μ^{a,t}(A) = t^{−n}μ(η_{a,t}^{−1}A); (μ^{a,t})^{y,s} = μ^{a+ty,ts}; ℝ^P is a C² submanifold of itself via ψ = id), and parent step 3(h) (restriction commutes with the push-forward by the measurable embedding η). Simon uses these identities tacitly in 7.3.3, proof of 3.3(1), (10) (chapter-07.txt line 467).
Notation: for s > 0, η_{a,s}(v) = −(s^{−1}•a) + s^{−1}•v = s^{−1}(v − a) (contract dilation, dilationCLM P s = s^{−1}•id).
0. (η is an affine homeomorphism.) For s > 0, v ↦ a + s·v is a two-sided inverse of η_{a,s}: s^{−1}((a + s v) − a) = v and a + s·s^{−1}(v − a) = v. Both maps are continuous (affine), so η_{a,s} is a homeomorphism of ℝ^P (Homeomorph.smulOfNeZero s^{−1} followed by Homeomorph.addLeft (−(s^{−1}•a))); hence it is measurable, a measurable embedding (Homeomorph.measurableEmbedding), injective, surjective and an open map, and ‖η_{a,s}(v) − η_{a,s}(v')‖ = s^{−1}‖v − v'‖.
1. (ℝ^P is a C² submanifold of itself.) Let y ∈ univ. Take d = P, V := univ ⊆ Euclid P, W := univ ⊆ Euclid P and ψ := id. Then V and W are open, y ∈ W, ψ is C^∞, so ContDiffOn ℝ 2 ψ V (contDiff_id.contDiffOn), ψ is injective on V, ψ '' V = univ = W ∩ univ, for every compact K ⊆ W the set V ∩ ψ^{−1}(K) = K is compact, and for every z ∈ V, fderiv ℝ ψ z = ContinuousLinearMap.id (fderiv_id) is injective. Hence IsEmbeddedSubmanifold 2 P univ.
2. For Borel A: (ofReal(s^{−n})•ν.map η_{a,s})(A) = ofReal(s^{−n})·(ν.map η_{a,s})(A) (Measure.smul_apply, smul_eq_mul) = ofReal(s^{−n})·ν(η_{a,s}^{−1}(A)) (Measure.map_apply, η measurable by 0, A measurable).
3. For v ∈ ℝ^P: v ∈ η_{a,s}^{−1}(B_ρ(w)) ⟺ ‖s^{−1}(v − a) − w‖ < ρ ⟺ s^{−1}‖v − (a + s w)‖ < ρ (since s^{−1}(v − a) − w = s^{−1}(v − (a + s w)) and ‖s^{−1}u‖ = s^{−1}‖u‖) ⟺ ‖v − (a + s w)‖ < sρ (multiply by s > 0) ⟺ v ∈ B_{sρ}(a + s w).
4. If ‖v − c‖ < ρ then ‖η_{a,s}(v) − η_{a,s}(c)‖ = s^{−1}‖v − c‖ < ρ/s, so η_{a,s}(B_ρ(c)) ⊆ B_{ρ/s}(η_{a,s}(c)). Conversely, if ‖u − η_{a,s}(c)‖ < ρ/s, put v := a + s u; then η_{a,s}(v) = u and, as c = a + s·η_{a,s}(c), ‖v − c‖ = s‖u − η_{a,s}(c)‖ < ρ, so u ∈ η_{a,s}(B_ρ(c)).
5. η_{a,s} is surjective (0), so η_{a,s}(univ) = univ; it is a homeomorphism, hence an open map, so η_{a,s}(A) is open for open A (Homeomorph.isOpenMap).
6. For every v: η_{y,t}(η_{a,s}(v)) = t^{−1}(s^{−1}(v − a) − y) = (st)^{−1}(v − a − s y) = η_{a+sy,st}(v), using (st)^{−1} = s^{−1}t^{−1}. So η_{y,t}∘η_{a,s} = η_{a+sy,st} (funext) and η_{y,t}(η_{a,s}(A)) = (η_{y,t}∘η_{a,s})(A) = η_{a+sy,st}(A) (Set.image_image).
7. ofReal(t^{−n})•(ofReal(s^{−n})•ν.map η_{a,s}).map η_{y,t} = ofReal(t^{−n})•ofReal(s^{−n})•(ν.map η_{a,s}).map η_{y,t} (Measure.map_smul) = (ofReal(t^{−n})·ofReal(s^{−n}))•ν.map(η_{y,t}∘η_{a,s}) (smul_smul; Measure.map_map with both maps measurable) = ofReal((st)^{−n})•ν.map η_{a+sy,st}, by step 6 and ofReal(t^{−n})·ofReal(s^{−n}) = ofReal(t^{−n}·s^{−n}) = ofReal((st)^{−n}) (ENNReal.ofReal_mul, both factors ≥ 0; mul_inv, mul_pow).
8. η_{0,1}(v) = −(1^{−1}•0) + 1^{−1}•v = v, so η_{0,1} = id. Hence ν.map η_{0,1} = ν (Measure.map_id), ofReal(1^{−n}) = ofReal 1 = 1, 1•ν = ν, and η_{0,1}(A) = A (Set.image_id).
9. Let B be Borel and η := η_{a,s}. Since η is a measurable embedding (0), (ν.map η).restrict(η(B)) = (ν.restrict(η^{−1}(η(B)))).map η (MeasurableEmbedding.restrict_map) = (ν.restrict B).map η, because η is injective, so η^{−1}(η(B)) = B (Set.preimage_image_eq). Restriction commutes with scalar multiplication ((c•μ).restrict S = c•(μ.restrict S), Measure.restrict_smul). Multiplying by ofReal(s^{−n}) gives ofReal(s^{−n})•(ν.restrict B).map η = (ofReal(s^{−n})•ν.map η).restrict(η(B)). ∎

## Key steps

1. η_{a,s} = s^{−1}(· − a) is an affine homeomorphism with inverse v ↦ a + s v; ψ = id is a C² chart, so ℝ^P is an embedded C² submanifold of itself.
2. Ball preimages/images and compositions follow from ‖η(v) − η(v')‖ = s^{−1}‖v − v'‖ and η_{y,t}∘η_{a,s} = η_{a+sy,st}.
3. The measure identities follow from Measure.map_apply, map_smul, map_map, map_id and MeasurableEmbedding.restrict_map.

## Reference use

### local-project

Queries:
- `python3 -I -c json.load(local-references/123e8435b4a2469b/manifest.json); cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `python3 scan of dag.json lean_statement fields for 'BoundaryVanishes (blowUp', 'blowUp', 'restrict', 'withDensity', 'map (dilation', 'IsEmbeddedSubmanifold 2 (n + k) univ', 'HasCompactSupport f → ∫', with status, candidate_commit and depends_on of each match`
- `python3 extraction of subproblem.lean_statement/natural_proof/proof_key_steps from the parent-child-handoff.json of the six reused accepted nodes; isolated-comparator-result.json of borel-restriction-a1 and of blowup_limit_cycle (node dir ...-34a94daa02)`
- `grep -n '^theorem|^def|^structure|^instance' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,AffineCurrentPushforward,Mass}.lean; sed -n 20,120p Chapter03/Rectifiable.lean`
- `grep -rn 'ext_of_integral_eq_on_compactlySupported|Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure|isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts|theorem restrict_map|measure_null_of_locally_null|extraction_of_frequently_atTop|IsCompact.tendsto_subseq|continuous_of_dominated|tendsto_integral_filter_of_dominated_convergence|euclideanHausdorffMeasure_smul₀|ext_of_forall_integral_eq' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -c 'idtp_fons_cc_\|idtp_fcc_' dag.json; grep -rl nodes/; grep -rl --include=Submission.lean ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/; git log --all -S idtp_fons_cc_ (all empty)`
- `sed -n 300,330p and 420,535p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt (Simon 7.3.1 and the proof of 7.3.3)`
- `lake env lean /tmp/ccd_k7q2/final/Types.lean; lake env lean /tmp/ccd_k7q2/final/AssemblyAx.lean (#print axioms); lake env lean /tmp/ccd_k7q2/final/AC.lean, DR.lean, CR.lean, TMB.lean`
- `python3 replay of Runtime._dependency_problem, Runtime._topological and Runtime._existing_lean_name_problem on /tmp/ccd_k7q2/final/subproblems_final.json against dag.json (updated_at 2026-10-13T19:24:44Z)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5982ed9bb9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-34a94daa02/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-34a94daa02/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-borel-restriction-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-measure-invaria-4622bb5be6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/ccd_k7q2/final/Types.lean`
- `/tmp/ccd_k7q2/final/AssemblyAx.lean`
- `/tmp/ccd_k7q2/final/AC.lean`
- `/tmp/ccd_k7q2/final/DR.lean`
- `/tmp/ccd_k7q2/final/CR.lean`
- `/tmp/ccd_k7q2/final/TMB.lean`

Pins match: manifest project b4d606db1 = workspace HEAD, Mathlib 25730c7c; SimonGMT 2b36630; the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Reusable accepted declarations (dag.json; candidate commits present locally; isolated comparator passed): dimred_im_mass_measure (01ae2c59), dtc_blowUp_scaling (a94d596c), cone_current_imrep_measure_smul_image (e183b985), idtp_tpf_blowUp_limit_boundaryVanishes (f498a8ef; exactly the parent's (F7)), dor_lmb_imrep_restrict_current (90d679af; Borel restriction of an IMRep with weight μ⌞A, used for 3(h)) and dimred_cs_mi_withDensity_dilate (fc55b748; n-homogeneity of Hⁿ.withDensity f, used for step 14). Their types are copied byte for byte. No accepted or library declaration states the ambient-submanifold fact, the dilation calculus of rescaled measures, (F9) from DEM, the monotonicity consequences, the tangent-measure statement or the positive-scale family, so these enter as the six fresh children (fresh idtp_fons_cc_ names occur nowhere). Library facts used in the child proofs: SimonGMT GeometricCurrentOn.boundary_affinePushforward (Chapter06/AffineCurrentPushforward.lean:188), restrictDomain_apply, zeroRegion and support (CurrentLocalEquality.lean), massOn (Mass.lean:68), countablyRectifiable_of_measure_zero (Chapter03/Rectifiable.lean:45). Snapshot Mathlib: Measure.ext_of_integral_eq_on_compactlySupported (RieszMarkovKakutani/Real.lean:412), Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (Measure/Regular.lean:1183), MeasurableEmbedding.restrict_map (Measure/Restrict.lean:890), measure_null_of_locally_null (OuterMeasure/Basic.lean:150), extraction_of_frequently_atTop (AtTopBot/Basic.lean:114), IsCompact.tendsto_subseq (Topology/Sequences.lean:298), tendsto_integral_filter_of_dominated_convergence, euclideanHausdorffMeasure_smul₀ (Euclidean/Volume/Measure.lean:152). Lean: all 12 types elaborate. The parent's frozen type compiles from the child types (stated as axioms) and uses exactly the six new children plus dimred_im_mass_measure, dtc_blowUp_scaling, dor_lmb_imrep_restrict_current and the standard axioms. ambient_calculus and density_representation are fully proved; cycle_rescale is proved from its siblings' frozen types; tangent_measures (B) is derived from (A). The runtime replay accepts the split.
