# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.chain_boundary-a1.pullback_divergence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (“dγ as a divergence … By SimonGMT exteriorDerivative_apply (removeNth i v = v ∘ succAbove i) and the chain rule (DΦ_p(y)e_i = e_{ι(i)}): dγ(Φ_p y)(E_p) = Σ_i (−1)^i D[γ(·)(E_p∘succAbove i)](Φ_p y)(e_{ι(i)}) = Σ_i ∂_i G_i(y)”). Here the integer base point toLp(b) is generalised to an arbitrary point a ∈ Euclid P, and ι is arbitrary (no monotonicity is used). The C¹ claim (a) is that step's remark “G is C^∞”, stated for C¹ forms.

Notation. w_j := EuclideanSpace.single (ι j) 1 ∈ Euclid P. Φ(y) := a + Σ_j y j • w_j. E := (w_j)_{j ∈ Fin (m+1)}. For i ∈ Fin (m+1), E∘succAbove i = (w_{succAbove i l})_{l ∈ Fin m} = (fun l => EuclideanSpace.single ((ι ∘ Fin.succAbove i) l) 1). F_i(y) := (−1)^i · γ(Φ y)(E∘succAbove i). e_i := EuclideanSpace.single i 1 ∈ Euclid (m+1).

1. Φ is affine. Let L := Σ_j (EuclideanSpace.proj j).smulRight w_j : Euclid (m+1) →L[ℝ] Euclid P. Then L v = Σ_j v j • w_j and Φ = a + L. Hence Φ is C¹ (contDiff_const.add L.contDiff), and HasFDerivAt Φ L y for every y (L.hasFDerivAt.const_add a). Also L e_i = Σ_j (e_i) j • w_j = w_i, since (e_i) j = 1 if j = i and 0 otherwise.
2. (a) Regularity. For a fixed tuple v ∈ (Euclid P)^m, the evaluation ω ↦ ω v is the continuous linear map ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v. So y ↦ γ(Φ y)(E∘succAbove i) equals (apply (E∘succAbove i)) ∘ γ ∘ Φ. This is a composition of C¹ maps (γ by hypothesis, Φ by step 1), so it is C¹. Multiplying by the constant (−1)^i keeps it C¹ (contDiff_const.mul). Hence every F_i is C¹.
3. (b) Exterior derivative. γ is C¹, hence differentiable at x := Φ y. By SimonGMT's exteriorDerivative_apply (Mathlib extDeriv_apply), exteriorDerivative γ x E = Σ_i (−1 : ℤ)^i • fderiv ℝ (fun x' => γ x' (Fin.removeNth i E)) x (E i). Here Fin.removeNth i E = E∘succAbove i by definition, and E i = w_i.
4. Chain rule. Put g_i(x') := γ x' (E∘succAbove i). Since γ has a derivative at x, so does g_i (HasFDerivAt.continuousAlternatingMap_apply_const). Write D_i := fderiv ℝ g_i x. Since F_i = (−1)^i · (g_i ∘ Φ), HasFDerivAt.comp with step 1 and then HasFDerivAt.const_mul give HasFDerivAt F_i ((−1)^i • D_i.comp L) y. Hence fderiv ℝ F_i y e_i = (−1)^i · D_i (L e_i) = (−1)^i · D_i w_i.
5. Summation. The ℤ-scalar action (−1 : ℤ)^i • r equals the real product (−1 : ℝ)^i · r (zsmul_eq_mul with the cast of (−1)^i). So by step 4 the i-th term in step 3 equals fderiv ℝ F_i y e_i. Summing over i gives exteriorDerivative γ (Φ y) E = Σ_i fderiv ℝ F_i y e_i for every y ∈ Euclid (m+1). Together with (a), this is the claim. ∎

## Key steps

1. Φ(y) = a + L y, where L v = Σ_j v_j e_{ι(j)} is a continuous linear map. Φ is C¹ with DΦ ≡ L, and L e_i = e_{ι(i)}.
2. F_i = (−1)^i · ev_{E∘succAbove i} ∘ γ ∘ Φ is C¹, since evaluation is ContinuousAlternatingMap.apply, a continuous linear map.
3. exteriorDerivative_apply: dγ(Φ y)(E) = Σ_i (−1)^i D[γ(·)(removeNth i E)](Φ y)(e_{ι(i)}), with removeNth i E = E∘succAbove i.
4. Chain rule: DF_i(y)e_i = (−1)^i D[γ(·)(E∘succAbove i)](Φ y)(L e_i) = (−1)^i D[…](Φ y)(e_{ι(i)}). Sum over i, converting the ℤ-action (−1)^i • to real multiplication.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); manifest.json project_commit b4d606db1…, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d`
- `rg -n 'cmcdtfrcb' project mathlib/Mathlib -g '*.lean' (exit 1, no match); python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name for cmcdtfrcb|cube_divergence|cube_stokes|face_regroup|regroup|cubical (0 hits); 'divergence'/'stokes' hits inspected (cmr_coordinate_divergence_form, codim1_rdo_dg_vdl_integral_divergence_eq_zero, cbr_cipi_plane_halfspace_stokes, …): none has an identical type`
- `rg -n -i 'IsLatticeChain|latticeFace|LatticeFaceIndex' project/GMT -g '*.lean' (only Ch06/Submission.lean, separate module); rg -n -i 'cube|stokes|divergence' project/GMT -g '*.lean' (only tangentialDivergence defs); rg -n -i 'integral_divergence|divergence theorem|insertNth|unit cube|cube' lake-packages-25730c7c/simongmt/Poincare -g '*.lean' (no cube Stokes/divergence lemma)`
- `grep -n 'theorem integral_divergence_of_hasFDerivAt_off_countable' mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean (lines 266, 296, 313); lake env lean probe under import GMT.Ch07.Submission: Unknown identifier integral_divergence_of_hasFDerivAt_off_countable' and BoxIntegral.Box (module outside the frozen import closure)`
- `grep -rn 'volume_preserving_ofLp|volume_preserving_toLp|univ_pi_Ioo_ae_eq_Icc|strictMono_succAbove|prod_fiberwise_of_maps_to|continuousAlternatingMap_apply|def removeNth|def insertNthEquiv|setIntegral_preimage_emb' mathlib/Mathlib`
- `lake env lean Avail.lean/Avail2.lean probes: intervalIntegral.integral_eq_sub_of_hasDerivAt, intervalIntegral.integral_of_le, integral_Ioc_eq_integral_Ioo, integral_prod_symm, Measure.prod_restrict, volume_preserving_piFinSuccAbove, MeasurableEquiv.piFinSuccAbove_symm_apply, Continuous.finInsertNth, HasFDerivAt.continuousAlternatingMap_apply_const, ContinuousAlternatingMap.apply, Finset.sum_fiberwise_of_maps_to, Fin.sum_univ_succAbove all available; Fin.insertNthEquiv_apply is pointwise (rfl used instead)`
- `git show 14cdd14d8 / fa0865963 (leaf gate: 'leaf proof must preserve the complete frozen base byte-for-byte', no imports/helpers); git show 84d5ca9d5:GMT/Ch07/Submission.lean (proof base = contract imports only, 457 lines); python3 scan of .humanize/swarm-configs (max_nodes 5000, max_depth 6)`
- `python3 verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') → replayed scope; lake env lean /tmp/cbsplit-k7q2/lean/Node{A1,B1,B,C,Parent}.lean (all four child types and the parent type elaborate)`
- `lake env lean /tmp/cbsplit-k7q2/lean/Assembly.lean (frozen cube_stokes + face_regroup types ⇒ selected frozen type; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/cbsplit-k7q2/lean/Combined.lean (each child proved as ONE theorem under base imports; parent assembled; exact Submission.X comparator-style checks; no errors; standard axioms only)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-416ba8809f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/tmp/cbsplit-k7q2/lean/Combined.lean`
- `/tmp/cbsplit-k7q2/lean/Assembly.lean`
- `/tmp/cbsplit-k7q2/lean/ValidA1.lean`
- `/tmp/cbsplit-k7q2/lean/ValidB1.lean`
- `/tmp/cbsplit-k7q2/lean/ValidB.lean`
- `/tmp/cbsplit-k7q2/lean/ValidC.lean`
- `/tmp/cbsplit-k7q2/lean/Avail.lean`
- `/tmp/cbsplit-k7q2/lean/Avail2.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace, and Submission.lean equals the contract. No local declaration gives cubical Stokes, a cube divergence identity, or face regrouping. The Ch06 lattice-chain definitions live in a separate module and come with no proofs. No accepted DAG node has an identical type to reuse. Mathlib's box divergence theorem (DivergenceTheorem.lean, lines 266–313) exists in the snapshot but is NOT reachable from the frozen Ch07 imports, and leaves may not add imports. So the cube identity is split per coordinate and proved with reachable tools: PiLp.volume_preserving_toLp, volume_preserving_piFinSuccAbove, Measure.prod_restrict, integral_prod_symm, intervalIntegral.integral_eq_sub_of_hasDerivAt, ContinuousAlternatingMap.apply and SimonGMT exteriorDerivative_apply. Lean checks under `import GMT.Ch07.Submission` alone pass: all four children are proved as single theorems, and the parent is assembled from cube_stokes and face_regroup, using only standard axioms. The prefix cmcdtfrcb_ collides with nothing.
