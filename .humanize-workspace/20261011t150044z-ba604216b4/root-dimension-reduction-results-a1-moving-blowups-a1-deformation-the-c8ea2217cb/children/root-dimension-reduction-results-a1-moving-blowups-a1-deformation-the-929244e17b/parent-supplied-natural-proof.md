# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_pushforward-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_pushforward-a1.piece_rep-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2 (B1) and 3 (B2′) of the supplied proof and the (AF) computation of its step 6, for an IMRep of finite total multiplicity. Conventions: Euclid P = ℝ^P; Hⁿ := μHE[n] (Euclidean-normalized Hausdorff measure); λ := volume on ℝⁿ = Euclid n (λ = μHE[n] there); e_a := EuclideanSpace.single a 1 (a ∈ Fin n); for a map K, DK(u) := fderiv ℝ K u (the zero map where K is not differentiable) and v_K(u) := (DK(u)e_a)_a; J_K(u) := √det(⟨DK(u)e_a, DK(u)e_b⟩)_{a,b} (Real.sqrt of the Gram determinant); |α| := covectorEuclideanNorm α; for v : Fin n → ℝ^P, ev_v ∈ Λ_n(ℝ^P) (MultiVector P n) is α ↦ α(v) (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v); an IMRep R has carrier M, multiplicity θ := R.mult and orientation ξ := R.orient.
1. (Pieces, B1.) M is Borel and countably n-rectifiable (R.measurableSet_carrier, R.rectifiable). (B1) applied to M gives G_i (L_i-Lipschitz), Borel A_i, m_i > 0 with m_i|a − a'| ≤ |G_i(a) − G_i(a')| on A_i, G_i differentiable with injective derivative on A_i, G_i(A_i) Borel ⊆ M, pairwise disjoint, and Hⁿ(M ∖ ⋃_i G_i(A_i)) = 0. Write J_i := J_{G_i}, v_i(u) := v_{G_i}(u).
2. (Signs.) For each i the sibling piece_sign (with (IMC), U := ℝ^P open, R, G_i, A_i, L_i, m_i; G_i(A_i) ⊆ M) gives a measurable s_i : ℝⁿ → ℤ, s_i ∈ {1, −1}, with J_i(u)·ξ(G_i u)(α) = s_i(u)·α(v_i(u)) for every α, for λ-a.e. u ∈ A_i.
3. (Definitions.) w_i(u) := (θ(G_i u) : ℤ)·s_i(u) and c_i(u) := J_i(u). w_i is measurable (θ measurable, G_i continuous, s_i measurable); c_i is measurable by the sibling area_lintegral, part (i), and c_i ≥ 0. Moreover |w_i(u)| = θ(G_i u).
4. (Gram bound.) For u ∈ A_i and every α, (GB)(i) gives |α(v_i(u))| ≤ |α|·√det Gram(v_i(u)) = c_i(u)·|α|.
5. (Measure comparison.) By the sibling bilip_measure (G_i, A_i, L_i, m_i), ofReal(m_i)ⁿλ(Z) ≤ Hⁿ(G_i(Z)) for Z ⊆ A_i. For Borel B ⊆ ℝ^P take Z := A_i ∩ G_i⁻¹(B): ofReal(m_i)ⁿ·(λ⌞A_i)(G_i⁻¹B) ≤ Hⁿ(G_i(Z)) ≤ Hⁿ(G_i(A_i) ∩ B) = (Hⁿ⌞G_i(A_i))(B). So ofReal(m_i)ⁿ • Measure.map G_i (λ⌞A_i) ≤ Hⁿ⌞G_i(A_i), and for every Borel f ≥ 0, ofReal(m_i)ⁿ∫⁻_{A_i} f(G_i u) du ≤ ∫⁻_{G_i(A_i)} f dHⁿ (lintegral_map).
6. (Integrability of w_i.) With f := θ: ∫⁻_{A_i} |w_i| dλ = ∫⁻_{A_i} θ(G_i u) du ≤ ofReal(m_i)⁻ⁿ∫⁻_{G_i(A_i)} θ dHⁿ ≤ ofReal(m_i)⁻ⁿ∫⁻_M θ dHⁿ = ofReal(m_i)⁻ⁿR.measure(ℝ^P) < ∞. As w_i is measurable, it is integrable on A_i.
7. (Mass sum.) For each i the sibling area_lintegral, part (ii) (f := G_i, s := A_i: Borel, G_i differentiable with injective derivative on A_i and injective on A_i; g := θ), gives ∫⁻_{A_i} ofReal(|w_i|c_i) dλ = ∫⁻_{A_i} ofReal(J_i(u))·θ(G_i u) du = ∫⁻_{G_i(A_i)} θ dHⁿ. The G_i(A_i) are Borel, pairwise disjoint and contained in M, so Σ_i ∫⁻_{G_i(A_i)} θ dHⁿ = ∫⁻_{⋃_i G_i(A_i)} θ dHⁿ (lintegral_iUnion) ≤ ∫⁻_M θ dHⁿ = R.measure(ℝ^P) (R.measure = (Hⁿ⌞M).withDensity θ).
8. (Representation.) Let η be a continuous n-form with compact support; C := sup_y |η(y)| < ∞ (covectorEuclideanNorm is continuous, being the square root of a finite sum of squares of evaluations). Put f(x) := θ(x)·ξ(x)(η(x)).
(a) f is integrable on M for Hⁿ: it is a.e. strongly measurable (θ measurable, ξ a.e. strongly measurable for Hⁿ⌞M, η continuous, the pairing (ζ, α) ↦ ζ(α) continuous bilinear), and by (IMC)(d) |f(x)| ≤ θ(x)|η(x)| ≤ C·θ(x) for Hⁿ-a.e. x ∈ M, while ∫_M θ dHⁿ < ∞.
(b) hasSum_integral_iUnion for the disjoint Borel sets G_i(A_i) (f integrable on their union ⊆ M) gives HasSum (i ↦ ∫_{G_i(A_i)} f dHⁿ) (∫_{⋃_i G_i(A_i)} f dHⁿ). Since ⋃_i G_i(A_i) ⊆ M and Hⁿ(M ∖ ⋃_i G_i(A_i)) = 0, these sets are Hⁿ-a.e. equal, so the sum is ∫_M f dHⁿ = R.action(η).
(c) For each i the sibling area_integral (G := G_i, F := A_i, h := f) gives ∫_{G_i(A_i)} f dHⁿ = ∫_{A_i} J_i(u)f(G_i u) du = ∫_{A_i} θ(G_i u)·[J_i(u)ξ(G_i u)(η(G_i u))] du. By step 2 with α := η(G_i u), for λ-a.e. u ∈ A_i the bracket equals s_i(u)·η(G_i u)(v_i(u)). Hence (setIntegral_congr_ae) ∫_{G_i(A_i)} f dHⁿ = ∫_{A_i} w_i(u)·η(G_i u)(v_i(u)) du.
(d) (b) and (c) give HasSum (i ↦ ∫_{A_i} w_i(u)η(G_i u)(DG_i(u)e) du) (R.action(η)).
9. The remaining clauses (G_i Lipschitz, A_i Borel, G_i differentiable on A_i, G_i(A_i) ⊆ M) are part of step 1. ∎

## Key steps

1. (B1) decomposes M into disjoint bi-Lipschitz images G_i(A_i) up to an Hⁿ-null set.
2. piece_sign gives measurable signs s_i with J_iξ∘G_i = s_i·ev_{DG_i e} a.e. on A_i; set w_i := θ∘G_i·s_i ∈ ℤ and c_i := J_i.
3. (GB) gives |α(DG_i e)| ≤ c_i|α|; bilip_measure gives ∫_{A_i}|w_i| ≤ m_i⁻ⁿ∫_Mθ < ∞.
4. area_lintegral: Σ_i∫_{A_i}|w_i|c_i = Σ_i∫_{G_i(A_i)}θ ≤ R.measure(ℝ^P).
5. (IMC)(d) makes θξ(η) integrable; countable additivity over G_i(A_i), area_integral and the sign identity give HasSum (∫_{A_i} w_i η(G_i)(DG_i e)) (R.action η).

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in the workspace (b4d606db1da5…) and in SNAPSHOT/mathlib (25730c7c…); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `python3 scans of RUN/dag.json: the selected node, its depends_on and their statuses; accepted lean_statements containing IsUnitOrientationOf, Pairwise/bi-Lipschitz pieces, area formulas, IMRep constructors, R.action with HasSum, carrier ⊆ support; lean_name prefix dimred_mbl_dt_lpip (no node)`
- `python3/cat of twin and parent decompositions: nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9bda5f8762/decomposition-v1.json (cmcdt_lp_integer_multiplicity), nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-3cd71b3c6f/decomposition-v1.json (dor_lmb_fcd_im_pushforward), nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a2fdfc1c6f/decomposition-v1.json, and the parent-child-handoff.json of the six reused nodes`
- `rg -c dimred_mbl_dt_lpip SNAPSHOT/project lake-packages-25730c7c/simongmt/Poincare -g '*.lean' (no match)`
- `grep -n in SNAPSHOT/mathlib and lake-packages-25730c7c/mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (MeasureTheory/Function/Jacobian.lean:255), hausdorffMeasure_image_le (MeasureTheory/Measure/Hausdorff.lean:733,745), euclideanHausdorffMeasure_def and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean), tendsto_tsum_of_dominated_convergence (Analysis/Normed/Group/Tannery.lean:45; imported only by NumberTheory/LSeries/Injectivity and Analysis/Normed/Ring/InfiniteProd), LinearMap.exists_antilipschitzWith and isOpen_setOfPred_linearIndependent (Analysis/Normed/Module/FiniteDimension.lean), nullMeasurableSet_eq_fun (MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:575), LinearMap.normDet API (Analysis/InnerProductSpace/NormDet.lean), grep -i hadamard (no Gram Hadamard inequality)`
- `grep -n in SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, countablyRectifiable_range, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique) and Chapter06/Forms.lean, Currents.lean, Mass.lean, CurrentLocalEquality.lean (Covector, DifferentialForm, IsTestForm, TestFormOn, GeometricCurrentOn, GeometricCurrentOn.ext, covectorEuclideanNorm, massAdmissibleOn, massOn, mass, zeroRegion, isOpen_zeroRegion, support)`
- `lake env lean /tmp/imp_decomp/lean/Avail.lean and Avail2.lean: #check of the cited Mathlib/SimonGMT names after import GMT.Ch07.Submission (all present except tendsto_tsum_of_dominated_convergence, Matrix.gram, LinearMap.normDet and ContinuousAlternatingMap.map_linearDependent; AlternatingMap.map_linearDependent is present)`
- `lake env lean /tmp/imp_decomp/lean/Types.lean (the 12 child types in the comparator challenge scope: only sorry warnings); python3 -I validate_lean_statement of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py and of verifier/lean_contract.py on all 12; verifier gmt-compare.py contract_scope replay`
- `lake env lean /tmp/imp_decomp/lean/Skeleton.lean (exact selected type from the exact child and dependency types, sorry only in analytic steps), /tmp/imp_decomp/lean/BilipProof.lean (bilip_measure proved, no sorry), /tmp/imp_decomp/lean/ChainCheck.lean (chain-rule identity and CB/c-bound domination)`
- `git show <candidate>:GMT/Ch07/Submission.lean | grep ^import for accepted candidates a2ba78fca3, 98617b4294, d5ba41d68f, 15f8046553, c2cf4bd9, 6ae39d3e62 (accepted solutions may add imports such as Poincare.SimonGMT.Chapter02.AreaLipschitz)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-c8ea2217cb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-a2fdfc1c6f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9bda5f8762/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-3cd71b3c6f/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-64a6473a66/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-db95546c3f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-dad7016689/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-828dc69c10/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-4d6ef43151/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/imp_decomp/lean/Types.lean`
- `/tmp/imp_decomp/lean/Skeleton.lean`
- `/tmp/imp_decomp/lean/BilipProof.lean`
- `/tmp/imp_decomp/lean/ChainCheck.lean`
- `/tmp/imp_decomp/lean/Avail.lean`
- `/tmp/imp_decomp/lean/Avail2.lean`

Pins match: project b4d606db, Mathlib 25730c7c, and the workspace Submission is byte-identical to the snapshot contract. The snapshot, SimonGMT and Mathlib contain no lemma for this node's obligations: Lipschitz push-forward integrality, parametric piece representation, orientation sign along pieces, or the two-sided bi-Lipschitz Hausdorff comparison. Six accepted DAG declarations have exactly the needed types and are reused byte-identically: ptd_piece_image_approxTangent_ae, codim1_lura_gram_area_formula, codim1_lur_cd_injective_area_formula_gram, codim1_lur_normalized_wedge_orientation, rsdic_unitOrientation_eq_or_eq_neg and dtc_bc_lc_sl_sf_imrep_of_subset. The analogous twin children (cmcdt_lpi_*, dor_lmb_fcd_imp_*) are unaccepted, so six fresh names dimred_mbl_dt_lpip_* are used. Every cited Mathlib/SimonGMT lemma exists in the pinned snapshot. All of them are in the frozen import closure except Tannery's tendsto_tsum_of_dominated_convergence, which the parent must import (as accepted solutions already import extra modules) or prove inline. All 12 types elaborate in the comparator scope and pass both validators. A Lean skeleton derives the selected type from the children and the parent's dependencies, and bilip_measure is fully proved.
