# Parent-supplied natural-language proof

- Parent DAG node: `root.de_giorgi-a1.blowup_halfspace-a1`
- Child DAG node: `root.de_giorgi-a1.blowup_halfspace-a1.blowup_image_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Selected-node proof, Step 2(c) ("η_r maps E ∩ B_{rR}(x) onto E_r ∩ B_R(0) and B_{rR}(x) ∖ E onto B_R(0) ∖ E_r (η_r is a bijection with η_r(B_{rR}(x)) = B_R(0)), and multiplies L^N by r^{−N}") and Step 3 ("F_k is null-measurable, being the image of the null-measurable E under the affine homeomorphism η_{r_k}, which maps L^N-null sets to L^N-null sets and Borel sets to Borel sets"); this is the change of variables x ↦ ρ_k x of Simon, Ch. 3, proof of Theorem 4.3, display (8) (chapter-03.txt lines 662-667), done for a general centre x. No sibling child is used.

Notation. L^N := volume on ℝ^N = Rn N (finrank ℝ ℝ^N = N); B_ρ(z) is the open ball; η := blowUpMap x r, η(y) = r⁻¹·(y − x); in Lean r⁻¹ = 0 when r = 0.

1. (Factorisation.) η is the translation T(y) := y − x followed by the dilation z ↦ r⁻¹z. Hence η(A) = r⁻¹·T(A), and T(A) = {y − x : y ∈ A} = {z : z + x ∈ A} is the preimage τ⁻¹(A) of A under the translation τ(z) := z + x.

2. (Two invariance properties of L^N, valid for arbitrary sets, i.e. for the outer measure.) (a) Translation invariance: L^N(τ⁻¹(S)) = L^N(S) for every S ⊆ ℝ^N. (b) Scaling: L^N(c·S) = |c^N|·L^N(S) for every S ⊆ ℝ^N and c ∈ ℝ. This is the behaviour of the Haar measure L^N under the linear map z ↦ cz of determinant c^N (Mathlib addHaar_smul). It includes c = 0: for N ≥ 1, 0·S ⊆ {0} is null; for N = 0, ℝ^0 is a point and |c^0| = 1.

3. (Null-measurability, any r.) Let A be L^N-null-measurable. The translation τ is measurable and, by 2(a), measure-preserving, so it is quasi-measure-preserving; the preimage T(A) = τ⁻¹(A) of a null-measurable set under such a map is null-measurable. Put S := T(A) and c := r⁻¹, so η(A) = c·S. If c = 0 then c·S is ∅ or {0}, both measurable. If c ≠ 0, choose a measurable M with L^N(S Δ M) = 0. Then c·M is measurable, because z ↦ cz is a homeomorphism and so maps Borel sets to Borel sets. Moreover c·S Δ c·M = c·(S Δ M), since z ↦ cz is a bijection, and this set has measure |c^N|·0 = 0 by 2(b). Hence η(A) = c·S is null-measurable (Mathlib NullMeasurableSet.const_smul), for every r ∈ ℝ.

4. (Volume scaling, r > 0.) By 2(b) with c = r⁻¹ > 0, where |c^N| = (r^N)⁻¹, and by 2(a): L^N(η(A)) = (r^N)⁻¹·L^N(T(A)) = (r^N)⁻¹·L^N(A) for an arbitrary A, i.e. volume (η '' A) = ENNReal.ofReal ((r^N)⁻¹) * volume A.

5. (η maps B_{rR}(x) onto B_R(0), r > 0.) For y ∈ ℝ^N, |η(y)| = r⁻¹|y − x|. So if y ∈ B_{rR}(x), i.e. |y − x| < rR, then |η(y)| < R and η(y) ∈ B_R(0). Conversely, for z ∈ B_R(0) put y := x + r·z; then |y − x| = r|z| < rR and η(y) = r⁻¹·(r·z) = z. Hence η(B_{rR}(x)) = B_R(0); both sides are empty when R ≤ 0.

6. (Injectivity, r ≠ 0.) If η(y) = η(y') then r⁻¹·(y − y') = 0, so y = y' since r⁻¹ ≠ 0.

7. (Ball identities.) Images under an injective map commute with intersections and differences: η(A ∩ B) = η(A) ∩ η(B) and η(B ∖ A) = η(B) ∖ η(A). Take B := B_{rR}(x) and use step 5: η(A ∩ B_{rR}(x)) = η(A) ∩ B_R(0) and η(B_{rR}(x) ∖ A) = B_R(0) ∖ η(A).

8. Step 3 is assertion (i); steps 4 and 7 are assertion (ii). ∎

## Key steps

1. Factor η = (z ↦ r⁻¹z) ∘ (y ↦ y − x), so η(A) = r⁻¹·τ⁻¹(A) with τ(z) = z + x.
2. L^N is translation invariant and satisfies L^N(c·S) = |c^N|L^N(S) for every set S and every c ∈ ℝ.
3. Null-measurability: τ is measure-preserving, so τ⁻¹(A) is null-measurable; dilation by any scalar, including 0, preserves null-measurability.
4. Volume: with c = r⁻¹ > 0, L^N(η(A)) = (r^N)⁻¹L^N(A) for every A.
5. η(B_{rR}(x)) = B_R(0) via |η(y)| = r⁻¹|y − x| and the inverse z ↦ x + rz. η is injective, so images commute with ∩ and ∖, which gives both ball identities.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean`
- `rg -n "theorem tendsto_of_subseq_tendsto|theorem addHaar_image_homothety|theorem addHaar_smul|theorem addHaar_preimage_smul|theorem addHaar_image_continuousLinearEquiv|theorem integral_indicator₀|theorem setIntegral_union" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem HasCompactSupport.fderiv_apply" <snapshot>/mathlib/Mathlib; rg -n "mul_le_mul_left'|theorem mul_le_mul_right|zero_le" <snapshot>/mathlib/Mathlib/Algebra/Order`
- `rg -n "theorem trace_smulRight|trace_smulRight" <snapshot>/mathlib/Mathlib`
- `rg -n "symmDiff" <snapshot>/mathlib/Mathlib/MeasureTheory/Integral; rg -n "theorem tendsto_measure_symmDiff|measure_symmDiff_le" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem [A-Za-z_']*blowUp|lemma [A-Za-z_']*blowUp" .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n "volume \(blowUpMap" .lake/packages/simongmt/Poincare/SimonGMT; rg -n "euclideanDivergence_smul|smulRight" .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `rg -n "^theorem|^lemma|^def" .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `python3 -I dag.json scan: lean_statements containing blowUpMap/symmDiff; lean_name collision check (152 nodes, also case-insensitive)`
- `python3 -I (importlib of verifier/gmt-compare.py) contract_scope + child_modules(contract mode) -> GMT/Scratch/BHS_Challenge_<key>.lean; lake env lean on BHS_Challenge_*.lean, BHS_Proof_*.lean, BHS_FullCheck.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/FinitePerimeter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-blowup-halfspace-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-chart-tangent-differential-a1-chart-blowup-tangent-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_FullCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_image_volume.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_l1loc_transfer.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_perimeter_bound.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/BHS_Proof_blowup_flatness.lean`

The snapshot contract is byte-identical to the workspace contract (project d09bc8a, Mathlib 25730c7c). No Mathlib, SimonGMT or accepted-DAG declaration states any of the four children. Mathlib supplies only ingredients: addHaar_smul, NullMeasurableSet.const_smul, measure_preimage_add_right, integral_indicator₀, LinearMap.trace_smulRight (Trace.lean:272), HasCompactSupport.fderiv_apply (𝕜 explicit), measure_symmDiff_le, and tendsto_of_subseq_tendsto (CountablyGenerated.lean:125), which handles Step 6 directly. SimonGMT has blowUpMap (Rectifiable.lean) and euclideanDivergence/euclideanDivergence_eq_sum_inner (BV.lean). Its blow-up scaling lemmas are for μHE[n] and closed balls, in Chapter04 (not imported by Submission). FinitePerimeter.lean has definitions only. The rg searches for a Lebesgue-volume blow-up lemma, a divergence-of-ζv lemma and a set-integral/symmDiff transfer lemma found nothing. The accepted DAG nodes setIntegral_blowUpMap_image and chartTD_setIntegral_blowUpMap_image are μHE[n] identities with different types. All four child types elaborate in the exact NodeChallenge scope, and their full proofs compile with only propext, Classical.choice and Quot.sound. The selected-node assembly compiles against the frozen sibling types. No proposed lean_name collides with dag.json.
