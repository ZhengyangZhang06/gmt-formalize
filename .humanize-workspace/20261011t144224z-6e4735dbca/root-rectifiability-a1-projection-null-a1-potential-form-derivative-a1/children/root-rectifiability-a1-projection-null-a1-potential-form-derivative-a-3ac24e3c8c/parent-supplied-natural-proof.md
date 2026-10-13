# Parent-supplied natural-language proof

- Parent DAG node: `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1.wedge_cons_linear-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 of the parent proof (linearity in the first slot), with the details filled in.

Notation. Alt := ContinuousAlternatingMap.alternatizeUncurryFin. It sends a continuous linear map F : ℝ^P →L Covector(ℝ^P, m) to an (m+1)-covector. Fix β : Fin m → (ℝ^P)^*. Put θ := wedgeCovectors m β, an m-covector that does not depend on γ. For γ ∈ (ℝ^P)^*, γ.smulRight θ is the continuous linear map v ↦ γ(v)•θ.

1. Unfolding the definition. SimonGMT defines, for every α : Fin (m+1) → (ℝ^P)^*,
 wedgeCovectors (m+1) α = Alt((α 0).smulRight (wedgeCovectors m (Fin.tail α))).
 Take α := Fin.cons γ β. Then α 0 = γ (Fin.cons_zero) and Fin.tail α = β (Fin.tail_cons). Hence, for every γ ∈ (ℝ^P)^*,
 wedgeCovectors (m+1) (Fin.cons γ β) = Alt(γ.smulRight θ).   (∗)

2. smulRight is linear in its first argument. Let γ, δ ∈ (ℝ^P)^* and c ∈ ℝ. For every v ∈ ℝ^P and w : Fin m → ℝ^P:
 - ((γ+δ).smulRight θ)(v)(w) = (γ(v)+δ(v))·θ(w) = γ(v)·θ(w) + δ(v)·θ(w) = (γ.smulRight θ + δ.smulRight θ)(v)(w), by add_smul;
 - ((c•γ).smulRight θ)(v)(w) = (c·γ(v))·θ(w) = c·(γ(v)·θ(w)) = (c•(γ.smulRight θ))(v)(w), by mul_smul.
 Continuous linear maps and continuous alternating maps are determined by their values (ext). Therefore (γ+δ).smulRight θ = γ.smulRight θ + δ.smulRight θ and (c•γ).smulRight θ = c•(γ.smulRight θ).

3. Alt is linear. For all F, G and c ∈ ℝ, Alt(F+G) = Alt F + Alt G and Alt(c•F) = c•Alt F. These are Mathlib ContinuousAlternatingMap.alternatizeUncurryFin_add and alternatizeUncurryFin_smul; Alt is the continuous linear map alternatizeUncurryFinCLM.

4. Additivity. By (∗), Step 2 and Step 3,
 wedgeCovectors (m+1) (Fin.cons (γ+δ) β) = Alt((γ+δ).smulRight θ) = Alt(γ.smulRight θ + δ.smulRight θ) = Alt(γ.smulRight θ) + Alt(δ.smulRight θ) = wedgeCovectors (m+1) (Fin.cons γ β) + wedgeCovectors (m+1) (Fin.cons δ β).

5. Homogeneity. By (∗), Step 2 and Step 3,
 wedgeCovectors (m+1) (Fin.cons (c•γ) β) = Alt((c•γ).smulRight θ) = Alt(c•(γ.smulRight θ)) = c•Alt(γ.smulRight θ) = c•wedgeCovectors (m+1) (Fin.cons γ β).

6. Steps 4 and 5 are exactly the two fields map_add and map_smul of IsLinearMap ℝ for the map γ ↦ wedgeCovectors (m+1) (Fin.cons γ β). This proves the claim. ∎

## Key steps

1. Unfold the definition: wedgeCovectors (m+1) (Fin.cons γ β) = Alt(γ.smulRight (wedgeCovectors m β)), using Fin.cons_zero and Fin.tail_cons.
2. γ ↦ γ.smulRight θ is additive and homogeneous (ext; add_smul, mul_smul).
3. Alt = alternatizeUncurryFin is additive and homogeneous (alternatizeUncurryFin_add, alternatizeUncurryFin_smul).
4. Composing the two gives map_add and map_smul, i.e. IsLinearMap ℝ.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c95; mathlib_commit 25730c7c)`
- `rg -n 'abbrev Eucl|^theorem main_theorem|^namespace|^open' project/GMT/Ch06/Contract.lean (snapshot)`
- `rg -n '^noncomputable def extDeriv |theorem sign_cycleRange|theorem cycleRange_symm_zero|theorem cycleRange_symm_succ|theorem det_permute \(|theorem det_zero_of_row_eq|lemma exists_succAbove_eq \{|theorem sign_symm \(|lemma alternatizeUncurryFinCLM_apply|theorem alternatizeUncurryFin_add \(|theorem alternatizeUncurryFin_smul \{|theorem HasFDerivAt.sum \(|theorem HasFDerivAt.smul_const \(|theorem HasFDerivAt.const_mul \(|theorem HasFDerivAt.mul \(|theorem basisFun_apply|theorem basisFun_repr|abbrev EuclideanSpace.proj ' on the snapshot's mathlib/Mathlib files listed`
- `rg -ln 'def wedgeCovectors' in the snapshot (no match: SimonGMT is not in the snapshot; used the pinned lake package instead)`
- `grep -n 'wedgeCovectors' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `grep -n 'Covector|DifferentialForm|exteriorDerivative' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3 scan of dag.json lean_statements for wedgeCovectors/extDeriv/alternatizeUncurryFin/Fin.cons/succAbove/cycleRange (no accepted node with a reusable identical type)`
- `python3 reserved-name scan of dag.json and nodes/*/decomposition-v*.json (467 names; no collision with rpn_pfd_*)`
- `python3 verifier/lean_contract.py validate_lean_statement on the 4 child statements (all valid)`
- `python3 verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') to replay the child comparator header`
- `lake env lean /tmp/pfd_decomp/T1.lean (glue proves the frozen parent type from the four child types; exit 0)`
- `lake env lean /tmp/pfd_decomp/T2.lean, T3.lean (child proofs; fixed coe_zero and explicit smul_const argument)`
- `lake env lean /tmp/pfd_decomp/EndToEnd.lean (4 children + glue + comparator challenge/solution forms; #print axioms = [propext, Classical.choice, Quot.sound]; exit 0)`
- `python3 read of nodes/root-rectifiability-a1-projection-null-a1*/decomposition-v*.json and decomposition-audit-v3.json (sibling split precedents)`

Files inspected:
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Sign.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/SuccPred.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a1/parent-child-handoff.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1/decomposition-audit-v3.json`
- `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1/decomposition-v1.json`
- `/tmp/pfd_decomp/T1.lean`
- `/tmp/pfd_decomp/EndToEnd.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Mathlib defines extDeriv ω x := alternatizeUncurryFin (fderiv ω x) (DifferentialForm/Basic.lean:72).

Lemmas the children use, all present in the snapshot:
- signs: Fin.sign_cycleRange, cycleRange_symm_zero, cycleRange_symm_succ (Perm/Fin.lean:225,258,262); Equiv.Perm.sign_symm (Perm/Sign.lean:385);
- determinants: Matrix.det_permute, det_zero_of_row_eq (Determinant/Basic.lean:216,373);
- Fin.exists_succAbove_eq (Data/Fin/SuccPred.lean:661);
- linearity of Alt: alternatizeUncurryFinCLM_apply, alternatizeUncurryFin_add, alternatizeUncurryFin_smul (Alternating/Uncurry/Fin.lean:129,149,160);
- calculus: HasFDerivAt.sum, smul_const, mul, const_mul (FDeriv/Add.lean:418; FDeriv/Mul.lean:126,205,352);
- coordinates: EuclideanSpace.proj, basisFun_apply, basisFun_repr (PiL2.lean:285,806,810).

SimonGMT is absent from the snapshot (no match). In the pinned simongmt package, FormsDuality.lean:115 defines wedgeCovectors (n+1) α = alternatizeUncurryFin ((α 0).smulRight (wedgeCovectors n (Fin.tail α))), and :127 proves wedgeCovectors_apply_det.

No accepted DAG node has an identical reusable type, so all four children are new. Each child type elaborates in the replayed comparator scope. All four children and the parent glue are proved end to end with only propext, Classical.choice and Quot.sound.
