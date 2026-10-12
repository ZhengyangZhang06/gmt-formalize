# Parent-supplied natural-language proof

- Parent DAG node: `root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1`
- Child DAG node: `root.first_rectifiability-a1.hausdorff_null_of_weight_null-a1.unit_ball_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this is the normalisation identity used in Step 4 of the supplied parent proof, unitBallVolume n = realUnitBallVolume n. Here SimonGMT Chapter01.realUnitBallVolume m := ENNReal.ofReal (π^{m/2}/Γ(m/2+1)) (Chapter01/Hausdorff.lean:34), with defining equation realUnitBallVolume_eq (:38). The supplied proof took the identity from SimonGMT volume_euclidean_ball_eq (Chapter01/EuclideanHausdorffUpper.lean:71). That lemma needs n > 0, which is why the supplied proof treated n = 0 separately, and it lies outside the import closure of GMT.Ch08.Submission. Here the identity is proved for every n ∈ ℕ from Mathlib facts inside that closure; the contract imports Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls.

Notation: E_n := EuclideanSpace ℝ (Fin n) with its volume. By definition, unitBallVolume n = volume (ball (0 : E_n) 1). Throughout, n/2 denotes the real number (n:ℝ)/2, and π^{n/2} is the real power Real.pi ^ ((n:ℝ)/2).

1. Case n = 0. The index type Fin 0 is empty. By Mathlib volume_euclideanSpace_eq_dirac (MeasureTheory/Measure/Haar/InnerProductSpace.lean:142, hypothesis [IsEmpty ι]), the volume of E_0 is the Dirac measure at 0. Since 1 > 0 we have 0 ∈ ball 0 1 (mem_ball_self), so unitBallVolume 0 = dirac 0 (ball 0 1) = 1 (Measure.dirac_apply_of_mem). On the right-hand side, (0:ℝ)/2 = 0, so π^0 = 1, and Γ(0 + 1) = Γ(1) = 1. The right side is therefore ENNReal.ofReal (1/1) = ENNReal.ofReal 1 = 1, and both sides equal 1.

2. Case n ≥ 1, the ball formula. Fin n is nonempty, since it contains 0 when 0 < n. Apply Mathlib EuclideanSpace.volume_ball (MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:307, hypotheses [Nonempty ι] [Fintype ι]) with ι := Fin n, centre 0 and radius 1:
volume (ball 0 1) = ENNReal.ofReal(1)^{card (Fin n)} · ENNReal.ofReal(√π^{card (Fin n)} / Γ(card (Fin n)/2 + 1)).
Here card (Fin n) = n (Fintype.card_fin), ENNReal.ofReal 1 = 1 and 1^n = 1. Hence unitBallVolume n = ENNReal.ofReal(√π^n / Γ((n:ℝ)/2 + 1)).

3. Case n ≥ 1, the power identity √π^n = π^{(n:ℝ)/2}.
- √π = π^{1/2} (Real.sqrt_eq_rpow, Analysis/SpecialFunctions/Pow/Real.lean:989).
- (π^{1/2})^n = (π^{1/2})^{(n:ℝ)} (Real.rpow_natCast, Pow/Real.lean:61, read right to left).
- Since π ≥ 0, (π^{1/2})^{(n:ℝ)} = π^{(1/2)·n} (Real.rpow_mul, Pow/Real.lean:414, read right to left).
- (1/2)·n = (n:ℝ)/2 by ring arithmetic.
Substituting into Step 2 gives unitBallVolume n = ENNReal.ofReal(π^{(n:ℝ)/2} / Γ((n:ℝ)/2 + 1)), which is the claim. ∎

## Key steps

1. n = 0: the volume of EuclideanSpace ℝ (Fin 0) is dirac 0 (volume_euclideanSpace_eq_dirac), so ω_0 = 1 = ofReal(π^0/Γ(1)).
2. n ≥ 1: EuclideanSpace.volume_ball at centre 0 and radius 1, with card (Fin n) = n and ofReal 1 = 1, gives ω_n = ofReal(√π^n/Γ(n/2+1)).
3. √π^n = π^{n/2} by Real.sqrt_eq_rpow, Real.rpow_natCast and Real.rpow_mul (π ≥ 0), which gives the claim.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'theorem addHaar_closedBall ' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean (line 500, no Nontrivial hypothesis)`
- `rg -n 'of_pseudoMetrizableSpace_of_isFiniteMeasure|exists_isOpen_lt_of_lt' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean (1072; 359)`
- `sed -n 925,955p mathlib/Mathlib/Topology/Bases.lean (isOpen_iUnion_countable 932, isOpen_biUnion_countable 942)`
- `rg -n 'theorem exists_pos_sum_of_countable|theorem exists_inv_nat_lt|theorem le_toOuterMeasure_caratheodory' mathlib/Mathlib (SpecificLimits/Basic.lean:642, Basic/ENNReal/Inv.lean:650, MeasureTheory/Measure/OuterMeasure.lean:37)`
- `grep -n 'theorem volume_ball' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean (EuclideanSpace.volume_ball 307 with [Nonempty ι]); grep -n volume_euclideanSpace_eq_dirac mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean (142)`
- `grep -n 'sqrt_eq_rpow|rpow_natCast|rpow_mul' mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean (989; 61; 414)`
- `rg -n 'restrict_apply|restrict_apply'' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean (75; 111); isFiniteMeasure_restrict Typeclasses/Finite.lean:40; limsup_congr Order/LiminfLimsup.lean:201`
- `grep -n '^theorem' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean (no density-vs-Hausdorff comparison theorem in Mathlib)`
- `grep -n in simongmt Chapter01/DensityComparison.lean (mul_simonHausdorff_le_of_le_dimensionalUpperDensity 251), Chapter01/Densities.lean (dimensionalDensityQuotient 39, dimensionalUpperDensity 44, volume_closedBall_eq_densityNormalization 515), Chapter01/Hausdorff.lean (realUnitBallVolume 34, realUnitBallVolume_eq 38, simonHausdorffMeasureReal_toOuterMeasure 445), Chapter02/AreaLiteral.lean (simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure 42), Chapter01/EuclideanHausdorffUpper.lean (volume_euclidean_ball_eq 71 needs 0 < n; realUnitBallVolume_nat_eq 54), Chapter08/Varifold.lean (abbrev Euclidean 54)`
- `python import-closure walk from the contract's SimonGMT imports (22 Poincare modules; includes Chapter01.Hausdorff, excludes Chapter01.Densities/DensityComparison/EuclideanNormalization/EuclideanHausdorffUpper and Chapter02.AreaLiteral)`
- `git show fb766d9 (ch08 leaf dropped a speculative import); ch04 git log -G'^import' -- GMT/Ch04/Submission.lean (38ba3ce draft adds AreaLipschitz, accepted non-leaf candidate 17dc1f6 per accepted-candidate.json)`
- `lake env lean /tmp/hnw-scratch-7f3a/Full.lean (first variant incl. Simon 3.3 bridge as child; standard axioms)`
- `lake env lean /tmp/hnw-scratch-7f3a/NoImp.lean (both final children fully proved with only import GMT.Ch08.Submission; #print axioms = propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/hnw-scratch-7f3a/Assembly.lean (adds DensityComparison + AreaLiteral imports; both children + parent frt_hausdorff_null_of_weight_null with exact frozen type; no sorry; standard axioms)`
- `lake env lean /tmp/hnw-scratch-7f3a/Ch_B.lean and Ch_C.lean (comparator NodeChallenge form from gmt-compare.py contract_scope replay)`
- `lean_contract.validate_lean_statement on both child statements (pass)`
- `python3 collision check of frt_hnw_* names against dag.json lean_name values, nodes/*/decomposition*.json subproblems and git grep over all refs (no hits)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-hausdorff-null-of-weight-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-hausdorff-null-of-weight-null-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`

The snapshot is project 63436ae6 with Mathlib 25730c7c.

What the supplied proof needs, and where it lives:
- Its SimonGMT ingredients are mul_simonHausdorff_le_of_le_dimensionalUpperDensity (DensityComparison.lean:251) and simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure (AreaLiteral.lean:42). Both exist and use standard axioms, but they lie outside the import closure of GMT.Ch08.Submission. That closure has SimonGMT Chapter01.Hausdorff (realUnitBallVolume_eq:38, simonHausdorffMeasureReal_toOuterMeasure:445) but not Densities, DensityComparison, EuclideanHausdorffUpper or AreaLiteral.
- Mathlib has no density-vs-Hausdorff comparison (Hausdorff.lean theorem list), so this step has to come from SimonGMT.
- Leaves keep their base imports (fb766d9). A decomposed node's draft may add imports (ch04 38ba3ce/17dc1f6).
- So the comparison goes in this node's assembly, and the children use only in-closure facts.

In-closure facts used by the children:
- Mathlib addHaar_closedBall (EqHaar.lean:500), EuclideanSpace.volume_ball (VolumeOfBalls.lean:307, needs Nonempty ι) and volume_euclideanSpace_eq_dirac (Haar/InnerProductSpace.lean:142).
- Real.sqrt_eq_rpow, rpow_natCast and rpow_mul (Pow/Real.lean:989/61/414).
- isOpen_biUnion_countable (Bases.lean:942), ENNReal.exists_pos_sum_of_countable (SpecificLimits/Basic.lean:642), WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure (Regular.lean:1072) and Set.exists_isOpen_lt_of_lt (Regular.lean:359).
- Measure.restrict_apply / restrict_apply' (Restrict.lean:75/111).

Machine checks:
- Both children are proved with only import GMT.Ch08.Submission.
- The parent assembly, with the two added imports, proves the exact frozen type with no sorry and axioms propext, Classical.choice, Quot.sound.
- The NodeChallenge files elaborate and both statements pass validate_lean_statement.
- No name collides with the DAG, any proposal or any git ref.
