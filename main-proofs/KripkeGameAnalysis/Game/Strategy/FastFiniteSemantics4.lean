import KripkeGameAnalysis.Game.Basic
import KripkeGameAnalysis.ModalLogic.FiniteSemantics
import KripkeGameAnalysis.Game.Strategy.gen.ValuationTruthTables
import Init.Data.BitVec.Lemmas
import Mathlib.Tactic.FinCases

namespace KripkeGameStrategy

abbrev ValuationIndex := Fin 65536
abbrev ValuationTruthTable := BitVec 65536

def valuationBitIndex : KripkeGameVars → Fin 4 → Fin 16
  | KripkeGameVars.p, world => ⟨world.1, by omega⟩
  | KripkeGameVars.q, world => ⟨4 + world.1, by omega⟩
  | KripkeGameVars.r, world => ⟨8 + world.1, by omega⟩
  | KripkeGameVars.s, world => ⟨12 + world.1, by omega⟩

def decodeValuation (frame : FiniteKripkeFrame 4) (idx : ValuationIndex) : frame.FiniteValuation KripkeGameVars :=
  fun var world => (BitVec.ofFin (w := 16) idx)[valuationBitIndex var world]

private def encodeValuationBits {frame : FiniteKripkeFrame 4} (val : frame.FiniteValuation KripkeGameVars) : BitVec 16 :=
  BitVec.ofBoolListLE [
    val KripkeGameVars.p 0, val KripkeGameVars.p 1, val KripkeGameVars.p 2, val KripkeGameVars.p 3,
    val KripkeGameVars.q 0, val KripkeGameVars.q 1, val KripkeGameVars.q 2, val KripkeGameVars.q 3,
    val KripkeGameVars.r 0, val KripkeGameVars.r 1, val KripkeGameVars.r 2, val KripkeGameVars.r 3,
    val KripkeGameVars.s 0, val KripkeGameVars.s 1, val KripkeGameVars.s 2, val KripkeGameVars.s 3
  ]

private def encodeValuation {frame : FiniteKripkeFrame 4} (val : frame.FiniteValuation KripkeGameVars) : ValuationIndex :=
  (encodeValuationBits val).toFin

@[simp] private theorem decode_encodeValuation {frame : FiniteKripkeFrame 4} (val : frame.FiniteValuation KripkeGameVars) :
    decodeValuation frame (encodeValuation val) = val := by
  funext var world
  rw [decodeValuation, encodeValuation, BitVec.ofFin_toFin, encodeValuationBits]
  change (BitVec.ofBoolListLE
      [val KripkeGameVars.p 0, val KripkeGameVars.p 1, val KripkeGameVars.p 2, val KripkeGameVars.p 3,
        val KripkeGameVars.q 0, val KripkeGameVars.q 1, val KripkeGameVars.q 2, val KripkeGameVars.q 3,
        val KripkeGameVars.r 0, val KripkeGameVars.r 1, val KripkeGameVars.r 2, val KripkeGameVars.r 3,
        val KripkeGameVars.s 0, val KripkeGameVars.s 1, val KripkeGameVars.s 2, val KripkeGameVars.s 3]
      ).getLsbD (valuationBitIndex var world).1 = val var world
  rw [BitVec.getLsbD_ofBoolListLE]
  cases var <;> fin_cases world <;> simp [valuationBitIndex]

private theorem satisfiesForAllValuations_eq_decide_forall_decode
    (frame : FiniteKripkeFrame 4)
    (world : frame.vertices)
    (fml : ModalFormula KripkeGameVars) :
    frame.satisfiesForAllValuations world fml =
      decide (∀ idx : ValuationIndex, (decodeValuation frame idx).decideSatisfaction world fml) := by
  unfold FiniteKripkeFrame.satisfiesForAllValuations
  exact Bool.decide_congr <| by
    constructor
    · intro h idx
      exact h _ (FiniteKripkeFrame.allFinValuations_mem frame (decodeValuation frame idx))
    · intro h finval _
      simpa using h (encodeValuation finval)

def valuationTruthTable (var : KripkeGameVars) (world : Fin 4) : ValuationTruthTable :=
  match var, world with
  | KripkeGameVars.p, 0 => Generated.valuationTruthTables[0]
  | KripkeGameVars.p, 1 => Generated.valuationTruthTables[1]
  | KripkeGameVars.p, 2 => Generated.valuationTruthTables[2]
  | KripkeGameVars.p, 3 => Generated.valuationTruthTables[3]
  | KripkeGameVars.q, 0 => Generated.valuationTruthTables[4]
  | KripkeGameVars.q, 1 => Generated.valuationTruthTables[5]
  | KripkeGameVars.q, 2 => Generated.valuationTruthTables[6]
  | KripkeGameVars.q, 3 => Generated.valuationTruthTables[7]
  | KripkeGameVars.r, 0 => Generated.valuationTruthTables[8]
  | KripkeGameVars.r, 1 => Generated.valuationTruthTables[9]
  | KripkeGameVars.r, 2 => Generated.valuationTruthTables[10]
  | KripkeGameVars.r, 3 => Generated.valuationTruthTables[11]
  | KripkeGameVars.s, 0 => Generated.valuationTruthTables[12]
  | KripkeGameVars.s, 1 => Generated.valuationTruthTables[13]
  | KripkeGameVars.s, 2 => Generated.valuationTruthTables[14]
  | KripkeGameVars.s, 3 => Generated.valuationTruthTables[15]

set_option maxRecDepth 1000000 in
@[simp] theorem valuationTruthTable_get (var : KripkeGameVars) (world : Fin 4) (idx : ValuationIndex) :
    (valuationTruthTable var world)[idx] = (decodeValuation (FiniteKripkeFrame.ofFin (n := 4) 0) idx) var world := by
  cases var <;> fin_cases world
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 0 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 1 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 2 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 3 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 4 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 5 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 6 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 7 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 8 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 9 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 10 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 11 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 12 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 13 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 14 idx)
  · simpa [valuationTruthTable, decodeValuation, valuationBitIndex] using
      (Generated.valuationTruthTables_spec 15 idx)

private abbrev allValuationsTrue : ValuationTruthTable := BitVec.allOnes 65536

private def tableAllTrue (table : ValuationTruthTable) : Bool :=
  decide (∀ idx : ValuationIndex, table[idx] = true)

set_option maxRecDepth 1000000 in
@[simp] private theorem getElem_allValuationsTrue (idx : ValuationIndex) :
    allValuationsTrue[idx] = true := by
  exact BitVec.getElem_allOnes idx.1 idx.2

private def evalFormulaTable (frame : FiniteKripkeFrame 4) : ModalFormula KripkeGameVars → Fin 4 → ValuationTruthTable
  | .var var, world =>
      valuationTruthTable var world
  | .neg fml, world =>
      ~~~ evalFormulaTable frame fml world
  | .and left right, world =>
      evalFormulaTable frame left world &&& evalFormulaTable frame right world
  | .box fml, world =>
      (if frame world 0 then evalFormulaTable frame fml 0 else allValuationsTrue) &&&
      (if frame world 1 then evalFormulaTable frame fml 1 else allValuationsTrue) &&&
      (if frame world 2 then evalFormulaTable frame fml 2 else allValuationsTrue) &&&
      (if frame world 3 then evalFormulaTable frame fml 3 else allValuationsTrue)

set_option maxRecDepth 1000000 in
private theorem evalFormulaTable_get
    (frame : FiniteKripkeFrame 4)
    (fml : ModalFormula KripkeGameVars)
    (world : Fin 4)
    (idx : ValuationIndex) :
    (evalFormulaTable frame fml world)[idx] =
      (decodeValuation frame idx).decideSatisfaction world fml := by
  induction fml generalizing world with
  | var var =>
      simpa [evalFormulaTable, KripkeFrame.Valuation.decideSatisfaction] using valuationTruthTable_get var world idx
  | neg fml ih =>
      simpa [evalFormulaTable, KripkeFrame.Valuation.decideSatisfaction] using congrArg (! ·) (ih world)
  | and left right ihLeft ihRight =>
      simpa [evalFormulaTable, KripkeFrame.Valuation.decideSatisfaction] using congrArg₂ Bool.and (ihLeft world) (ihRight world)
  | box fml ih =>
      let b0 := if frame world 0 then (decodeValuation frame idx).decideSatisfaction 0 fml else true
      let b1 := if frame world 1 then (decodeValuation frame idx).decideSatisfaction 1 fml else true
      let b2 := if frame world 2 then (decodeValuation frame idx).decideSatisfaction 2 fml else true
      let b3 := if frame world 3 then (decodeValuation frame idx).decideSatisfaction 3 fml else true
      have h0 : (if frame world 0 then evalFormulaTable frame fml 0 else allValuationsTrue)[idx] = b0 := by
        dsimp [b0]
        by_cases h : frame world 0
        · rw [if_pos h, if_pos h]
          exact ih 0
        · rw [if_neg h, if_neg h]
          exact getElem_allValuationsTrue idx
      have h1 : (if frame world 1 then evalFormulaTable frame fml 1 else allValuationsTrue)[idx] = b1 := by
        dsimp [b1]
        by_cases h : frame world 1
        · rw [if_pos h, if_pos h]
          exact ih 1
        · rw [if_neg h, if_neg h]
          exact getElem_allValuationsTrue idx
      have h2 : (if frame world 2 then evalFormulaTable frame fml 2 else allValuationsTrue)[idx] = b2 := by
        dsimp [b2]
        by_cases h : frame world 2
        · rw [if_pos h, if_pos h]
          exact ih 2
        · rw [if_neg h, if_neg h]
          exact getElem_allValuationsTrue idx
      have h3 : (if frame world 3 then evalFormulaTable frame fml 3 else allValuationsTrue)[idx] = b3 := by
        dsimp [b3]
        by_cases h : frame world 3
        · rw [if_pos h, if_pos h]
          exact ih 3
        · rw [if_neg h, if_neg h]
          exact getElem_allValuationsTrue idx
      have hBits : (evalFormulaTable frame (.box fml) world)[idx] = (((b0 && b1) && b2) && b3) := by
        rw [evalFormulaTable]
        have hOuter :
            ((((if frame world 0 then evalFormulaTable frame fml 0 else allValuationsTrue) &&&
                  (if frame world 1 then evalFormulaTable frame fml 1 else allValuationsTrue)) &&&
                (if frame world 2 then evalFormulaTable frame fml 2 else allValuationsTrue)) &&&
              (if frame world 3 then evalFormulaTable frame fml 3 else allValuationsTrue))[idx] =
              ((((if frame world 0 then evalFormulaTable frame fml 0 else allValuationsTrue) &&&
                    (if frame world 1 then evalFormulaTable frame fml 1 else allValuationsTrue)) &&&
                  (if frame world 2 then evalFormulaTable frame fml 2 else allValuationsTrue))[idx] &&
                (if frame world 3 then evalFormulaTable frame fml 3 else allValuationsTrue)[idx]) := by
          simp
        have hMid :
            (((if frame world 0 then evalFormulaTable frame fml 0 else allValuationsTrue) &&&
                (if frame world 1 then evalFormulaTable frame fml 1 else allValuationsTrue)) &&&
              (if frame world 2 then evalFormulaTable frame fml 2 else allValuationsTrue))[idx] =
              (((if frame world 0 then evalFormulaTable frame fml 0 else allValuationsTrue) &&&
                  (if frame world 1 then evalFormulaTable frame fml 1 else allValuationsTrue))[idx] &&
                (if frame world 2 then evalFormulaTable frame fml 2 else allValuationsTrue)[idx]) := by
          simp
        have hInner :
            ((if frame world 0 then evalFormulaTable frame fml 0 else allValuationsTrue) &&&
              (if frame world 1 then evalFormulaTable frame fml 1 else allValuationsTrue))[idx] =
              ((if frame world 0 then evalFormulaTable frame fml 0 else allValuationsTrue)[idx] &&
                (if frame world 1 then evalFormulaTable frame fml 1 else allValuationsTrue)[idx]) := by
          simp
        rw [hOuter, hMid, hInner]
        rw [h0, h1, h2, h3]
      exact hBits.trans <| by
        dsimp [b0, b1, b2, b3]
        simp only [KripkeFrame.Valuation.decideSatisfaction, KripkeFrame.accessible, Fin.forall_fin_succ,
          Bool.decide_and, Bool.and_assoc]
        simp [FiniteKripkeFrame.asKripkeFrame]

private theorem evalFormulaTable_allValuationsTrue_iff
    (frame : FiniteKripkeFrame 4)
    (fml : ModalFormula KripkeGameVars)
    (world : Fin 4) :
    tableAllTrue (evalFormulaTable frame fml world) = true ↔
      frame.satisfiesForAllValuations world fml = true := by
  rw [tableAllTrue, satisfiesForAllValuations_eq_decide_forall_decode, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h idx
    exact (evalFormulaTable_get frame fml world idx).symm.trans (h idx)
  · intro h idx
    exact (evalFormulaTable_get frame fml world idx).trans (h idx)

abbrev ValuationTruthMask := Nat

private def allValuationsTrueMask : ValuationTruthMask :=
  (BitVec.allOnes 65536).toNat

private theorem allValuationsTrueMask_lt : allValuationsTrueMask < 2 ^ 65536 := by
  simpa [allValuationsTrueMask] using (BitVec.allOnes 65536).isLt

@[simp] private theorem testBit_allValuationsTrueMask (idx : ValuationIndex) :
    Nat.testBit allValuationsTrueMask idx = true := by
  simpa [allValuationsTrueMask] using
    (BitVec.testBit_toNat (x := BitVec.allOnes 65536) (i := idx)).trans (BitVec.getElem_allOnes idx.1 idx.2)

private def valuationTruthMask (var : KripkeGameVars) (world : Fin 4) : ValuationTruthMask :=
  (valuationTruthTable var world).toNat

@[simp] private theorem valuationTruthMask_testBit
    (var : KripkeGameVars)
    (world : Fin 4)
    (idx : ValuationIndex) :
    Nat.testBit (valuationTruthMask var world) idx = (decodeValuation (FiniteKripkeFrame.ofFin (n := 4) 0) idx) var world := by
  simpa [valuationTruthMask] using
    (BitVec.testBit_toNat (x := valuationTruthTable var world) (i := idx)).trans (valuationTruthTable_get var world idx)

private def evalFormulaMask (frame : FiniteKripkeFrame 4) : ModalFormula KripkeGameVars → Fin 4 → ValuationTruthMask
  | .var var, world =>
      valuationTruthMask var world
  | .neg fml, world =>
      allValuationsTrueMask ^^^ evalFormulaMask frame fml world
  | .and left right, world =>
      evalFormulaMask frame left world &&& evalFormulaMask frame right world
  | .box fml, world =>
      (if frame world 0 then evalFormulaMask frame fml 0 else allValuationsTrueMask) &&&
      (if frame world 1 then evalFormulaMask frame fml 1 else allValuationsTrueMask) &&&
      (if frame world 2 then evalFormulaMask frame fml 2 else allValuationsTrueMask) &&&
      (if frame world 3 then evalFormulaMask frame fml 3 else allValuationsTrueMask)

private theorem evalFormulaMask_lt
    (frame : FiniteKripkeFrame 4)
    (fml : ModalFormula KripkeGameVars)
    (world : Fin 4) :
    evalFormulaMask frame fml world < 2 ^ 65536 := by
  induction fml generalizing world with
  | var var =>
      simpa [evalFormulaMask, valuationTruthMask] using (valuationTruthTable var world).isLt
  | neg fml ih =>
      exact Nat.xor_lt_two_pow allValuationsTrueMask_lt (ih world)
  | and left right ihLeft ihRight =>
      exact Nat.and_lt_two_pow (evalFormulaMask frame left world) (ihRight world)
  | box fml ih =>
      have h0 : (if frame world 0 then evalFormulaMask frame fml 0 else allValuationsTrueMask) < 2 ^ 65536 := by
        by_cases h : frame world 0 <;> simp [h, ih 0, allValuationsTrueMask_lt]
      have h1 : (if frame world 1 then evalFormulaMask frame fml 1 else allValuationsTrueMask) < 2 ^ 65536 := by
        by_cases h : frame world 1 <;> simp [h, ih 1, allValuationsTrueMask_lt]
      have h2 : (if frame world 2 then evalFormulaMask frame fml 2 else allValuationsTrueMask) < 2 ^ 65536 := by
        by_cases h : frame world 2 <;> simp [h, ih 2, allValuationsTrueMask_lt]
      have h3 : (if frame world 3 then evalFormulaMask frame fml 3 else allValuationsTrueMask) < 2 ^ 65536 := by
        by_cases h : frame world 3 <;> simp [h, ih 3, allValuationsTrueMask_lt]
      exact Nat.and_lt_two_pow
        (((if frame world 0 then evalFormulaMask frame fml 0 else allValuationsTrueMask) &&&
          (if frame world 1 then evalFormulaMask frame fml 1 else allValuationsTrueMask)) &&&
          (if frame world 2 then evalFormulaMask frame fml 2 else allValuationsTrueMask))
        h3

private theorem evalFormulaMask_testBit
    (frame : FiniteKripkeFrame 4)
    (fml : ModalFormula KripkeGameVars)
    (world : Fin 4)
    (idx : ValuationIndex) :
    Nat.testBit (evalFormulaMask frame fml world) idx =
      (decodeValuation frame idx).decideSatisfaction world fml := by
  induction fml generalizing world with
  | var var =>
      simpa [decodeValuation, evalFormulaMask, KripkeFrame.Valuation.decideSatisfaction] using
        valuationTruthMask_testBit var world idx
  | neg fml ih =>
      simp [evalFormulaMask, KripkeFrame.Valuation.decideSatisfaction, Nat.testBit_xor,
        testBit_allValuationsTrueMask, ih]
  | and left right ihLeft ihRight =>
      simp [evalFormulaMask, KripkeFrame.Valuation.decideSatisfaction, Nat.testBit_and,
        ihLeft, ihRight]
  | box fml ih =>
      let b0 := if frame world 0 then (decodeValuation frame idx).decideSatisfaction 0 fml else true
      let b1 := if frame world 1 then (decodeValuation frame idx).decideSatisfaction 1 fml else true
      let b2 := if frame world 2 then (decodeValuation frame idx).decideSatisfaction 2 fml else true
      let b3 := if frame world 3 then (decodeValuation frame idx).decideSatisfaction 3 fml else true
      have h0 : Nat.testBit (if frame world 0 then evalFormulaMask frame fml 0 else allValuationsTrueMask) idx = b0 := by
        dsimp [b0]
        by_cases h : frame world 0
        · simp [h, ih 0]
        · simp [h, testBit_allValuationsTrueMask]
      have h1 : Nat.testBit (if frame world 1 then evalFormulaMask frame fml 1 else allValuationsTrueMask) idx = b1 := by
        dsimp [b1]
        by_cases h : frame world 1
        · simp [h, ih 1]
        · simp [h, testBit_allValuationsTrueMask]
      have h2 : Nat.testBit (if frame world 2 then evalFormulaMask frame fml 2 else allValuationsTrueMask) idx = b2 := by
        dsimp [b2]
        by_cases h : frame world 2
        · simp [h, ih 2]
        · simp [h, testBit_allValuationsTrueMask]
      have h3 : Nat.testBit (if frame world 3 then evalFormulaMask frame fml 3 else allValuationsTrueMask) idx = b3 := by
        dsimp [b3]
        by_cases h : frame world 3
        · simp [h, ih 3]
        · simp [h, testBit_allValuationsTrueMask]
      rw [evalFormulaMask]
      simp only [Nat.testBit_and, h0, h1, h2, h3]
      dsimp [b0, b1, b2, b3]
      simp [KripkeFrame.Valuation.decideSatisfaction, KripkeFrame.accessible,
        Fin.forall_fin_succ, Bool.decide_and, Bool.and_assoc, FiniteKripkeFrame.asKripkeFrame]

private theorem evalFormulaMask_allValuationsTrue_iff
    (frame : FiniteKripkeFrame 4)
    (fml : ModalFormula KripkeGameVars)
    (world : Fin 4) :
    decide (evalFormulaMask frame fml world = allValuationsTrueMask) = true ↔
      frame.satisfiesForAllValuations world fml = true := by
  rw [decide_eq_true_iff, satisfiesForAllValuations_eq_decide_forall_decode, decide_eq_true_iff]
  constructor
  · intro h idx
    have hBit : Nat.testBit (evalFormulaMask frame fml world) idx =
        Nat.testBit allValuationsTrueMask idx := congrArg (fun n => Nat.testBit n idx) h
    have hEval : (decodeValuation frame idx).decideSatisfaction world fml = Nat.testBit allValuationsTrueMask idx :=
      (evalFormulaMask_testBit frame fml world idx).symm.trans hBit
    simpa using hEval.trans (testBit_allValuationsTrueMask idx)
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 65536
    · let idx : ValuationIndex := ⟨i, hi⟩
      have hEval : Nat.testBit (evalFormulaMask frame fml world) i = true := by
        simpa [idx] using (evalFormulaMask_testBit frame fml world idx).trans (h idx)
      have hAll : Nat.testBit allValuationsTrueMask i = true := by
        simpa [idx] using testBit_allValuationsTrueMask idx
      exact hEval.trans hAll.symm
    · have hi' : 65536 ≤ i := Nat.le_of_not_lt hi
      have hPow : 2 ^ 65536 ≤ 2 ^ i := Nat.pow_le_pow_right Nat.zero_lt_two hi'
      have hEval : Nat.testBit (evalFormulaMask frame fml world) i = false := by
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (evalFormulaMask_lt frame fml world) hPow)
      have hAll : Nat.testBit allValuationsTrueMask i = false := by
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le allValuationsTrueMask_lt hPow)
      exact hEval.trans hAll.symm

namespace FiniteKripkeFrame

def countSatisfyingNodesFast4 (frame : FiniteKripkeFrame 4) (fml : ModalFormula KripkeGameVars) : ℕ :=
  (Finset.univ.filter fun world : Fin 4 => decide (evalFormulaMask frame fml world = allValuationsTrueMask)).card

theorem countSatisfyingNodesFast4_eq (frame : FiniteKripkeFrame 4) (fml : ModalFormula KripkeGameVars) :
    countSatisfyingNodesFast4 frame fml = frame.countSatisfyingNodes fml := by
  unfold countSatisfyingNodesFast4 FiniteKripkeFrame.countSatisfyingNodes FiniteKripkeFrame.allNodes
  apply congrArg Finset.card
  ext world
  simpa using (evalFormulaMask_allValuationsTrue_iff frame fml world)

end FiniteKripkeFrame

end KripkeGameStrategy
