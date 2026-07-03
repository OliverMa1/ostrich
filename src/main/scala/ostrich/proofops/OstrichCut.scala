/**
 * This file is part of Ostrich, an SMT solver for strings.
 * Copyright (c) 2024-2025 Philipp Ruemmer. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ostrich.proofops

import ap.basetypes.IdealInt
import ap.parser.SMTLineariser
import ap.terfor.TerForConvenience
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{Atom, PredConj}
import ap.terfor.{Term, TermOrder, ConstantTerm}
import ap.terfor.conjunctions.Conjunction
import ap.theories.TheoryRegistry
import ap.types.{Sort, SortedPredicate}
import ap.parameters.Param
import ap.util.{Tarjan, Seqs}

import LinearCombination.SingleTerm

import ostrich._
import ostrich.automata.{
  AtomicStateAutomaton, AutomataUtils, Automaton, BricsAutomaton
}

import scala.collection.mutable.{HashSet => MHashSet}

object OstrichCut {

  case class CutProposal(
    variable      : ConstantTerm,
    preferredWord : Option[Seq[Int]],
    method        : String,
    details       : String = ""
  )

  private final case class CutWord(
    word    : Seq[Int],
    method  : String,
    details : String
  )

  private final case class RegularEntry(complemented : Boolean, atom : Atom)

}

/**
 * Class to pick concrete values of string variables. This proof rule
 * is currently only applied when everything else has finished.
 */
class OstrichCut(val theory : OstrichStringTheory)
      extends PropagationSaturationUtils {

  import theory._
  import OstrichCut._

  private lazy val cutTracePrinter = new CutTracePrinter
  private val MaxTraceAutomatonRegexChars = 4000

  private val llmUtils = new LLMUtils()

  def handleGoal(goal : Goal, cutEverything : Boolean) : Seq[Plugin.Action] = {
    assert(cutEverything, "selective cuts not finalized yet")
    val stringVariables =
      if (cutEverything) findAllStringVars(goal) else findCutVars(goal)

    if (stringVariables.nonEmpty) {
      val rand = Param.RANDOM_DATA_SOURCE(goal.settings)

      val proposal =
        if (theoryFlags.experimentalCutPicker)
          chooseExperimentalCut(goal, stringVariables)
            .getOrElse(CutProposal(rand.pick(stringVariables), None,
                                   "fallback-random"))
        else
          CutProposal(rand.pick(stringVariables), None, "legacy-random")

      //if (theoryFlags.cutTrace)
      // Console.err.println(cutTracePrinter.preCutGoalToString(goal, stringVariables, Some(proposal)))

      cutForProposal(goal, proposal)
    } else {
      List()
    }
  }

  private def chooseExperimentalCut(
    goal            : Goal,
    stringVariables : IndexedSeq[ConstantTerm]
  ) : Option[CutProposal] = {
    // Collaborator hook: inspect the saturated goal, dependencies, regex
    // domains, length facts, etc., then return Some(CutProposal(...)).
    //goal
    //CutProposal(
      //variable = someStringVariable,
      //preferredWord = Some(Seq('V'.toInt)),
      //method = "my-picker",
      //details = "short diagnostic note"
    //)

    val prompt : String = llmUtils.generatePrompt(cutTracePrinter.preCutGoalForPromptToString(goal, stringVariables))
    val response : String = llmUtils.promptLLM(prompt)
    println(response)
    val parsed = parseLLMResponse(response, stringVariables)

    // Just some printing for now
    parsed match {
      case Some(x) =>
        print(x._1)
        print("=")
        print(x._2)
        println()
      case None => None
    }

    parsed match {
      case Some(x) =>
        Some(
          CutProposal(
          variable = x._1,
          preferredWord = x._2,
          method = "LLM based suggestion",
          details = "short diagnostic note"
        ))
      case None => None
    }
  }

  private def parseLLMResponse(str: String, stringVariables : IndexedSeq[ConstantTerm]) : Option[(ConstantTerm, Option[Seq[Int]])]  = {
    val lines = str.trim.split("\n", 2)
    if (lines.length == 2) {
      val name = lines(0).trim
      val quoted = lines(1).trim

      if (quoted.length >= 2 &&
        quoted.head == '"' &&
        quoted.last == '"') {

        val chars = quoted.substring(1, quoted.length - 1).map(_.toInt)
        for (variable <- stringVariables) {
          if (variable.name == name) {
            return Some(variable, Some(chars))
          }
        }
      }
    }
    None
  }

  private def findAllStringVars(goal : Goal) : IndexedSeq[ConstantTerm] = {
    val predConj = goal.facts.predConj
    val allAtoms = predConj.positiveLits ++ predConj.negativeLits

    (for (a <- allAtoms.iterator;
          sorts = SortedPredicate argumentSorts a;
          (LinearCombination.SingleTerm(c : ConstantTerm), StringSort) <-
            a.iterator zip sorts.iterator)
     yield c).toVector.distinct
  }

  /**
   * Find cut variables by building the dependency graph induced by
   * string function applications and computing its strongly connected
   * components. There are three cases in which we need to introduce
   * cuts for the possible values of string variable <code>x</code>:
   * <code>x</code> occurs in an SCC together with other string variables;
   * <code>x</code> occurs as the result variable of multiple function
   * applications; or there are other formulas (not belonging to the theory
   * of strings) that refer to <code>x</code>. We return the set of all
   * string variables that such variables <code>x</code> depend on.
   * 
   * Currently not used.
   */
  private def findCutVars(goal : Goal) : IndexedSeq[ConstantTerm] = {
    val predConj = goal.facts.predConj
    val allAtoms = predConj.positiveLits ++ predConj.negativeLits

    val funApps = getFunApps(goal)
    val stringVars =
      (for ((_, args, res, _) <- funApps;
            Some(SingleTerm(c : ConstantTerm)) <- args ++ List(Some(res)))
       yield c).toIndexedSeq.distinct

    // build the dependency graph

    def containsArg(t : FunAppTuple, c : ConstantTerm) =
      t._2.exists {
        case Some(SingleTerm(`c`)) => true
        case _ => false
      }

    type GraphNode = Either[ConstantTerm, FunAppTuple]
    val depGraph = new Tarjan.Graph[GraphNode] {
      val nodes =
        stringVars.map(Left(_)) ++ funApps.map(Right(_))
      def successors(n : GraphNode) =
        n match {
          case Left(c) =>
            for (t <- funApps.iterator; if containsArg(t, c)) yield Right(t)
          case Right((_, _, SingleTerm(c : ConstantTerm), _)) =>
            Iterator(Left(c))
          case _ =>
            Iterator()
        }
    }

    // compute strongly connected components

    val sccs = Tarjan(depGraph)

    println(sccs)

    // string variables that occur as the result of multiple function
    // applications

    val multiplyAssignedVars =
      (for ((SingleTerm(c : ConstantTerm), apps) <- funApps.groupBy(_._3);
            if apps.size > 1)
       yield c).toSet

    // compute string variables that are used by non-theory atoms

    val nonTheoryAtoms =
      allAtoms filterNot {
        a => TheoryRegistry.lookupSymbol(a.pred) match {
          case Some(`theory`) => true
          case _ => false
        }
      }

    val nonTheoryAtomVars =
      (for (a <- nonTheoryAtoms; c <- a.constants) yield c).toSet

    // compute all string variables to be considered in cuts
    
    val cutNodes = new MHashSet[GraphNode]

    for (scc <- sccs.reverse) {
      val sccVars =
        for (Left(c) <- scc) yield c
      if (sccVars.size > 1 ||
          !Seqs.disjointSeq(nonTheoryAtomVars, sccVars) ||
          !Seqs.disjointSeq(multiplyAssignedVars, sccVars) ||
          scc.exists(n => depGraph.successors(n) exists cutNodes))
        cutNodes ++= scc
    }

    println(cutNodes)

    val cutVars = for (Left(c) <- cutNodes.toSeq) yield c
    goal.order.sort(cutVars).toVector
  }

  /**
   * Perform a cut for one specific string variable: split the proof into
   * the cases <code>x = w</code> and <code>x != w</code>, for some string
   * <code>w</code> in the domain of <code>x</code>.
   */
  private def cutForVar(goal : Goal,
                        stringVar : ConstantTerm) : Seq[Plugin.Action] =
    cutForVar(goal, stringVar, "legacy-enumeration", "")

  private def cutForVar(goal : Goal,
                        stringVar : ConstantTerm,
                        method : String,
                        details : String) : Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val order = goal.order
    val predConj = goal.facts.predConj

    val stringVarLC = l(stringVar)

    val regexes =
      for (a <- predConj.positiveLitsWithPred(str_in_re_id);
           if a.head == stringVarLC)
      yield a.last

    val auts =
      for (LinearCombination.Constant(IdealInt(id)) <- regexes)
      yield autDatabase.id2Automaton(id).get

    val (lowerLenBound, upperLenBound) = lengthBounds(goal, stringVarLC)

    val acceptedWord =
      AutomataUtils.findAcceptedWord(auts, lowerLenBound, upperLenBound)

    if (acceptedWord.isDefined) {
      cutForWord(goal, stringVar, CutWord(acceptedWord.get, method, details))
    } else {
      if (OFlags.debug)
        Console.err.println("OstrichCut closed a proof goal")

      val rcons =
        predConj.positiveLitsWithPred(str_in_re_id)
          .filter(_.head == stringVarLC)
          .toSeq
      // TODO: this will not catch all relevant assumptions:
      // the lowerBound/upperBound functions might rely on further formulas
      val lcons =
        predConj.positiveLitsWithPred(_str_len)
          .filter(_(0) == stringVar)
          .toSeq
      List(Plugin.CloseByAxiom(rcons ++ lcons, theory))
    }
  }

  private def cutForProposal(goal : Goal,
                             proposal : CutProposal) : Seq[Plugin.Action] =
    proposal.preferredWord match {
      case Some(word) =>
        validateProposedWord(goal, proposal.variable, word) match {
          case Right(()) =>
            cutForWord(goal, proposal.variable,
                       CutWord(word, proposal.method, proposal.details))

          case Left(reason) =>
            logRejectedCandidate(proposal.variable, word, reason)
            cutForVar(goal, proposal.variable, "fallback-enumeration",
                      appendDetails(proposal.details,
                                    "rejected candidate: " + reason))
        }

      case None =>
        cutForVar(goal, proposal.variable, proposal.method, proposal.details)
    }

  private def cutForWord(goal : Goal,
                         stringVar : ConstantTerm,
                         cutWord : CutWord) : Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val order = goal.order

    val acceptedWordId =
      strDatabase.list2Id(cutWord.word)

    val stringVarLC = l(stringVar)
    val negAutomaton =
      !BricsAutomaton.fromString(strDatabase.id2Str(acceptedWordId))
    val negAutomatonId =
      autDatabase.automaton2Id(negAutomaton)

    if (OFlags.debug) {
      val str = strDatabase.id2Str(acceptedWordId)
      Console.err.println(
        f"Performing cut: $stringVar == ${"\""}${str}${"\""} (length ${str.size})")
    }

    if (theoryFlags.cutTrace)
      Console.err.println(
        "OstrichCut chosen cut: var=" + stringVar +
        " word=" + quotedWord(cutWord.word) +
        " length=" + cutWord.word.size +
        " method=" + cutWord.method +
        detailsSuffix(cutWord.details))

    List(Plugin.AxiomSplit(
          List(),
          List((stringVar === acceptedWordId, List()),
               (str_in_re_id(List(stringVarLC, l(negAutomatonId))), List())),
          theory))
  }

  private[proofops] def validateProposedWord(
    goal : Goal,
    stringVar : ConstantTerm,
    word : Seq[Int]
  ) : Either[String, Unit] = {
    import TerForConvenience._
    implicit val order = goal.order

    val stringVarLC = l(stringVar)
    val predConj = goal.facts.predConj

    val positiveRegular =
      predConj.positiveLitsWithPred(str_in_re_id).map(RegularEntry(false, _))
    val negativeRegular =
      predConj.negativeLitsWithPred(str_in_re_id).map(RegularEntry(true, _))

    for (entry <- positiveRegular ++ negativeRegular; if entry.atom(0) == stringVarLC)
      automatonFor(entry) match {
        case Some(aut) =>
          if (!aut(word))
            return Left("not-in-current-domain")
        case None =>
          return Left("unknown-current-domain")
      }

    val (lowerLenBound, upperLenBound) = lengthBounds(goal, stringVarLC)

    (lowerLenBound, upperLenBound) match {
      case (Some(lb), Some(ub)) if lb == ub && word.size != lb =>
        Left("violates-exact-length-" + lb)
      case (Some(lb), _) if word.size < lb =>
        Left("below-lower-length-bound-" + lb)
      case (_, Some(ub)) if word.size > ub =>
        Left("above-upper-length-bound-" + ub)
      case _ =>
        Right(())
    }
  }

  private def lengthBounds(
    goal : Goal,
    stringVarLC : LinearCombination
  ) : (Option[Int], Option[Int]) = {
    val predConj = goal.facts.predConj
    val reducer = goal.reduceWithFacts

    val lengthTerm =
      predConj.positiveLitsWithPred(_str_len)
        .collectFirst { case a if a(0) == stringVarLC => a(1) }

    val lowerLenBound =
      lengthTerm.flatMap(reducer.lowerBound).map(_.intValue)
    val upperLenBound =
      lengthTerm.flatMap(reducer.upperBound).map(_.intValue)

    (lowerLenBound, upperLenBound)
  }

  private def automatonFor(entry : RegularEntry) : Option[Automaton] =
    try {
      Some(decodeRegexId(entry.atom, entry.complemented))
    } catch {
      case _ : Throwable => None
    }

  private def logRejectedCandidate(stringVar : ConstantTerm,
                                   word : Seq[Int],
                                   reason : String) : Unit =
    if (theoryFlags.cutTrace)
      Console.err.println(
        "OstrichCut rejected candidate: var=" + stringVar +
        " word=" + quotedWord(word) +
        " reason=" + reason)

  private def appendDetails(base : String, extra : String) : String =
    if (base.isEmpty) extra else base + "; " + extra

  private def detailsSuffix(details : String) : String =
    if (details.isEmpty) "" else " details=" + details

  private def quotedWord(word : Seq[Int]) : String =
    "\"" + SMTLineariser.escapeString(word.map(_.toChar).mkString) + "\""

  private[proofops] def hiddenBookkeepingAtom(a : Atom) : Boolean = {
    val name = a.pred.name
    a.pred == agePred ||
    name.endsWith("Propagation_spawned") ||
    name == "LengthAbstraction_spawned"
  }

  private[proofops] def sourceRegexForTrace(
    a : Atom,
    complemented : Boolean
  ) : Option[String] =
    a(1) match {
      case LinearCombination.Constant(id) =>
        autDatabase.id2Regex(id.intValueSafe).map { regex =>
          val body = SMTLineariser.asString(regex)
          if (complemented) "(re.comp " + body + ")" else body
        }
      case _ =>
        None
    }

  private[proofops] def sourceRegexOrAutomatonForTrace(
    a : Atom,
    complemented : Boolean
  ) : String =
    sourceRegexForTrace(a, complemented)
      .getOrElse(sourceAutomatonForTrace(a, complemented))

  private[proofops] def sourceAutomatonForTrace(
    a : Atom,
    complemented : Boolean
  ) : String =
    a(1) match {
      case LinearCombination.Constant(id) =>
        val autId = id.intValueSafe
        autDatabase.id2Automaton(autId) match {
          case Some(aut : AtomicStateAutomaton) =>
            try {
              val body = fromAutomatonRegex(aut)
              val regex =
                if (complemented) "(re.comp " + body + ")" else body
              if (regex.size <= MaxTraceAutomatonRegexChars)
                regex
              else
                summarizedAutomatonFallback(autId, complemented, aut,
                                            regex.size)
            } catch {
              case _ : Throwable =>
                automatonIdFallback(autId, complemented)
            }
          case _ =>
            automatonIdFallback(autId, complemented)
        }
      case other =>
        "<automaton id term=" + other + ">"
    }

  private def fromAutomatonRegex(aut : AtomicStateAutomaton) : String =
    "(re.from_automaton \"" +
      SMTLineariser.escapeString(AutomatonParser.toString(aut)) +
      "\")"

  private def summarizedAutomatonFallback(
    id          : Int,
    complemented : Boolean,
    aut         : AtomicStateAutomaton,
    regexChars  : Int
  ) : String = {
    val summary =
      "<automaton id=" + id +
      " states=" + aut.states.size +
      " transitions=" + aut.transitions.size +
      " re.from_automaton chars=" + regexChars + ">"
    if (complemented) "(re.comp " + summary + ")" else summary
  }

  private def automatonIdFallback(id : Int, complemented : Boolean) : String = {
    val summary = "<automaton id=" + id + ">"
    if (complemented) "(re.comp " + summary + ")" else summary
  }

  private final class CutTracePrinter {

    private var preCutCount = 0
    private val MaxIntersectedSummaryConstraints = 8

    def preCutGoalForPromptToString(goal: Goal,
                                    stringVariables: IndexedSeq[ConstantTerm]) : String = this.synchronized {
      if (theoryFlags.cutTraceLimit <= 0 ||
        preCutCount >= theoryFlags.cutTraceLimit)
        return ""

      preCutCount = preCutCount + 1

      val out = new StringBuilder
      out.append("=== OstrichCut pre-cut goal #")
      out.append(preCutCount)
      out.append(" BEGIN ===\n")

      appendArithmeticConstraints(out, goal)
      appendStringAndFunctionConstraints(out, goal)
      appendRegularConstraints(out, goal)
      appendCutVariables(out, stringVariables)

      out.append("=== OstrichCut pre-cut goal #")
      out.append(preCutCount)
      out.append(" END ===\n")

      out.toString
    }

    def preCutGoalToString(
                            goal: Goal,
                            stringVariables: IndexedSeq[ConstantTerm],
                            proposal: Option[CutProposal]
                          ): String = this.synchronized {
      if (theoryFlags.cutTraceLimit <= 0 ||
        preCutCount >= theoryFlags.cutTraceLimit)
        return ""

      preCutCount = preCutCount + 1

      val out = new StringBuilder
      out.append("=== OstrichCut pre-cut goal #")
      out.append(preCutCount)
      out.append(" BEGIN ===\n")

      appendArithmeticConstraints(out, goal)
      appendStringAndFunctionConstraints(out, goal)
      appendRegularConstraints(out, goal)
      appendCutVariables(out, stringVariables)
      appendChosenCut(out, proposal)
      appendCutAnalysis(out, goal)

      out.append("=== OstrichCut pre-cut goal #")
      out.append(preCutCount)
      out.append(" END ===\n")

      out.toString
    }

    private def appendArithmeticConstraints(out : StringBuilder,
                                            goal : Goal) : Unit = {
      out.append("Arithmetic constraints:\n")
      val arithConj = goal.facts.arithConj
      if (arithConj.size == 0)
        out.append("  <none>\n")
      else
        appendLines(out, arithConj.toString)
    }

    private def appendStringAndFunctionConstraints(out : StringBuilder,
                                                   goal : Goal) : Unit = {
      out.append("String and function constraints:\n")
      val predConj = goal.facts.predConj
      val entries =
        (for (a <- predConj.positiveLits.iterator;
              if !hiddenBookkeepingAtom(a);
              if a.pred != str_in_re_id)
         yield ("+", a)).toVector ++
        (for (a <- predConj.negativeLits.iterator;
              if !hiddenBookkeepingAtom(a);
              if a.pred != str_in_re_id)
         yield ("-", a)).toVector

      if (entries.isEmpty) {
        out.append("  <none>\n")
      } else {
        for ((sign, atom) <- entries) {
          out.append("  ")
          out.append(sign)
          out.append(" ")
          out.append(printableAtom(atom))
          out.append("\n")
        }
      }
    }

    private def appendRegularConstraints(out : StringBuilder,
                                         goal : Goal) : Unit = {
      out.append("Regular-language constraints:\n")
      val predConj = goal.facts.predConj
      val entries =
        predConj.positiveLitsWithPred(str_in_re_id).map(RegularEntry(false, _)) ++
        predConj.negativeLitsWithPred(str_in_re_id).map(RegularEntry(true, _))

      if (entries.isEmpty) {
        out.append("  <none>\n")
      } else {
        val grouped =
          entries.groupBy(_.atom(0)).toSeq.sortBy(_._1.toString)

        for ((term, termEntries) <- grouped) {
          out.append("  ")
          out.append(printableStringTerm(term, StringSort))
          out.append(" domain (")
          out.append(termEntries.size)
          out.append(" constraints): ")
          out.append(regularDomainSummary(termEntries))
          out.append("\n")

          for (entry <- termEntries) {
            out.append("    source regex ")
            out.append(sourceRegexOrAutomatonForTrace(entry.atom,
                                                      entry.complemented))
            out.append("\n")
          }
        }
      }
    }

    private def appendCutVariables(out : StringBuilder,
                                   stringVariables : IndexedSeq[ConstantTerm])
                                   : Unit = {
      out.append("Available cut variables:\n")
      if (stringVariables.isEmpty)
        out.append("  <none>\n")
      else {
        out.append("  ")
        out.append(stringVariables.mkString(", "))
        out.append("\n")
      }
    }

    private def appendChosenCut(out : StringBuilder,
                                proposal : Option[CutProposal]) : Unit = {
      out.append("Chosen cut:\n")
      proposal match {
        case Some(p) =>
          out.append("  variable=")
          out.append(p.variable)
          out.append("\n")
          out.append("  method=")
          out.append(p.method)
          out.append("\n")
          p.preferredWord match {
            case Some(word) =>
              out.append("  word=")
              out.append(quotedWord(word))
              out.append("\n")
              out.append("  length=")
              out.append(word.size)
              out.append("\n")
            case None =>
              out.append("  word=<legacy enumeration>\n")
          }
          if (!p.details.isEmpty) {
            out.append("  details=")
            out.append(p.details)
            out.append("\n")
          }
        case None =>
          out.append("  <none>\n")
      }
    }

    private def appendCutAnalysis(out : StringBuilder, goal : Goal) : Unit =
      try {
        val funApps = getFunApps(goal)
        val order = getCutOrder(goal).distinct
        val orderSet = order.toSet
        val leftover = funApps.filterNot(orderSet)

        out.append("Cut analysis:\n")
        out.append("  funApps=")
        out.append(funApps.size)
        out.append("\n")
        out.append("  order=")
        out.append(formatFunApps(order))
        out.append("\n")
        out.append("  leftover=")
        out.append(formatFunApps(leftover))
        out.append("\n")
        out.append("  straightLine=")
        out.append(straightLine(goal))
        out.append("\n")
        out.append("  chainFree=")
        out.append(chainFree(goal))
        out.append("\n")
      } catch {
        case e : Throwable =>
          out.append("Cut analysis:\n")
          out.append("  unavailable=")
          out.append(e.getClass.getSimpleName)
          out.append(": ")
          out.append(e.getMessage)
          out.append("\n")
      }

    private def regularDomainSummary(entries : Seq[RegularEntry]) : String = {
      val auts = entries.flatMap(automatonFor)
      if (auts.size != entries.size) {
        "automaton unavailable"
      } else if (auts.isEmpty) {
        "automaton unconstrained"
      } else if (auts.size <= MaxIntersectedSummaryConstraints &&
                 auts.forall(_.isInstanceOf[AtomicStateAutomaton])) {
        val aut = auts.reduceLeft(_ & _)
        automatonSummary(aut)
      } else {
        "automata=" + auts.size
      }
    }

    private def automatonSummary(aut : Automaton) : String =
      aut match {
        case atomic : AtomicStateAutomaton =>
          "automaton states=" + atomic.states.size +
          " transitions=" + atomic.transitions.size
        case _ =>
          "automaton type=" + aut.getClass.getSimpleName
      }

    private def printableAtom(a : Atom) : String = {
      val sorts = SortedPredicate.argumentSorts(a)
      val args =
        (a.iterator zip sorts.iterator).map {
          case (lc, sort) => printableStringTerm(lc, sort)
        }.toSeq
      a.pred.name + args.mkString("(", ", ", ")")
    }

    private def printableStringTerm(lc : LinearCombination,
                                    sort : Sort) : String =
      if (sort == StringSort)
        wordForLinearCombination(lc) match {
          case Some(word) => quotedWord(word)
          case None       => lc.toString
        }
      else
        lc.toString

    private def wordForLinearCombination(
      lc : LinearCombination
    ) : Option[Seq[Int]] =
      lc match {
        case LinearCombination.Constant(IdealInt(id))
            if strDatabase.containsId(id) =>
          Some(strDatabase.id2List(id))
        case _ =>
          None
      }

    private def appendLines(out : StringBuilder, text : String) : Unit = {
      val lines =
        text.split(" & ").iterator.map(_.trim).filter(_.nonEmpty).toSeq
      if (lines.isEmpty)
        out.append("  <none>\n")
      else
        for (line <- lines) {
          out.append("  ")
          out.append(line)
          out.append("\n")
        }
    }

    private def formatFunApps(funApps : Seq[FunAppTuple]) : String =
      if (funApps.isEmpty)
        "<none>"
      else
        funApps.map { case (_, _, _, atom) => printableAtom(atom) }
          .mkString("[", ", ", "]")
  }

}
