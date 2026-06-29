/**
 * This file is part of Ostrich, an SMT solver for strings.
 * Copyright (c) 2026 Oliver Markgraf, Matthew Hague, Philipp Ruemmer.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright
 *   notice, this list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright
 *   notice, this list of conditions and the following disclaimer in the
 *   documentation and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their contributors
 *   may be used to endorse or promote products derived from this software
 *   without specific prior written permission.
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

import ap.proof.theoryPlugins.Plugin
import ap.parser.IConstant
import ap.parser.IFormula
import ap.terfor.preds.{Atom, Predicate}
import ap.types.MonoSortedPredicate
import org.scalacheck.Properties
import ostrich.automata.BricsAutomaton

object OstrichCutSpecification
  extends Properties("OstrichCutSpecification")
          with TestProverUtils {

  import prover._
  import ap.parser.IExpression._
  import theory._

  implicit val order = prover.order

  private val xTerm = createConstant("cut_x", StringSort)
  private val x = xTerm.asInstanceOf[IConstant].c
  private val cut = new OstrichCut(theory)

  private val autA = BricsAutomaton.fromString("a")
  private val idAutA = autDatabase.automaton2Id(autA)

  private val regexId =
    autDatabase.regex2Id(re_+(str_to_re("x")))

  shutdown

  private def atomFrom(formula : IFormula, pred : Predicate) : Atom =
    createGoalFor(formula).facts.predConj.positiveLitsWithPred(pred).head

  property("Trace hides bookkeeping atoms") = {
    val semanticGoal = createGoalFor(str_in_re_id(xTerm, idAutA))
    val ageAtom = cut.buildAge(x, 0, 0, semanticGoal)
    val spawnedPred =
      MonoSortedPredicate("BackwardsPropagation_spawned", List())
    val spawnedAtom =
      Atom.createNoCopy(spawnedPred, Array(), semanticGoal.order)
    val semanticAtom =
      semanticGoal.facts.predConj.positiveLitsWithPred(str_in_re_id).head

    cut.hiddenBookkeepingAtom(ageAtom) &&
    cut.hiddenBookkeepingAtom(spawnedAtom) &&
    !cut.hiddenBookkeepingAtom(semanticAtom)
  }

  property("Trace decodes stored source regexes") = {
    val atom = atomFrom(str_in_re_id(xTerm, regexId), str_in_re_id)

    val decoded = cut.sourceRegexForTrace(atom, complemented = false)
    val complemented = cut.sourceRegexForTrace(atom, complemented = true)

    decoded.exists(_.contains("\"x\"")) &&
    complemented.exists(s => s.startsWith("(re.comp ") && s.contains("\"x\""))
  }

  property("Trace prints automaton literals for automaton-only ids") = {
    val atom = atomFrom(str_in_re_id(xTerm, idAutA), str_in_re_id)

    val decoded = cut.sourceRegexOrAutomatonForTrace(atom, complemented = false)
    val complemented =
      cut.sourceRegexOrAutomatonForTrace(atom, complemented = true)

    decoded.startsWith("(re.from_automaton \"") &&
    decoded.contains("automaton aut") &&
    complemented.startsWith("(re.comp (re.from_automaton \"")
  }

  property("Candidate words are checked against current domains") = {
    val positiveGoal = createGoalFor(str_in_re_id(xTerm, idAutA))
    val negativeGoal = createGoalFor(!str_in_re_id(xTerm, idAutA))

    cut.validateProposedWord(positiveGoal, x, Seq('a'.toInt)) == Right(()) &&
    cut.validateProposedWord(positiveGoal, x, Seq('b'.toInt)).left.toOption ==
      Some("not-in-current-domain") &&
    cut.validateProposedWord(negativeGoal, x, Seq('a'.toInt)).left.toOption ==
      Some("not-in-current-domain")
  }

  property("Candidate words are checked against length facts") = {
    val goal = createGoalFor(str_len(xTerm) === 1)

    cut.validateProposedWord(goal, x, Seq('a'.toInt)) == Right(()) &&
    cut.validateProposedWord(goal, x, Seq('a'.toInt, 'a'.toInt)).left.toOption ==
      Some("violates-exact-length-1")
  }

  property("Legacy cut path still produces the exhaustive split") = {
    val goal = createGoalFor(str_in_re_id(xTerm, idAutA))

    cut.handleGoal(goal, cutEverything = true) match {
      case Seq(Plugin.AxiomSplit(_, cases, _)) => cases.size == 2
      case _ => false
    }
  }

}
