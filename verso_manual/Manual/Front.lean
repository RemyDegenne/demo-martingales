/-
 - Created in 2025 by Rémy Degenne
-/

import Manual.Pages.Basic
import Manual.Pages.Martingales
import Manual.Pages.VariousDefs
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.exampleProject "src/"

set_option verso.exampleModule "Martingales.Martingales"

#doc (Manual) "Probability in Mathlib" =>
%%%
authors := ["Rémy Degenne"]
shortTitle := "Probability in Mathlib"
%%%

How do I define a probability space and two independent random variables in Lean? Should I use `IsProbabilityMeasure` or `ProbabilityMeasure`?
How do I condition on an event?

This document answers these and other simple questions about how to work with probability using Mathlib.

{include 0 Manual.Pages.Basic}

{include 0 Manual.Pages.Martingales}

{include 0 Manual.Pages.VariousDefs}
