/-
 - Created in 2025 by Rémy Degenne
-/

import VersoManual

import Manual.Front

open Verso.Genre.Manual Verso.Output.Html

def extraCss : List String := ["static/style.css"]

def extraHead : Array Verso.Output.Html := #[
    {{<link rel="icon" type="image/x-icon" href="static/favicon.svg"/>}},
    {{<script src="static/scripts.js"></script>}},
  ]

def config : Config :=
  Config.addKaTeX (
    Config.addSearch {
      extraCss := extraCss,
      extraHead := extraHead,
      sourceLink := some "https://github.com/RemyDegenne/demo-martingales",
      issueLink := some "https://github.com/RemyDegenne/demo-martingales/issues",
    }
  )

def main := manualMain (%doc Manual.Front) (config := config)
