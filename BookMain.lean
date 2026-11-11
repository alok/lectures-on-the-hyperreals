import Book
import VersoManual

open Verso.Genre.Manual
open Verso.Output Html

def extraHeadTags : Array Html := #[
  {{ <link rel="stylesheet" href="static/hyperreals.css" /> }},
  {{ <script src="static/hyperreals-3d.js" defer="defer"></script> }}
]

def main (args : List String) : IO UInt32 :=
  manualMain (%doc Book) (options := args) (config := config)
where
  config : RenderConfig := {
    extraFiles := [("static", "static")],
    extraHead := extraHeadTags,
    emitTeX := false,
    emitHtmlSingle := .no,
    emitHtmlMulti := .immediately,
    htmlDepth := 2,
    sectionTocDepth := some 2,
    rootTocDepth := some 2,
    logo := some "static/logo.svg",
    logoLink := some "./",
    sourceLink := some "https://github.com/alok/lectures-on-the-hyperreals",
    issueLink := some "https://github.com/alok/lectures-on-the-hyperreals/issues"
  }
