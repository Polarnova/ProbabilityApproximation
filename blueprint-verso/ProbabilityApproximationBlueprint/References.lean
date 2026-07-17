/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import VersoManual.Basic
import VersoBlueprint.Commands.Bibliography
import ProbabilityApproximationBlueprint.Sources

namespace ProbabilityApproximationBlueprint.References

open Lean Elab
open Verso.Genre.Manual.Bibliography

private partial def inlineText : Verso.Doc.Inline Verso.Genre.Manual → String
  | .text value | .code value | .math _ value => value
  | .bold contents | .emph contents | .concat contents | .other _ contents
  | .link contents _ | .footnote _ contents =>
      contents.toList.foldl (init := "") fun output content =>
        output ++ inlineText content
  | .linebreak value => value
  | .image description _ => description

private def referenceSortKey (entry : Informal.Commands.BibliographyEntry) : String :=
  let authors :=
    entry.citation.authors.map fun author =>
      inlineText (Bibliography.lastName author)
  String.intercalate "\u0000" authors.toList ++
    "\u0000" ++ toString entry.citation.year ++
    "\u0000" ++ entry.label

open Verso Doc Elab Genre Manual in
block_extension Block.references (bibliography : Informal.Commands.BibliographyData) where
  data := toJson bibliography
  traverse := Informal.Commands.Block.bibliography.descr.traverse
  toHtml := Informal.Commands.Block.bibliography.descr.toHtml
  extraCss := Informal.Commands.Block.bibliography.descr.extraCss
  extraJs := Informal.Commands.Block.bibliography.descr.extraJs
  usePackages := Informal.Commands.Block.bibliography.descr.usePackages
  preamble := ["\\hypersetup{hidelinks}"]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun goI _goB _id data _contents => do
      let .ok bibliography :=
          fromJson? (α := Informal.Commands.BibliographyData) data
        | Verso.reportError s!"Malformed references data: {data}"
          pure .empty
      let entries :=
        bibliography.entries.toArray.qsort
          (fun left right => referenceSortKey left < referenceSortKey right)
      let items ← entries.mapM fun entry => do
        let rendered ← entry.citation.bibTeX goI
        let anchor := "bp-bib-" ++ Informal.Cite.citationAnchorId entry.label
        let anchored :=
          .raw ("\\hypertarget{" ++ anchor ++ "}{") ++ rendered ++ .raw "}"
        pure \TeX{\item[] \Lean{anchored} s!"\n"}
      let body := \TeX{\begin{description}\Lean{items}\end{description}}
      pure <|
        .raw "\\begingroup\n\\let\\href\\oldhref\n" ++
        body ++
        .raw "\n\\endgroup\n"

open Verso Doc Elab Syntax PartElabM
private def mkReferencesPart (stx : Syntax) (endPos : String.Pos.Raw) :
    PartElabM FinishedPart := do
  let titlePreview := "References"
  let titleSyntax ← `(inline | "References")
  let expandedTitle ← #[titleSyntax].mapM (elabInline ·)
  let metadata : Option (TSyntax `term) := some (← `(term| { number := false }))
  let entries := Informal.Cite.allBibEntries (← getEnv)
  let referenceTerms : Array (TSyntax `term) ← entries.toArray.mapM fun (label, declaration) =>
    `(Informal.Commands.BibliographyEntry.mk $(quote label) $(mkIdent declaration))
  let block ←
    ``(Verso.Doc.Block.other
      (ProbabilityApproximationBlueprint.References.Block.references
        (Informal.Commands.BibliographyData.mk
          (entries := ([$referenceTerms,*] : List Informal.Commands.BibliographyEntry))))
      #[])
  pure <| FinishedPart.mk stx stx expandedTitle titlePreview metadata #[block] #[] endPos

open Verso Doc Elab Syntax PartElabM in
@[part_command Lean.Doc.Syntax.command]
public meta def referencesCmd : PartCommand
  | stx@`(block|command{references}) => do
      let endPos := stx.getTailPos?.get!
      closePartsUntil 1 endPos
      addPart (← mkReferencesPart stx endPos)
  | _ => (Lean.Elab.throwUnsupportedSyntax : PartElabM Unit)

end ProbabilityApproximationBlueprint.References
