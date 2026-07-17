/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Lean
import VersoManual.Basic
import ProbabilityApproximationBlueprint.Sources

namespace Citations

open Lean Elab

open Verso Doc Elab Genre Manual in
inline_extension Inline.referenceLink (label : String) where
  data := toJson label
  traverse _id _data _contents := pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun go _id data contents => do
      let .ok label := fromJson? (α := String) data
        | Verso.reportError s!"Malformed bibliography link: {data}"
          pure .empty
      let body ← contents.mapM go
      let anchor := "bp-bib-" ++ Informal.Cite.citationAnchorId label
      pure <| .raw ("\\hyperlink{" ++ anchor ++ "}{") ++ body ++ .raw "}"
  toHtml :=
    some <| fun go _id _data contents =>
      contents.mapM go

open Verso Doc Elab in
private def citeItemTerm (label : String) (declaration : Lean.Name) :
    DocElabM (TSyntax `term) :=
  `(Informal.Cite.CiteItem.mk $(quote label) $(mkIdent declaration))

open Verso Doc Elab in
private def linkedCitationTerm (label : String) (item : TSyntax `term)
    (style : Informal.Cite.CitationStyle)
    (kind : Option Informal.Cite.CitePartKind) (index : Option String)
    (contents : Array (TSyntax `term)) : DocElabM (TSyntax `term) := do
  let citation ←
    `(Verso.Doc.Inline.other
      (Informal.Cite.Inline.bpCite
        ([$item] : List Informal.Cite.CiteItem)
        $(quote style)
        $(quote kind)
        $(quote index))
      #[$contents,*])
  `(Verso.Doc.Inline.other
    (Citations.Inline.referenceLink $(quote label))
    #[$citation])

private def intersperse (separator : TSyntax `term) (items : Array (TSyntax `term)) :
    Array (TSyntax `term) :=
  items.foldl (init := #[]) fun output item =>
    if output.isEmpty then output.push item else output.push separator |>.push item

open Verso Doc Elab in
private def groupedCitationTerm (style : Informal.Cite.CitationStyle)
    (config : Informal.Cite.CiteConfig) (extra : Array (TSyntax `inline)) :
    DocElabM (TSyntax `term) := do
  let resolved ←
    config.citations.mapM fun citation =>
      Informal.Cite.resolveCitation citation.syntax citation.val
  let extraTerms ← extra.mapM elabInline
  match resolved with
  | [] => throwError "A bibliography citation must contain at least one key"
  | [(label, declaration)] =>
      let item ← citeItemTerm label declaration
      linkedCitationTerm label item style config.kind config.index extraTerms
  | citations =>
      let itemStyle :=
        match style with
        | .parenthetical => Informal.Cite.CitationStyle.here
        | .textual => .textual
        | .here => .here
      let linked ← citations.toArray.mapM fun (label, declaration) => do
        let item ← citeItemTerm label declaration
        linkedCitationTerm label item itemStyle none none #[]
      let separator ← `(Verso.Doc.Inline.text "; ")
      let mut pieces := intersperse separator linked
      if style == .parenthetical then
        pieces := #[← `(Verso.Doc.Inline.text "(")] ++ pieces
      if let some locator := Informal.Cite.locatorText config.kind config.index then
        pieces := pieces.push (← `(Verso.Doc.Inline.text $(quote s!", {locator}")))
      unless extraTerms.isEmpty do
        pieces := pieces.push (← `(Verso.Doc.Inline.text ", ")) ++ extraTerms
      if style == .parenthetical then
        pieces := pieces.push (← `(Verso.Doc.Inline.text ")"))
      `(Verso.Doc.Inline.concat #[$pieces,*])

open Verso Doc Elab in
@[role]
def citep : RoleExpanderOf Informal.Cite.CiteConfig
  | config, extra => groupedCitationTerm .parenthetical config extra

open Verso Doc Elab in
@[role]
def citet : RoleExpanderOf Informal.Cite.CiteConfig
  | config, extra => groupedCitationTerm .textual config extra

open Verso Doc Elab in
@[role]
def citehere : RoleExpanderOf Informal.Cite.CiteConfig
  | config, extra => groupedCitationTerm .here config extra

end Citations
