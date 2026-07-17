/-
Copyright (c) 2026 Asher Yan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asher Yan with ChatGPT 5.6
-/
import Lean
import VersoBlueprint.Cite

open Lean Elab Command
open Verso.Genre.Manual.Bibliography

namespace ProbabilityApproximationBlueprint.BibTeX

/-- A parsed BibTeX entry before conversion to Verso's bibliography model. -/
structure Entry where
  kind : String
  key : String
  fields : List (String × String)
deriving Repr, Inhabited

private abbrev Parser := StateT (List Char) (Except String)

private def trim (value : String) : String :=
  value.trimAscii.toString

private def normalizedName (value : String) : String :=
  (trim value).toLower

private def isNameChar (char : Char) : Bool :=
  char.isAlphanum || char == '_' || char == '-' || char == ':' || char == '.'

private partial def skipTrivia : Parser Unit := do
  match ← get with
  | [] => pure ()
  | '%' :: chars =>
      let chars := chars.dropWhile (· != '\n')
      set chars
      skipTrivia
  | char :: chars =>
      if char.isWhitespace then
        set chars
        skipTrivia

private def peek? : Parser (Option Char) := do
  pure (← get).head?

private def pop : Parser Char := do
  match ← get with
  | [] => throw "unexpected end of BibTeX input"
  | char :: chars =>
      set chars
      pure char

private def expect (expected : Char) : Parser Unit := do
  let actual ← pop
  unless actual == expected do
    throw s!"expected '{expected}', found '{actual}'"

private def takeWhile (predicate : Char → Bool) : Parser String := do
  let chars ← get
  let (taken, suffix) := chars.span predicate
  set suffix
  pure (String.ofList taken)

private def identifier : Parser String := do
  let value ← takeWhile isNameChar
  if value.isEmpty then
    throw "expected a BibTeX identifier"
  else
    pure value

private def untilDelimiter (delimiter : Char) : Parser String := do
  let value ← takeWhile (· != delimiter)
  pure (trim value)

private partial def bracedValueLoop (depth : Nat) (accumulator : List Char) : Parser String := do
  match ← pop with
  | '{' => bracedValueLoop (depth + 1) ('{' :: accumulator)
  | '}' =>
      if depth == 1 then
        pure (String.ofList accumulator.reverse)
      else
        bracedValueLoop (depth - 1) ('}' :: accumulator)
  | '\\' =>
      let escaped ← pop
      bracedValueLoop depth (escaped :: '\\' :: accumulator)
  | char => bracedValueLoop depth (char :: accumulator)

private def bracedValue : Parser String := do
  expect '{'
  bracedValueLoop 1 []

private partial def quotedValueLoop (accumulator : List Char) : Parser String := do
  match ← pop with
  | '"' => pure (String.ofList accumulator.reverse)
  | '\\' =>
      let escaped ← pop
      quotedValueLoop (escaped :: '\\' :: accumulator)
  | char => quotedValueLoop (char :: accumulator)

private def quotedValue : Parser String := do
  expect '"'
  quotedValueLoop []

private def bareValue : Parser String := do
  let value ← takeWhile fun char =>
    char != ',' && char != '}' && char != ')' && char != '#'
  let value := trim value
  if value.isEmpty then
    throw "expected a BibTeX value"
  else
    pure value

private def valueAtom : Parser String := do
  skipTrivia
  match ← peek? with
  | some '{' => bracedValue
  | some '"' => quotedValue
  | some _ => bareValue
  | none => throw "unexpected end of BibTeX input while reading a value"

private partial def value : Parser String := do
  let first ← valueAtom
  skipTrivia
  if (← peek?) == some '#' then
    discard pop
    let rest ← value
    pure (first ++ rest)
  else
    pure first

private partial def fields (closing : Char) (accumulator : List (String × String)) :
    Parser (List (String × String)) := do
  skipTrivia
  match ← peek? with
  | none => throw s!"unexpected end of BibTeX input; expected '{closing}'"
  | some char =>
      if char == closing then
        discard pop
        pure accumulator.reverse
      else if char == ',' then
        discard pop
        fields closing accumulator
      else
        let name := normalizedName (← identifier)
        skipTrivia
        expect '='
        let fieldValue ← value
        fields closing ((name, trim fieldValue) :: accumulator)

private def entry : Parser Entry := do
  skipTrivia
  expect '@'
  let kind := normalizedName (← identifier)
  skipTrivia
  let opening ← pop
  let closing ←
    match opening with
    | '{' => pure '}'
    | '(' => pure ')'
    | _ => throw s!"expected an opening brace or parenthesis after entry type, found '{opening}'"
  skipTrivia
  let key ← untilDelimiter ','
  if key.isEmpty then
    throw "BibTeX entry has an empty citation key"
  expect ','
  let parsedFields ← fields closing []
  pure { kind, key, fields := parsedFields }

private partial def entries (accumulator : List Entry) : Parser (List Entry) := do
  skipTrivia
  match ← peek? with
  | none => pure accumulator.reverse
  | some '@' =>
      let parsed ← entry
      if accumulator.any (·.key == parsed.key) then
        throw s!"duplicate BibTeX citation key '{parsed.key}'"
      entries (parsed :: accumulator)
  | some char => throw s!"expected '@' at the start of a BibTeX entry, found '{char}'"

/-- Parse a BibTeX database containing braced, quoted, bare, and concatenated field values. -/
def parse (source : String) : Except String (List Entry) :=
  (entries []).run source.toList |>.map Prod.fst

private def Entry.field? (entry : Entry) (name : String) : Option String :=
  entry.fields.find? (fun field => field.1 == normalizedName name) |>.map Prod.snd

private def Entry.field (entry : Entry) (name : String) : Except String String :=
  match entry.field? name with
  | some value => pure value
  | none => throw s!"BibTeX entry '{entry.key}' lacks required field '{name}'"

private def parseNat (entry : Entry) (fieldName value : String) : Except String Nat :=
  match (trim value).toNat? with
  | some parsed => pure parsed
  | none => throw s!"BibTeX entry '{entry.key}' has invalid {fieldName} '{value}'"

private def parseYear (entry : Entry) : Except String Int := do
  pure (Int.ofNat (← parseNat entry "year" (← entry.field "year")))

private def parsePages (entry : Entry) (value : String) : Except String (Nat × Nat) := do
  let parts := (value.replace "--" "-").splitOn "-"
  match parts with
  | [first, last] =>
      pure (
        ← parseNat entry "page" first,
        ← parseNat entry "page" last
      )
  | _ => throw s!"BibTeX entry '{entry.key}' has invalid pages '{value}'"

private def parseNames (value : String) : Array String :=
  (value.splitOn " and ").map trim |>.filter (· != "") |>.toArray

private def liftExcept : Except String α → CommandElabM α
  | .ok value => pure value
  | .error message => throwError message

private def inlineTerm (value : String) : CommandElabM (TSyntax `term) :=
  `(Verso.Doc.Inline.text $(quote value))

private def inlineArrayTerm (values : Array String) : CommandElabM (TSyntax `term) := do
  let terms ← values.mapM inlineTerm
  `(#[$terms,*])

private def optionalInlineTerm (value : Option String) : CommandElabM (TSyntax `term) :=
  match value with
  | none => `(none)
  | some value => do
      let term ← inlineTerm value
      `(some $term)

private def optionalInlineArrayTerm (value : Option (Array String)) :
    CommandElabM (TSyntax `term) :=
  match value with
  | none => `(none)
  | some values => do
      let term ← inlineArrayTerm values
      `(some $term)

private def Entry.url? (entry : Entry) : Option String :=
  entry.field? "url" <|> (entry.field? "doi").map (fun doi => s!"https://doi.org/{doi}")

private def articleTerm (entry : Entry) : CommandElabM (TSyntax `term) := do
  let title ← inlineTerm (← liftExcept (entry.field "title"))
  let authors ← inlineArrayTerm (parseNames (← liftExcept (entry.field "author")))
  let journal ← inlineTerm (← liftExcept (entry.field "journal"))
  let year ← liftExcept (parseYear entry)
  let month ← optionalInlineTerm (entry.field? "month")
  let volume ← inlineTerm (entry.field? "volume" |>.getD "")
  let number ← inlineTerm (entry.field? "number" |>.getD "")
  let pages ← liftExcept (entry.field? "pages" |>.mapM (parsePages entry))
  let url := entry.url?
  `(Verso.Genre.Manual.Bibliography.Citable.article {
      title := $title
      authors := $authors
      journal := $journal
      year := $(quote year)
      month := $month
      volume := $volume
      number := $number
      pages := $(quote pages)
      url := $(quote url)
    })

private def proceedingsTerm (entry : Entry) : CommandElabM (TSyntax `term) := do
  let title ← inlineTerm (← liftExcept (entry.field "title"))
  let authors ← inlineArrayTerm (parseNames (← liftExcept (entry.field "author")))
  let year ← liftExcept (parseYear entry)
  let booktitle ← inlineTerm (← liftExcept (entry.field "booktitle"))
  let editors ← optionalInlineArrayTerm (entry.field? "editor" |>.map parseNames)
  let series ← optionalInlineTerm (entry.field? "series")
  let url := entry.url?
  `(Verso.Genre.Manual.Bibliography.Citable.inProceedings {
      title := $title
      authors := $authors
      year := $(quote year)
      booktitle := $booktitle
      editors := $editors
      series := $series
      url := $(quote url)
    })

private def bookTerm (entry : Entry) : CommandElabM (TSyntax `term) := do
  let title ← inlineTerm (← liftExcept (entry.field "title"))
  let authors ← inlineArrayTerm (parseNames (← liftExcept (entry.field "author")))
  let year ← liftExcept (parseYear entry)
  let booktitle ← inlineTerm (← liftExcept (entry.field "publisher"))
  let seriesValue :=
    match entry.field? "series", entry.field? "volume" with
    | some series, some volume => some s!"{series}, vol. {volume}"
    | some series, none => some series
    | none, some volume => some s!"vol. {volume}"
    | none, none => none
  let series ← optionalInlineTerm seriesValue
  let url := entry.url?
  `(Verso.Genre.Manual.Bibliography.Citable.inProceedings {
      title := $title
      authors := $authors
      year := $(quote year)
      booktitle := $booktitle
      editors := none
      series := $series
      url := $(quote url)
    })

private def citableTerm (entry : Entry) : CommandElabM (TSyntax `term) :=
  match entry.kind with
  | "article" => articleTerm entry
  | "incollection" | "inproceedings" => proceedingsTerm entry
  | "book" => bookTerm entry
  | other => throwError s!"unsupported BibTeX entry type '@{other}' for '{entry.key}'"

syntax (name := loadBibTeX) "load_bibtex " str : command

/--
Parse a `.bib` file relative to the current Lean source and register every entry as a Verso
bibliography declaration. Citation keys must be valid Lean declaration names.
-/
elab_rules : command
  | `(load_bibtex $path:str) => do
      let sourcePath := System.FilePath.mk (← getFileName)
      let some sourceDirectory := sourcePath.parent
        | throwError "cannot determine the directory of '{sourcePath}'"
      let bibliographyPath := sourceDirectory / path.getString
      let source ← IO.FS.readFile bibliographyPath
      let parsed ←
        match parse source with
        | .ok parsed => pure parsed
        | .error message => throwError s!"{bibliographyPath}: {message}"
      for parsedEntry in parsed do
        let declarationName := parsedEntry.key.toName
        if declarationName.isAnonymous then
          throwError s!"invalid BibTeX citation key '{parsedEntry.key}'"
        let declaration ← citableTerm parsedEntry
        let command ←
          `(@[bib $(quote parsedEntry.key)]
            def $(mkIdent declarationName) : Citable := $declaration)
        elabCommand command

end ProbabilityApproximationBlueprint.BibTeX
