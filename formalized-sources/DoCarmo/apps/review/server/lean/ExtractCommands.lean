import Lean

/-!
Parser-only Lean command extractor for the review app.

This tool intentionally parses source syntax without elaborating imports. It gives
the TypeScript review server Lean-accurate top-level command boundaries while
remaining fast enough for local review-page source rendering.
-/

open Lean

def commandText? (source : String) (stx : Syntax) :
    Option (String × Position × Position) := do
  let range ← stx.getRange?
  let fileMap := source.toFileMap
  let text := (source.toRawSubstring.extract range.start range.stop).toString
  return (text, fileMap.toPosition range.start, fileMap.toPosition range.stop)

def namespaceName? (text : String) : Option String :=
  let trimmed := text.trimAscii.toString
  if trimmed.startsWith "namespace " then
    some (trimmed.drop "namespace ".length).trimAscii.toString
  else
    none

def endName? (text : String) : Option String :=
  let trimmed := text.trimAscii.toString
  if trimmed == "end" then
    some ""
  else if trimmed.startsWith "end " then
    some (trimmed.drop "end ".length).trimAscii.toString
  else
    none

def popNamespace (namespaces : Array String) (name : String) : Array String :=
  if namespaces.isEmpty then
    namespaces
  else if name.isEmpty || namespaces.back! == name then
    namespaces.pop
  else
    namespaces.pop

def commandJson
    (kind : String)
    (namespaces : Array String)
    (text : String)
    (startPos : Position)
    (endPos : Position) : Json :=
  Json.mkObj [
    ("kind", Json.str kind),
    ("namespaces", Json.arr (namespaces.map Json.str)),
    ("startLine", Json.num startPos.line),
    ("startColumn", Json.num startPos.column),
    ("endLine", Json.num endPos.line),
    ("endColumn", Json.num endPos.column),
    ("text", Json.str text)
  ]

partial def parseCommands
    (inputCtx : Parser.InputContext)
    (env : Environment)
    (state : Parser.ModuleParserState)
    (messages : MessageLog)
    (namespaces : Array String)
    (entries : Array Json) : IO (Array Json) := do
  let (stx, nextState, nextMessages) :=
    Parser.parseCommand inputCtx { env := env, options := {} } state messages
  if Parser.isTerminalCommand stx then
    return entries

  let kind := stx.getKind.toString
  let (entries, namespaces) :=
    match commandText? inputCtx.inputString stx with
    | none => (entries, namespaces)
    | some (text, startPos, endPos) =>
        let entries := entries.push (commandJson kind namespaces text startPos endPos)
        let namespaces :=
          match namespaceName? text with
          | some name => namespaces.push name
          | none =>
              match endName? text with
              | some name => popNamespace namespaces name
              | none => namespaces
        (entries, namespaces)
  parseCommands inputCtx env nextState nextMessages namespaces entries

unsafe def main (args : List String) : IO UInt32 := do
  let fileName ←
    match args with
    | [fileName] => pure fileName
    | _ =>
        IO.eprintln "usage: ExtractCommands <file.lean>"
        return 2
  let source ← IO.FS.readFile fileName
  let inputCtx := Parser.mkInputContext source fileName
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{ module := `Lean }] {}
  let (_, state, messages) ← Parser.parseHeader inputCtx
  let entries ← parseCommands inputCtx env state messages #[] #[]
  IO.println (Json.arr entries).compress
  return 0
