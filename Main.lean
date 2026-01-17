def main := do
  IO.println "Hello world"
  IO.println "Input something:"
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  IO.println s!"You typed {input}"
