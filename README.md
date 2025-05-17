# Formalising TPOD in Isabelle/HOL

This repository contains a formalisation of Cheang et al.'s TPOD in Isabelle/HOL.

## Requirements 

These theories have been tested with [Isabelle/HOL 2025](https://isabelle.in.tum.de/installation.html) and the latest [AFP](https://www.isa-afp.org/).

You will need to build this project's dependencies: [IsaBIL](https://github.com/matt-j-griffin/isabil).

## Edits to the AFP

Both Relative Security and BD Security use theories named `Trivia`. 
Isabelle/HOL cannot handle two theories with the same name, even if they are in the same session.
The exact exception is:

```
exception THEORY raised (line 378 of "context.ML"):
  Duplicate theory name
```

To fix this you will need to make edits to the AFP. The file that needs to be renamed is:
```
mv <afp-dir>/thys/Relative_Security/Preliminaries/Trivia <afp-dir>/thys/Relative_Security/Preliminaries/RS_Trivia`
```

You will also need to open these files and change their names.

Next, remove the reference to `Trivia` in `Relative_Security/Relative_Security`, the reference is not needed.
Finally, open `Relative_Security/ROOT` and change `Trivia` to `RS_Trivia`.




You will also need to open `<afp-dir>/thys/Relative_Security/Preliminaries/Transistion_System` and change the imports line from `imports Trivia` to `imports RS_Trivia`.

## Installation

Build in the root of the repository (where `ROOT` file is located) using `isabelle build -D .`.

To use these theories in your own work, add this repository to Isabelle: `isabelle components -u .`.
