/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import VersoManual
import VersoBlueprint.PreviewManifest
import RokickiBlueprint

/-!
Generator entry point for the Verso blueprint. `lake exe vbp build` discovers this file and runs it;
see `blueprint/README.md`.
-/

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc RokickiBlueprint)
    args
    (extensionImpls := by exact extension_impls%)
