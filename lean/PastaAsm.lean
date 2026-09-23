/-
Copyright (c) 2026 the pasta-asm contributors.
Released under the Apache License, Version 2.0, as described in the file LICENSE.
-/
import PastaAsm.Semantics
import PastaAsm.Inversion
import PastaAsm.InversionSpec
import PastaAsm.InversionConvergence
import PastaAsm.InversionBatch
import PastaAsm.InversionRegularPrefix
import PastaAsm.InversionDivergenceBoundary
import PastaAsm.InversionFarLength
import PastaAsm.InversionNearLength
import PastaAsm.InversionNormalization
import PastaAsm.Fields
import PastaAsm.InversionFields
import PastaAsm.Compositions
import PastaAsm.Spec
import PastaAsm.AArch64
import PastaAsm.X86_64

/-!
# The pasta-asm routines, formalized

Generic arithmetic is defined in the top-level `PastaAsm` modules. Architecture-specific
transcriptions and proofs live under their corresponding namespaces.

Every module of the development is imported here, so that a build of this root builds all of
them and the nanoda re-check (`lean/scripts/check_nanoda.sh`) exports all of them.
-/
