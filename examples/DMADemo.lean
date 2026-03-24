import Radix.DMA.Ops

/-!
# Example: DMA Transfer
-/

namespace Examples.DMADemo

def main : IO Unit := do
  IO.println "━━━ DMA Example ━━━"
  let descriptor : Radix.DMA.Descriptor :=
    { source := { start := 0, size := 4 }
    , destination := { start := 4, size := 4 }
    , order := .seqCst
    , coherence := .nonCoherent
    , atomicity := .burst 2
    }
  IO.println s!"  Valid: {Radix.DMA.isValid descriptor}"
  IO.println s!"  Burst bytes: {Radix.DMA.burstBytes descriptor}"
  IO.println s!"  Steps: {Radix.DMA.stepCount descriptor}"
  let src := ByteArray.mk #[1, 2, 3, 4, 9, 9, 9, 9]
  let dst := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0]
  IO.println s!"  Can simulate: {Radix.DMA.canSimulate src dst descriptor}"
  match Radix.DMA.simulateSteps src dst descriptor with
  | some steps =>
      IO.println s!"  Visible steps: {(Array.toList steps).map ByteArray.toList}"
  | none =>
      IO.println "  Visible steps: simulation unavailable"
  match Radix.DMA.simulateCopy src dst descriptor with
  | some bytes => IO.println s!"  Destination: {bytes.toList}"
  | none => throw (IO.userError "DMA simulation failed")

end Examples.DMADemo
