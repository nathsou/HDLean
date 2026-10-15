import Designs.SkidBuffer.Spec
import HDLean.Core.Network

namespace HDLean.SkidBuffer

/-- Each instance exposes ready, valid, and little-endian payload. Payload is
observed only when valid; the final stage is the pipeline consumer interface. -/
def observePipeline (ports : Fin (3 * (w + 2)) → Bool) :
    Fin 3 → Fifo.Output (Vector Bool w) :=
  fun j => Fifo.observe (Circuit.unpack ports j)

end HDLean.SkidBuffer
