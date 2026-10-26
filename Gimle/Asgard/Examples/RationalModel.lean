module

public import Gimle.Asgard.Model.Driven
public import Gimle.Asgard.Compile.Syntax

@[expose] public section

namespace Gimle.Asgard.Examples.RationalModel
open _root_.Gimle.Asgard.Polynomial Model

/-- x' = y/3, y' = -2x/7. The input declaration order differs from state order;
observations [y,x] deliberately reuse state display names with distinct IDs. -/
def body : Body := {
  program := ⟨[⟨"state-y", "y", .state⟩, ⟨"param-a", "a", .parameter⟩,
    ⟨"state-x", "x", .state⟩], equations% { dx := a*y; dy := -rat(2,7)*x; }⟩
  parameters := [⟨"param-a", 1/3⟩]
  observations := [⟨⟨"obs-y", "y", .output⟩, "state-y"⟩,
    ⟨⟨"obs-x", "x", .output⟩, "state-x"⟩]
}
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩]
  initialPorts := [⟨"initial-y", "y0", .initial⟩, ⟨"initial-x", "x0", .initial⟩]
  initialValues := [⟨"initial-y", -2⟩, ⟨"initial-x", 1/2⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 2/3
}
def model : ContinuousModel body evolution :=
  (compileContinuous body evolution).toOption.get (by decide +kernel)

end Gimle.Asgard.Examples.RationalModel
