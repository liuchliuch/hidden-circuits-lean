import HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetupFront
import HiddenCircuits.Approximation.SelfReduction.Runtime.CountSetupGuard
import HiddenCircuits.Approximation.SamplerRuntime.GraphParserProgram

/-! The graph counter shares the actual raw request parser and tape guard. -/
namespace HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
export CountSetup (request coins graph size front frontInput frontOutput front_executes front_queryFree
  request_pair coins_pair graph_estimate size_pair canonical_precision_bounds
  tapeGuard guardStore tapeGuard_executes tapeGuard_queryFree)
end HiddenCircuits.Approximation.SelfReduction.Runtime.GraphCountSetup
