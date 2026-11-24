import EinsteinpyLean.Utils.DualDiff
import EinsteinpyLean.Utils.ConstDiff

/-! The `epdiff` handlers of the Utils area. -/

namespace EinsteinpyLean.Utils

def handlers : List (String × Handler) := dualHandlers ++ constHandlers

end EinsteinpyLean.Utils
