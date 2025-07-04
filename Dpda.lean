-- This module serves as the root of the `Dpda` library.
-- Import modules here that should be built as part of the library.
import Dpda.RepeatBindMap
import Dpda.AugmentSingleton
import Dpda.WobblyFn
import Dpda.Testcases

/- Definitions -/

-- Textbook definitions
import Dpda.Definition.Hopcroft
import Dpda.Definition.Sipser

-- My definitions
import Dpda.Definition.PushOrPop1
import Dpda.Definition.PushOrPop2
import Dpda.Definition.Le1PopLe1Push
import Dpda.Definition.CharPopStringPush
import Dpda.Definition.PredeterminedToPushOrPop



/- Conversions (Also see overview.png) -/

-- The core cycle of transformations
import Dpda.Conversion.PredetToPP
import Dpda.Conversion.PP1ToPP2
import Dpda.Conversion.PP2ToLe1P2
import Dpda.Conversion.Le1P2ToCPSP
import Dpda.Conversion.CPSPToPredet


-- Out-of-cycle conversions
import Dpda.Conversion.CPSPToHopcroft
import Dpda.Conversion.HopcroftToCPSP

import Dpda.Conversion.Le1P2ToSipser
