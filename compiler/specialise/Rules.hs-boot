module Rules (
    RuleBase,
    mkSpecInfo,
    mkRuleBase,
    extendRuleBaseList
    ) where

import CoreSyn (CoreRule)
import NameEnv (NameEnv)
import IdInfo (SpecInfo)

type RuleBase = NameEnv [CoreRule]

-- For MkId
mkSpecInfo :: [CoreRule] -> SpecInfo

-- For LoadIface
mkRuleBase :: [CoreRule] -> RuleBase
extendRuleBaseList :: RuleBase -> [CoreRule] -> RuleBase
