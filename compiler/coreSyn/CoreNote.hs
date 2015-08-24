module CoreNote ( annotateCoreNotes ) where

import CoreSyn

-- | Add Core ticks to a Core expression.
--
-- The generated Core should satisfy the CorePrep invariants.
annotateCoreNotes :: CoreBind -> CoreBind
annotateCoreNotes = go_bs
  where go (App e a)        = App (go e) (go a)
        go (Lam b e)        = Lam b (go e)
        go (Let b e)        = Let (go_bs b) (go e)
        go (Case e b t as)  = Case (go e) b t (map (go_a b) as)
        go (Cast e c)       = Cast (go e) c
        go (Tick t e)       = Tick t (go e)
        go other            = other
        go_bs (NonRec b e)  = NonRec b $ tick_bind b e $ go e
        go_bs (Rec bs)      = Rec $ map go_b bs
        go_b (b, e)         = (b, tick_bind b e $ go e)
        go_a b alt@(c,bs,e) = (c, bs, Tick (CoreNote b (AltPtr alt)) $ go e)
        -- When ticking let bindings, we want to move the Core note
        -- inside lambdas in order to fulfill CorePrep invariants
        tick_bind b e (Lam b' e') = Lam b' (tick_bind b e e')
        tick_bind b e (Tick t e') | tickishFloatable t
                                  = Tick t (tick_bind b e e')
        tick_bind b e (Cast e' c) = Cast (tick_bind b e e') c
        tick_bind b e e'          = Tick (CoreNote b (ExprPtr e)) e'
