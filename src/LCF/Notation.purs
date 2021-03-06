module LCF.Notation
( (/\)
, (\/)
, (/\*)
, (~>)
) where

import LCF
import Data.List

-- | An abbreviation for `thenT`.
(/\) :: forall j d e. Tactic j d e -> Tactic j d e -> Tactic j d e
(/\) = thenT

infixr 7 /\

-- | An abbreviation for `orElseT`.
(\/) :: forall j d e. Tactic j d e -> Tactic j d e -> Tactic j d e
(\/) = orElseT

infixr 6 \/

-- | An abbreviation for `thenLT`.
(/\*) :: forall j d e. Tactic j d e -> [Tactic j d e] -> Tactic j d e
(/\*) = thenLT

-- | An abbreviation for `impliesT`.
(~>) :: forall j d e. Tactic j d e -> Tactic j d e -> Tactic j d e
(~>) = impliesT
