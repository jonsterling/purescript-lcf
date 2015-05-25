module LCF
( Validation()
, ProofState()
, Tactic(..)
, runTactic

, AdditiveTactic(..)
, getAdditiveTactic

, lazyThenLT
, lazyThenT
, thenLT
, thenT
, idT
, lazyOrElseT
, orElseT
, failT

, tryT
, repeatT

, notT
, impliesT
) where

import Control.Monad.Eff
import Control.Monad.Eff.Exception
import Data.Either
import Data.List
import Data.Monoid
import Data.Traversable
import Data.Tuple
import Data.Lazy

-- | A `Validation d e` constructs a proof/derivation `d` from the proofs of its subgoals.
type Validation d e = List d -> Eff (err :: Exception | e) d

-- | A `ProofState j d e` is a list of subgoals (judgements `j`) and a validation.
type ProofState j d e = { subgoals :: List j, validation :: Validation d e }

-- | A `Tactic j d e` is a strategy for constructing a proof in `d` of a judgement in `j` by transforming the proof state.
newtype Tactic j d e = Tactic (j -> Eff (err :: Exception | e) (ProofState j d e))

runTactic :: forall j d e. Tactic j d e -> j -> Eff (err :: Exception | e) (ProofState j d e)
runTactic (Tactic t) = t

splitAt :: forall a e. Number -> List a -> Eff (err :: Exception | e) (Tuple (List a) (List a))
splitAt n ls =
  if n < 0
    then throwException $ error "splitAt: negative index"
    else if n == 0
      then pure $ Tuple Nil ls
      else pure $ go n ls
  where
    go _ Nil = Tuple Nil Nil
    go 1 (Cons x xs) = Tuple (Cons x Nil) xs
    go m (Cons x xs) =
      case go (m - 1) xs of
        Tuple xs' xs'' -> Tuple (Cons x xs') xs''

mapShape :: forall a b e. List Number -> List (List a -> Eff (err :: Exception | e) b) -> List a -> Eff (err :: Exception | e) (List b)
mapShape Nil _ _ = pure Nil
mapShape (Cons n ns) (Cons f fs) xs = do
  Tuple ys zs <- splitAt n xs
  Cons <$> f ys <*> mapShape ns fs zs

refine :: forall j d e. Validation d e -> List (List j) -> List (Validation d e) -> ProofState j d e
refine v subgoals vs =
  { subgoals : subgoals >>= id
  , validation : \ds -> mapShape (length <$> subgoals) vs ds >>= v
  }

-- | The identity tactic has no effect on the proof state.
idT :: forall j d e. Tactic j d e
idT = Tactic \j -> pure
  { subgoals: Cons j Nil
  , validation: \ds ->
      case ds of
        Cons d Nil -> pure d
        _ -> throwException $ error "idTac: Wrong number of subderivations"
  }

unzipProofStates :: forall j d e. List (ProofState j d e) -> Tuple (List (List j)) (List (Validation  d e))
unzipProofStates = go $ Tuple Nil Nil
  where
    go r Nil = r
    go (Tuple jss vs) (Cons s ss) = go (Tuple (Cons s.subgoals jss) (Cons s.validation vs)) ss

-- | `lazyThenLT t ts` applies the tactics `ts` pointwise to the subgoals generated by the tactic `t`.
lazyThenLT :: forall j d e. Tactic j d e -> Lazy [Tactic j d e] -> Tactic j d e
lazyThenLT t1 ts = Tactic \j -> do
  state1 <- t1 `runTactic` j
  if null state1.subgoals then pure state1 else do
    states <- sequence $ (runTactic <$> fromArray (force ts)) <*> state1.subgoals
    case unzipProofStates states of
       Tuple subgoals validations ->
         pure $ refine state1.validation subgoals validations

-- | `lazyThenT t1 t2` applies the tactic `t2` to each of the subgoals generated by the tactic `t`.
lazyThenT :: forall j d e. Tactic j d e -> Lazy (Tactic j d e) -> Tactic j d e
lazyThenT t1 t2l = Tactic \j -> do
  state1 <- t1 `runTactic` j
  if null state1.subgoals then pure state1 else do
    states <- traverse (runTactic $ force t2l) state1.subgoals
    case unzipProofStates states of
       Tuple subgoals validations ->
         pure $ refine state1.validation subgoals validations

-- | `thenLT t ts` applies the tactics `ts` pointwise to the subgoals generated by the tactic `t`.
thenLT :: forall j d e. Tactic j d e -> [Tactic j d e] -> Tactic j d e
thenLT t1 ts = lazyThenLT t1 $ pure ts

-- | `thenT t1 t2` applies the tactic `t2` to each of the subgoals generated by the tactic `t`.
thenT :: forall j d e. Tactic j d e -> Tactic j d e -> Tactic j d e
thenT t1 t2 = lazyThenT t1 $ pure t2

-- | Tactics form a semigroup via the `thenT` tactical.
instance semigroupTactic :: Semigroup (Tactic j d e) where
  (<>) = thenT

-- | Tactics form a monoid via the `idT` tactic, which is the unit of `thenT`.
instance monoidTactic :: Monoid (Tactic j d e) where
  mempty = idT

-- A weird hack.
foreign import catchException'
   """
   function catchException(c) {
     return function(t) {
       return function() {
         try {
           return t();
         } catch(e) {
            if (e instanceof Error || Object.prototype.toString.call(e) === '[object Error]') {
              return c(e)();
            } else {
              return c(new Error(e.toString()))();
            }
           }
        };
     };
   }
   """ :: forall a eff. (Error -> Eff (err :: Exception | eff) a) -> Eff (err :: Exception | eff) a -> Eff (err :: Exception | eff) a

-- | `lazyOrElseT` t1 t2` first tries `t1`, and if it fails, then tries `t2`.
lazyOrElseT :: forall j d e. Tactic j d e -> Lazy (Tactic j d e) -> Tactic j d e
lazyOrElseT t1 t2 = Tactic \j ->
  catchException' (\_ -> force t2 `runTactic` j) $ t1 `runTactic` j

-- | `orElseT` t1 t2` first tries `t1`, and if it fails, then tries `t2`.
orElseT :: forall j d e. Tactic j d e -> Tactic j d e -> Tactic j d e
orElseT t1 t2 = lazyOrElseT t1 $ pure t2

-- | `failT` always fails.
failT :: forall j d e. Tactic j d e
failT = Tactic \j -> throwException $ error "failT"

-- | `tryT` either succeeds, or does nothing.
tryT :: forall j d e. Tactic j d e -> Tactic j d e
tryT t = orElseT t idT

-- | `repeatT` repeats a tactic for as long as it succeeds. `repeatT` never fails.
repeatT :: forall j d e. Tactic j d e -> Tactic j d e
repeatT t = tryT $ t `lazyThenT` defer \_ -> tryT $ repeatT t

-- | Succeeds if the tactic fails; fails if the tactic succeeds.
notT :: forall j d e. Tactic j d e -> Tactic j d e
notT t = Tactic \j -> do
  res <- catchException' (\_ -> Left <$> (idT `runTactic` j)) $ (Right <$> t `runTactic` j)
  case res of
    Left st -> pure st
    Right st -> throwException $ error "notT"

-- | Classical "implication" of tactics: either the left tactic fails, or the right tactic succeeds. Note: I am not sure if this is useful at all, but it seemed interesting it was definable.
impliesT :: forall j d e. Tactic j d e -> Tactic j d e -> Tactic j d e
impliesT t1 t2 = notT t1 `orElseT` t2

-- | The tactics also give rise to another semigroup and monoid structure, given by disjunction and failure.
newtype AdditiveTactic j d e = AdditiveTactic (Tactic j d e)

getAdditiveTactic :: forall j d e. AdditiveTactic j d e -> Tactic j d e
getAdditiveTactic (AdditiveTactic t) = t

-- | The semigroup operation is given by `orElseT`.
instance semigroupAdditiveTactic :: Semigroup (AdditiveTactic j d e) where
  (<>) (AdditiveTactic t1) (AdditiveTactic t2) = AdditiveTactic $ orElseT t1 t2

-- | The monoid arises from the `failT` tactic, which is the unit of `orElseT`.
instance monoidAdditiveTactic :: Monoid (AdditiveTactic j d e) where
  mempty = AdditiveTactic failT
