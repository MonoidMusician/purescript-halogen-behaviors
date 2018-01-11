module Halogen.Behavior.Internal.MultiAttrBehavior where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Ref (REF, Ref, modifyRef, readRef)
import DOM (DOM)
import DOM.Node.Types (Element)
import Data.Function.Uncurried as Fn
import Data.Maybe (Maybe(..))
import Data.Record (delete, get, set)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Data.Variant (Variant, case_, expand, inj, on)
import FRP (FRP)
import FRP.Behavior (ABehavior, Behavior, animate)
import FRP.Event (Event)
import Halogen.Behavior.Internal (class Nothings, class NothingsRL, eqMProp, removeProperty, setProperty)
import Halogen.HTML (class IsProp)
import Halogen.HTML.Core (Prop(..), toPropValue)
import Halogen.HTML.Properties (IProp(..))
import Type.Row (class ListToRow, class RowLacks, class RowToList, Cons, Nil, RLProxy(..), kind RowList)
import Unsafe.Coerce (unsafeCoerce)

type SubscribeCancel eff v = (v -> Eff eff Unit) -> Eff eff (Eff eff Unit)

class Nothings partial <= MultiAttrBehavior
  (required :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | required -> partial behaviors
  , partial -> required behaviors
  where
    subscribe :: forall e. Record behaviors -> SubscribeCancel ( frp :: FRP | e ) (Variant partial)
    handle :: forall e. Element -> Variant partial -> Eff ( dom :: DOM | e ) Unit
    toProps :: forall i. Record partial -> Array (IProp required i)
    shouldUpdate :: forall e. Ref (Record partial) -> Variant partial -> Eff ( ref :: REF | e ) Boolean
instance mab ::
  -- Use both RowToList and ListToRow for inference purposes
  ( RowToList required arl
  , ListToRow arl required
  , RowToList partial prl
  , ListToRow prl partial
  , RowToList behaviors brl
  , ListToRow brl behaviors
  , NothingsRL prl partial
  , MultiAttrBehaviorRL arl prl brl required partial behaviors
  ) => MultiAttrBehavior required partial behaviors where
    subscribe = subscribeRL (RLProxy :: RLProxy arl)
    handle = handleRL (RLProxy :: RLProxy arl)
    toProps = toPropsRL (RLProxy :: RLProxy arl)
    shouldUpdate = shouldUpdateRL (RLProxy :: RLProxy arl)

class
  ( NothingsRL prl partial
  , RowToList required arl, ListToRow arl required
  , RowToList behaviors brl -- , ListToRow brl behaviors
  ) <= MultiAttrBehaviorRL
  (arl :: RowList)
  (prl :: RowList)
  (brl :: RowList)
  (required :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | arl -> required
  , prl -> partial
  , brl -> behaviors
  , arl -> prl brl
  , prl -> arl brl
  , brl -> arl prl
  where
    subscribeRL :: forall e. RLProxy arl -> Record behaviors -> SubscribeCancel ( frp :: FRP | e ) (Variant partial)
    handleRL :: forall e. RLProxy arl -> Element -> Variant partial -> Eff ( dom :: DOM | e ) Unit
    toPropsRL :: forall i. RLProxy arl -> Record partial -> Array (IProp required i)
    shouldUpdateRL :: forall e. RLProxy arl -> Ref (Record partial) -> Variant partial -> Eff ( ref :: REF | e ) Boolean
instance mabNil :: MultiAttrBehaviorRL Nil Nil Nil () () () where
  subscribeRL _ {} cb = pure (pure unit)
  handleRL _ _ = case_
  toPropsRL _ {} = []
  shouldUpdateRL _ _ = case_
instance mabCons ::
  ( IsSymbol label
  , IsProp p
  , RowLacks label required'
  , RowLacks label partial'
  , RowLacks label behaviors'
  , RowCons label p required' required
  , RowCons label (Maybe p) partial' partial
  , RowCons label (Behavior (Maybe p)) behaviors' behaviors
  , Union partial' one partial
  , RowToList required (Cons label p arl)
  -- , ListToRow (Cons label p arl) required
  , RowToList partial (Cons label (Maybe p) prl)
  -- , ListToRow (Cons label (Maybe p) prl) partial
  , RowToList behaviors (Cons label (Behavior (Maybe p)) brl)
  -- , ListToRow (Cons label (Behavior (Maybe p)) brl) behaviors
  -- , Nothings partial
  -- , NothingsRL (Cons label (Maybe p) prl) partial
  , MultiAttrBehaviorRL arl prl brl required' partial' behaviors'
  ) => MultiAttrBehaviorRL
    (Cons label p arl)
    (Cons label (Maybe p) prl)
    (Cons label (ABehavior Event (Maybe p)) brl)
    required partial behaviors where
      subscribeRL _ r cb = do
        c1 <- subscribeRL (RLProxy :: RLProxy arl) (delete k r) (expand >>> cb)
        c2 <- animate (get k r) (inj k >>> cb)
        pure (c1 *> c2)
        where k = SProxy :: SProxy label
      handleRL _ el = handleRL (RLProxy :: RLProxy arl) el
        # on k case _ of
          Just v -> Fn.runFn3 setProperty propName (toPropValue v) el
          Nothing -> Fn.runFn2 removeProperty propName el
        where
          k = (SProxy :: SProxy label)
          propName = reflectSymbol k # case _ of
            "class" -> "className"
            "for" -> "htmlFor"
            n -> n
      toPropsRL _ r = case get k r of
        Nothing -> other
        Just v -> other <> [IProp (Property (reflectSymbol k) (toPropValue v))]
        where
          k = (SProxy :: SProxy label)
          exp = unsafeCoerce :: (forall i. Array (IProp required' i) -> Array (IProp required i))
          other = exp $ toPropsRL (RLProxy :: RLProxy arl) (delete k r)
      shouldUpdateRL _ ref = handleOther # on k handleThis
        where
          k = (SProxy :: SProxy label)
          handleThis = \v -> do
            rec <- readRef ref
            if get k rec `eqMProp` v
              then pure false
              else do
                modifyRef ref (set k v)
                pure true
          handleOther = unsafeCoerce (shouldUpdateRL (RLProxy :: RLProxy arl)) ref
