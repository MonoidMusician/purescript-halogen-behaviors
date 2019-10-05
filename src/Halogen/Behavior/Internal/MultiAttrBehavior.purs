module Halogen.Behavior.Internal.MultiAttrBehavior where

import Prelude

import Effect (Effect)
import Effect.Ref (Ref, modify_, read)
import Effect.Uncurried as EFn
import Data.Maybe (Maybe(..))
import Record (delete, get, set)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Data.Variant (Variant, case_, expand, inj, on)
import FRP.Behavior (ABehavior, Behavior, animate)
import FRP.Event (Event)
import Halogen.Behavior.Internal (class Nothings, class NothingsRL, eqMProp, removeProperty, setProperty)
import Halogen.HTML (class IsProp)
import Halogen.HTML.Core (Prop(..), toPropValue)
import Halogen.HTML.Properties (IProp(..))
import Type.Row (RProxy(..))
import Type.RowList (class ListToRow, RLProxy(..))
import Prim.Row (class Union, class Lacks, class Cons)
import Prim.RowList (kind RowList, Cons, Nil, class RowToList)
import Web.DOM (Element)
import Unsafe.Coerce (unsafeCoerce)

type SubscribeCancel v = (v -> Effect Unit) -> Effect (Effect Unit)

class Nothings partial <= MultiAttrBehavior
  (required :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | required -> partial behaviors
  , partial -> required behaviors
  where
    subscribe :: forall e. Record behaviors -> SubscribeCancel (Variant partial)
    handle :: forall e. Element -> Variant partial -> Effect Unit
    toProps :: forall i. Record partial -> Array (IProp required i)
    shouldUpdate :: forall e. Ref (Record partial) -> Variant partial -> Effect Boolean
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
    subscribeRL :: RLProxy arl -> Record behaviors -> SubscribeCancel (Variant partial)
    handleRL :: RLProxy arl -> Element -> Variant partial -> Effect Unit
    toPropsRL :: forall i. RLProxy arl -> Record partial -> Array (IProp required i)
    shouldUpdateRL :: RLProxy arl -> Ref (Record partial) -> Variant partial -> Effect Boolean
instance mabNil :: MultiAttrBehaviorRL Nil Nil Nil () () () where
  subscribeRL _ {} cb = pure (pure unit)
  handleRL _ _ = case_
  toPropsRL _ {} = []
  shouldUpdateRL _ _ = case_
instance mabCons ::
  ( IsSymbol label
  , IsProp p
  , Lacks label required'
  , Lacks label partial'
  , Lacks label behaviors'
  , Cons label p required' required
  , Cons label (Maybe p) partial' partial
  , Cons label (Behavior (Maybe p)) behaviors' behaviors
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
          Just v -> EFn.runEffectFn3 setProperty propName (toPropValue v) el
          Nothing -> EFn.runEffectFn2 removeProperty propName el
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
            rec <- read ref
            if get k rec `eqMProp` v
              then pure false
              else do
                modify_ (set k v) ref
                pure true
          handleOther = unsafeCoerce (shouldUpdateRL (RLProxy :: RLProxy arl)) ref
