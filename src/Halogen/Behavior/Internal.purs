module Halogen.Behavior.Internal where

import Prelude

import CSS (CSS, render, renderedInline)
import Effect (Effect)
import Effect.Ref (Ref, new, read)
import Data.Function.Uncurried as Fn
import Effect.Uncurried as EFn
import Data.Maybe (Maybe(..))
import Record (insert)
import Web.DOM (Element)
import Data.Symbol (class IsSymbol, SProxy(..))
import Halogen.HTML.Core (class IsProp, PropValue, toPropValue)
import Halogen.HTML.Properties (IProp(..))
import Halogen.VDom.Util as Util
import Type.RowList (class ListToRow, RLProxy(..))
import Prim.Row (class Union, class Lacks, class Cons)
import Prim.RowList (kind RowList, Cons, Nil, class RowToList)
import Unsafe.Coerce (unsafeCoerce)
import Unsafe.Reference (unsafeRefEq)
import Foreign (typeOf)

renderCSS :: CSS -> Maybe String
renderCSS = renderedInline <<< render

mapIProp :: forall attrs a b. (a -> b) -> IProp attrs a -> IProp attrs b
mapIProp f (IProp p) = IProp (map f <$> p)

expandAttr ::
  forall attrs attrs' extra.
    Union attrs extra attrs' =>
  IProp attrs ~> IProp attrs'
expandAttr = unsafeCoerce

expandAttrs ::
  forall attrs attrs' extra a.
    Union attrs extra attrs' =>
  Array (IProp attrs a) -> Array (IProp attrs' a)
expandAttrs = unsafeCoerce

eqProp :: forall p. IsProp p => p -> p -> Boolean
eqProp a b = unsafeRefEq (toPropValue a) (toPropValue b)

eqMProp :: forall p. IsProp p => Maybe p -> Maybe p -> Boolean
eqMProp (Just p1) (Just p2) = eqProp p1 p2
eqMProp Nothing Nothing = true
eqMProp _ _ = false

class Nothings (row :: # Type) where
  aWholeLotOfNothing :: Record row
class (RowToList row rl, ListToRow rl row) <= NothingsRL (rl :: RowList) (row :: # Type) | rl -> row where
  aWholeLotOfNothingRL :: RLProxy rl -> Record row
instance nothingsImpl :: (RowToList row rl, ListToRow rl row, NothingsRL rl row) => Nothings row where
  aWholeLotOfNothing = aWholeLotOfNothingRL (RLProxy :: RLProxy rl)
instance nothingsNil :: NothingsRL Nil () where
  aWholeLotOfNothingRL _ = {}
instance nothingsCons ::
  ( IsSymbol label
  , Cons label (Maybe ty) row' row
  , Lacks label row'
  , RowToList row (Cons label (Maybe ty) rl)
  , NothingsRL rl row'
  ) => NothingsRL (Cons label (Maybe ty) rl) row where
    aWholeLotOfNothingRL _ = insert (SProxy :: SProxy label) Nothing
      (aWholeLotOfNothingRL (RLProxy :: RLProxy rl) :: Record row')

-- allow mutation in ref?
newtype AroundState partial = AroundState
  { insideState :: Record partial
  , outsideState :: Maybe (Ref (Record partial))
  }

uninitializedAS :: forall partial. Nothings partial => AroundState partial
uninitializedAS = AroundState { insideState: aWholeLotOfNothing, outsideState: Nothing }

initialize :: forall partial. AroundState partial -> Effect (AroundState partial)
initialize (AroundState { insideState }) =
  new insideState <#>
    AroundState <<< { insideState, outsideState: _ } <<< Just

snapshot :: forall partial. AroundState partial -> Effect (AroundState partial)
snapshot a@(AroundState { outsideState: Nothing }) = pure a
snapshot (AroundState { outsideState: Just ref }) =
  read ref <#> \insideState ->
    AroundState { insideState, outsideState: Just ref }


setProperty ∷ EFn.EffectFn3 String PropValue Element Unit
setProperty = Util.unsafeSetAny

unsafeGetProperty ∷ EFn.EffectFn2 String Element PropValue
unsafeGetProperty = EFn.mkEffectFn2 \key el ->
  pure (Fn.runFn2 Util.unsafeGetAny key el)

removeProperty ∷ EFn.EffectFn2 String Element Unit
removeProperty = EFn.mkEffectFn2 \key el →
  case typeOf (Fn.runFn2 Util.unsafeGetAny key el) of
    "string" → EFn.runEffectFn3 Util.unsafeSetAny key "" el
    _        → EFn.runEffectFn3 Util.unsafeSetAny key Util.jsUndefined el
