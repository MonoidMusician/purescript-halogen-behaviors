module Halogen.Behavior where

import Prelude

import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.AVar (AVAR)
import Control.Monad.Eff.Ref (REF, Ref, newRef, readRef, writeRef)
import Control.Monad.Except (runExcept)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.MonadZero (guard)
import DOM (DOM)
import DOM.Event.Event (target)
import DOM.HTML.HTMLInputElement (value)
import DOM.HTML.Types (htmlElementToElement, readHTMLInputElement)
import DOM.Node.Types (Element)
import Data.Const (Const)
import Data.Foldable (for_)
import Data.Foreign (toForeign, typeOf)
import Data.Function.Uncurried as Fn
import Data.Int (even, round)
import Data.Maybe (Maybe(..))
import Data.Record (delete, get, insert)
import Data.Set (size)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant, case_, expand, inj, on)
import FRP (FRP)
import FRP.Behavior (Behavior, animate)
import FRP.Behavior.Mouse (buttons)
import FRP.Behavior.Time (seconds)
import Halogen (RefLabel(..))
import Halogen as H
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.HTML (class IsProp)
import Halogen.HTML as HH
import Halogen.HTML.Core (toPropValue)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (IProp(..))
import Halogen.HTML.Properties as HP
import Halogen.Query.EventSource (eventSource')
import Halogen.VDom.DOM.Prop (Prop(..), PropValue)
import Halogen.VDom.DOM.Prop as HVP
import Halogen.VDom.Driver (runUI)
import Halogen.VDom.Util as Util
import Type.Row (class RowLacks, class RowToList, Cons, Nil, RLProxy(..), kind RowList)
import Unsafe.Coerce (unsafeCoerce)
import Unsafe.Reference (unsafeRefEq)

newtype AProp (s :: Symbol) = AProperty PropValue
instance eqAProp :: Eq (AProp s) where
  eq (AProperty v1) (AProperty v2) = unsafeRefEq v1 v2

fromIProp ::
  forall s t one.
    IsSymbol s =>
    RowToList one (Cons s t Nil) =>
  IProp one Void -> Maybe (AProp s)
fromIProp (IProp (Property p v))
  | p == reflectSymbol (SProxy :: SProxy s)
  = Just (AProperty v)
fromIProp _ = Nothing

toIProp ::
  forall s o r.
    IsSymbol s =>
  AProp s -> IProp r o
toIProp (AProperty v) = IProp (Property p v)
  where p = reflectSymbol (SProxy :: SProxy s)

type State prop s =
  { value :: s
  , ref :: Maybe (Ref (Maybe (AProp prop)))
  , latest :: Maybe (AProp prop)
  }
initialState :: forall one s. s -> State one s
initialState =
  { value: _
  , ref: Nothing
  , latest: Nothing
  }

data Query prop s o a
  = Initialize a
  | Finalize a
  | Receive s a
  | Lift o a
  | UpdateProp (Maybe (AProp prop)) a

class MultiAttrBehavior
  (allowed :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | allowed -> partial behaviors
  , partial -> allowed behaviors
  where
    subscribe :: forall eff. Record behaviors -> (Variant partial -> Eff (frp :: FRP | eff) Unit) -> Eff (frp :: FRP | eff) (Eff (frp :: FRP | eff) Unit)
    handle :: forall e. Element -> Variant partial -> Eff ( dom :: DOM | e ) Unit
instance mab ::
  ( RowToList partial rl
  , MultiAttrBehaviorRL rl allowed partial behaviors
  ) => MultiAttrBehavior allowed partial behaviors where
    subscribe = subscribeRL (RLProxy :: RLProxy rl)
    handle = handleRL (RLProxy :: RLProxy rl)

class MultiAttrBehaviorRL
  (rl :: RowList)
  (allowed :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | rl -> allowed partial behaviors
  where
    subscribeRL :: forall eff. RLProxy rl -> Record behaviors -> (Variant partial -> Eff (frp :: FRP | eff) Unit) -> Eff (frp :: FRP | eff) (Eff (frp :: FRP | eff) Unit)
    handleRL :: forall e. RLProxy rl -> Element -> Variant partial -> Eff ( dom :: DOM | e ) Unit
instance mabNil :: MultiAttrBehaviorRL Nil () () () where
  subscribeRL _ {} cb = pure (pure unit)
  handleRL _ _ = case_
instance mabCons ::
  ( IsSymbol label
  , IsProp p
  , RowLacks label allowed'
  , RowLacks label partial'
  , RowLacks label behaviors'
  , RowCons label p allowed' allowed
  , RowCons label (Maybe p) partial' partial
  , RowCons label (Behavior (Maybe p)) behaviors' behaviors
  , Union partial' one partial
  , MultiAttrBehaviorRL rl allowed' partial' behaviors'
  ) => MultiAttrBehaviorRL (Cons label p rl) allowed partial behaviors where
    subscribeRL _ r cb = do
      c1 <- subscribeRL (RLProxy :: RLProxy rl) (delete k r) (expand >>> cb)
      c2 <- animate (get k r) (inj k >>> cb)
      pure (c1 *> c2)
      where k = SProxy :: SProxy label
    handleRL _ el = handleRL (RLProxy :: RLProxy rl) el
      # on k case _ of
        Just e -> Fn.runFn3 setProperty (reflectSymbol k) (toPropValue e) el
        Nothing -> Fn.runFn2 removeProperty (reflectSymbol k) el
      where k = (SProxy :: SProxy label)

-- allow mutation in ref?
newtype AroundState partial = AroundState
  { insideState :: Record partial
  , outsideState :: Maybe (Ref (Record partial))
  }

uninitializedAS :: forall partial. Nothings partial => AroundState partial
uninitializedAS = AroundState { insideState: aWholeLotOfNothing, outsideState: Nothing }

initialize :: forall partial eff. AroundState partial -> Eff ( ref :: REF | eff ) (AroundState partial)
initialize (AroundState { insideState }) =
  newRef insideState <#>
    AroundState <<< { insideState, outsideState: _ } <<< Just

snapshot :: forall partial eff. AroundState partial -> Eff ( ref :: REF | eff ) (AroundState partial)
snapshot a@(AroundState { outsideState: Nothing }) = pure a
snapshot (AroundState { outsideState: Just ref }) =
  readRef ref <#> \insideState ->
    AroundState { insideState, outsideState: Just ref }

eqProp :: forall p. IsProp p => p -> p -> Boolean
eqProp a b = unsafeRefEq (toPropValue a) (toPropValue b)

eqMProp :: forall p. IsProp p => Maybe p -> Maybe p -> Boolean
eqMProp (Just p1) (Just p2) = eqProp p1 p2
eqMProp Nothing Nothing = true
eqMProp _ _ = false

class Nothings (row :: # Type) where
  aWholeLotOfNothing :: Record row
class (RowToList row rl) <= NothingsRL (rl :: RowList) (row :: # Type) | rl -> row where
  aWholeLotOfNothingRL :: RLProxy rl -> Record row
instance nothingsImpl :: (RowToList row rl, NothingsRL rl row) => Nothings row where
  aWholeLotOfNothing = aWholeLotOfNothingRL (RLProxy :: RLProxy rl)
instance nothingsNil :: NothingsRL Nil () where
  aWholeLotOfNothingRL _ = {}
instance nothingsCons ::
  ( IsSymbol label
  , RowCons label (Maybe ty) row' row
  , RowLacks label row'
  , RowToList row (Cons label (Maybe ty) rl)
  , NothingsRL rl row'
  ) => NothingsRL (Cons label (Maybe ty) rl) row where
    aWholeLotOfNothingRL _ = insert (SProxy :: SProxy label) Nothing
      (aWholeLotOfNothingRL (RLProxy :: RLProxy rl) :: Record row')

behavioralComponent ::
  forall m r s o v prop eff other.
    MonadAff ( dom :: DOM, frp :: FRP, ref :: REF, avar :: AVAR | eff ) m =>
    IsSymbol prop =>
    RowCons prop v other r =>
  HH.Node r Void o ->
  (
    (Array (HH.IProp other o) -> Array (HH.HTML Void o) -> HH.HTML Void o) ->
    s ->
    HH.HTML Void o
  ) ->
  Behavior (Maybe (AProp prop)) ->
  H.Component HH.HTML (Query prop s o) s o m
behavioralComponent node renderWith behavior =
  H.lifecycleComponent
    { initialState
    , receiver: HE.input Receive
    , initializer: HE.input_ Initialize unit
    , finalizer: HE.input_ Initialize unit
    , render
    , eval
    }
  where
    label = RefLabel "behavioral-component"
    addRefProps = ([HP.ref label] <> _)
    propName = reflectSymbol (SProxy :: SProxy "style")
    expand = unsafeCoerce :: (Array (HH.IProp other o) -> Array (HH.IProp r o))

    -- Render the component. Delegates to the passed in renderer,
    -- lifts all communication from it.
    render :: State prop s -> H.HTML Void (Query prop s o)
    render { value, latest } = (Lift <@> unit) <$>
      let
        props = addRefProps case latest of
          Nothing -> []
          Just attr -> [toIProp attr]
        renderer attrs = node (expand attrs <> props)
      in renderWith renderer value

    eval :: Query prop s o ~> H.HalogenM (State prop s) (Query prop s o) (Const Void) Void o m
    -- Initialize the component.
    eval (Initialize a) = a <$ do
      -- Run the canceller, just in case ....
      eval (Finalize unit)
      -- Create a ref from the latest style
      style <- H.gets _.latest
      ref <- H.liftEff $ newRef style
      -- And store the ref and canceller in state!
      H.modify (_ { ref = Just ref })
      -- Start animating the behavior
      H.subscribe $ eventSource' (animate behavior)
        (Just <<< (UpdateProp <@> H.Listening))
    -- Update for a new input for the renderer.
    eval (Receive s a) = a <$ runMaybeT do
      -- Get the reference
      ref <- MaybeT $ H.gets _.ref
      -- Every time we update we need to snapshot the reference
      -- so the latest is available in render
      snapshot <- H.liftEff $ readRef ref
      H.modify (_ { value = s, latest = snapshot })
    -- Destroy the component.
    eval (Finalize a) = pure a
    -- Raise a query from the HTML to this component's output.
    eval (Lift q a) = a <$ do
      H.raise q
    -- Secretely set the style directly on the element, update the reference.
    -- Should *not* write to state.
    eval (UpdateProp mprop a) = a <$ runMaybeT do
      ref <- MaybeT $ H.gets _.ref
      prev <- H.liftEff $ readRef ref
      guard (mprop /= prev)
      -- Set the style directly on the DOM element
      el <- htmlElementToElement <$> MaybeT (H.getHTMLElementRef label)
      H.liftEff case mprop of
        Nothing -> Fn.runFn2 removeProperty propName el
        Just (AProperty p) -> Fn.runFn3 setProperty propName p el
      -- Update the reference with this style
      H.liftEff $ writeRef ref mprop

setProperty ∷ ∀ eff. Fn.Fn3 String PropValue Element (Eff (dom ∷ DOM | eff) Unit)
setProperty = Util.unsafeSetAny

unsafeGetProperty ∷ Fn.Fn2 String Element PropValue
unsafeGetProperty = Util.unsafeGetAny

removeProperty ∷ ∀ eff. Fn.Fn2 String Element (Eff (dom ∷ DOM | eff) Unit)
removeProperty = Fn.mkFn2 \key el →
  case typeOf (Fn.runFn2 Util.unsafeGetAny key el) of
    "string" → Fn.runFn3 Util.unsafeSetAny key "" el
    _        → Fn.runFn3 Util.unsafeSetAny key Util.jsUndefined el

main :: _
main = runHalogenAff $ awaitBody >>= runUI parent unit
  where
    pressed = buttons <#> size >>> (_ > 0)
    blink = seconds <#> round >>> even
    colorName = blink <#> if _ then "orange" else "rebeccapurple"
    italic = pressed <#> if _ then "italic" else "normal"
    combine coleur italicite = joinWith "; "
      [ "color: " <> coleur
      , "font-style: " <> italicite
      ]
    styleProp :: String -> AProp "style"
    styleProp = HVP.propFromString >>> AProperty
    b = (combine <$> colorName <*> italic) <#> styleProp >>> pure
    help = "Hold a mouse button down anywhere on the page to make this text italic!"
    component' = behavioralComponent HH.div <@> b $ \el t ->
      el [] [ HH.h1_ [ HH.text t ] ]
    parent = H.parentComponent
      { render: \v ->
        HH.div_
          [ HH.input [ HP.value v, HE.onInput (HE.input Tuple) ]
          , HH.slot unit component' v (absurd)
          ]
      , eval: \(Tuple e a) -> a <$ do
          for_ (runExcept $ target e # toForeign # readHTMLInputElement)
            (value >>> H.liftEff >=> H.put)
      , initialState: const help
      , receiver: const Nothing
      }
