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
import Data.Set (size)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Data.Tuple (Tuple(..))
import FRP (FRP)
import FRP.Behavior (Behavior, animate)
import FRP.Behavior.Mouse (buttons)
import FRP.Behavior.Time (seconds)
import Halogen (RefLabel(..))
import Halogen as H
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (IProp(..))
import Halogen.HTML.Properties as HP
import Halogen.Query.EventSource (eventSource')
import Halogen.VDom.DOM.Prop (Prop(..), PropValue)
import Halogen.VDom.DOM.Prop as HVP
import Halogen.VDom.Driver (runUI)
import Halogen.VDom.Util as Util
import Type.Row (class RowToList, Cons, Nil)
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
