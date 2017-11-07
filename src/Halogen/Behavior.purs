module Halogen.Behavior where

import Prelude

import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff.AVar (AVAR)
import Control.Monad.Eff.Console (CONSOLE, log)
import Control.Monad.Eff.Ref (REF, Ref, newRef, readRef, writeRef)
import Control.Monad.Except (runExcept)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.MonadZero (guard)
import DOM (DOM)
import DOM.Event.Event (target)
import DOM.HTML.HTMLInputElement (value)
import DOM.HTML.Types (htmlElementToElement, readHTMLInputElement)
import DOM.Node.Element (setAttribute)
import Data.Const (Const)
import Data.Foldable (for_)
import Data.Foreign (toForeign)
import Data.Int (even, round)
import Data.Maybe (Maybe(..))
import Data.Newtype (wrap)
import Data.Set (size)
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
import Halogen.HTML.Properties as HP
import Halogen.Query.EventSource (eventSource')
import Halogen.VDom.Driver (runUI)

type Style =
  { color :: String
  }
noStyle :: Style
noStyle = { color: "" }

type State s =
  { value :: s
  , ref :: Maybe (Ref Style)
  , latest :: Style
  }
initialState :: forall s. s -> State s
initialState =
  { value: _
  , ref: Nothing
  , latest: noStyle
  }

data Query s o a
  = Initialize a
  | Finalize a
  | Receive s a
  | Lift o a
  | UpdateStyle Style a

renderStyle :: Style -> String
renderStyle style = ("color: " <> style.color)

behavioralComponent ::
  forall m s o eff.
    MonadAff ( dom :: DOM, frp :: FRP, ref :: REF, avar :: AVAR, console :: CONSOLE | eff ) m =>
  (RefLabel -> s -> Style -> HH.HTML Void o) ->
  Behavior Style ->
  H.Component HH.HTML (Query s o) s o m
behavioralComponent renderr styleB = H.lifecycleComponent
  { initialState
  , receiver: HE.input Receive
  , initializer: HE.input_ Initialize unit
  , finalizer: HE.input_ Initialize unit
  , render
  , eval
  }
  where
    label = RefLabel "behavioral-component"
    -- Don't reevaluate this every time; apply the label _once_
    renderer = renderr label

    -- Render the component. Delegates to the passed in renderer,
    -- lifts all communication from it.
    render :: State s -> H.HTML Void (Query s o)
    render { value, latest } = (Lift <@> unit) <$>
      renderer value latest

    eval :: Query s o ~> H.HalogenM (State s) (Query s o) (Const Void) Void o m
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
      H.subscribe $ eventSource' (animate styleB)
        (Just <<< (UpdateStyle <@> H.Listening))
    -- Update for a new input for the renderer.
    eval (Receive s a) = a <$ runMaybeT do
      -- Get the reference
      ref <- MaybeT $ H.gets _.ref
      -- Every time we update we need to snapshot the reference
      -- so the latest is available in render
      snapshot <- H.liftEff $ readRef ref
      H.liftEff $ log ("Snapshot: " <> renderStyle snapshot)
      H.modify (_ { value = s, latest = snapshot })
    -- Destroy the component.
    eval (Finalize a) = pure a
    -- Raise a query from the HTML to this component's output.
    eval (Lift q a) = a <$ do
      H.raise q
    -- Secretely set the style directly on the element, update the reference.
    -- Should *not* write to state.
    eval (UpdateStyle style a) = a <$ runMaybeT do
      ref <- MaybeT $ H.gets _.ref
      prev <- H.liftEff $ readRef ref
      guard (style.color /= prev.color)
      -- Set the style directly on the DOM element
      el <- htmlElementToElement <$> MaybeT (H.getHTMLElementRef label)
      let rendered = renderStyle style
      H.liftEff $ setAttribute "style" rendered el
      -- Update the reference with this style
      H.liftEff $ log ("Setting style " <> rendered)
      H.liftEff $ writeRef ref style

main :: _
main = runHalogenAff $ awaitBody >>= runUI parent unit
  where
    pressed = buttons <#> size >>> (_ > 0)
    blink = seconds <#> round >>> even
    xor = (||) && ((&&) >>> compose not)
    colorName = (xor <$> pressed <*> blink) <#> if _ then "orange" else "rebeccapurple"
    b = colorName <#> { color: _ }
    help = "Hold a mouse button down anywhere on the page to change the color of this text"
    component' = behavioralComponent <@> b $ \label t style ->
      HH.div [ HP.ref label, HP.prop (wrap "style") $ renderStyle style ]
        [ HH.h1_ [ HH.text t ] ]
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
