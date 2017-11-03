module Halogen.Behavior where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff)
import Control.Monad.Eff.Ref (REF, Ref, newRef, readRef, writeRef)
import Control.Monad.Eff.Unsafe (unsafeCoerceEff)
import DOM (DOM)
import DOM.HTML.Types (HTMLElement, htmlElementToElement)
import DOM.Node.Element (setAttribute)
import Data.Const (Const)
import Data.Foldable (traverse_)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap, wrap)
import Data.Set (size)
import Data.Traversable (traverse)
import FRP (FRP)
import FRP.Behavior (Behavior, animate)
import FRP.Behavior.Mouse (buttons)
import Halogen (RefLabel(..))
import Halogen as H
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
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
  , destroyer :: Maybe (Eff ( dom :: DOM, frp :: FRP, ref :: REF ) Unit)
  }
initialState :: forall s. s -> State s
initialState =
  { value: _
  , ref: Nothing
  , latest: noStyle
  , destroyer: Nothing
  }

data Query s o a
  = Initialize a
  | Finalize a
  | Receive s a
  | Lift o a

renderStyle :: Style -> String
renderStyle style = ("color: " <> style.color)

behavioralComponent ::
  forall m s o eff.
    MonadEff ( dom :: DOM, ref :: REF, frp :: FRP | eff ) m =>
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

    -- This will allow an element's style to track a behavior.
    updateStyle :: HTMLElement -> Ref Style -> Style -> Eff ( dom :: DOM, ref :: REF, frp :: FRP | eff ) Unit
    updateStyle el ref style = do
      -- Set the style directly on the DOM element
      setAttribute "style" (renderStyle style) (htmlElementToElement el)
      -- Update the reference with this style
      writeRef ref style

    eval :: Query s o ~> H.HalogenM (State s) (Query s o) (Const Void) Void o m
    -- Initialize the component.
    eval (Initialize a) = a <$ do
      -- Run the canceller, just in case ....
      eval (Finalize unit)
      -- Create a ref from the latest style
      style <- H.gets _.latest
      ref <- H.liftEff $ newRef style
      -- Start animating the behavior
      destroyer <- H.getHTMLElementRef label >>= traverse \el ->
        H.liftEff $ animate styleB (updateStyle el ref)
      -- And store the ref and canceller in state!
      H.modify (_ { ref = Just ref, destroyer = map unsafeCoerceEff destroyer })
    -- Update for a new input for the renderer.
    eval (Receive s a) = a <$ do
      -- Get the reference
      H.gets _.ref >>= traverse_ \ref -> do
        -- Every time we update we need to snapshot the reference
        -- so the latest is available in render
        snapshot <- H.liftEff $ readRef ref
        H.modify (_ { value = s, latest = snapshot })
    -- Destroy the component.
    eval (Finalize a) =  a <$ do
      -- Run the canceller for the behavior animation
      H.gets (_.destroyer >>> map unsafeCoerceEff) >>= traverse_ H.liftEff
    -- Raise a query from the HTML to this component's output.
    eval (Lift q a) = a <$ do
      H.raise q

main :: _
main = runHalogenAff $ awaitBody >>= runUI component' unit
  where
    b = buttons <#> { color: _ } <<< \btns ->
      if size btns > 0 then "orange" else "rebeccapurple"
    component' = behavioralComponent <@> b $ \label _ style ->
      HH.div [HP.ref label, HP.prop (wrap "style") $ renderStyle style]
        [ HH.h1_ [ HH.text "Hold a mouse button down anywhere on the page to change the color of this text" ] ]
