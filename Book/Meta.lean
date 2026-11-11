import VersoManual
import Lean.Data.Json

open Lean
open Verso Doc Elab Output Html Code ArgParse
open Verso.Genre Manual

namespace Book

-- Raw HTML pass-through block for rich hero cards and custom callouts.
block_extension Block.rawHtml (htmlStr : String) where
  data := toJson htmlStr
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        Verso.reportError s!"rawHtml deserialization error: {err}"
        pure .empty
      | .ok (s : String) =>
        pure (Html.text false s)

@[code_block]
def rawHtml : CodeBlockExpanderOf Unit
  | (), str =>
    `(Verso.Doc.Block.other (Block.rawHtml $(quote str.getString)) #[])

structure Spatial3DConfig where
  model : String
  title : String

def Spatial3DConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] :
    ArgParse m Spatial3DConfig :=
  Spatial3DConfig.mk <$> .named `model .string false <*> .named `title .string false

instance [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] :
    FromArgs Spatial3DConfig m := ⟨Spatial3DConfig.parse⟩

-- Stereoscopic 3D Spatial Stage (<model stagemode="orbit"> for Vision Pro + WebGL/AR fallback).
block_extension Block.spatial3d (modelSlug : String) (title : String) (captionHtml : String) where
  data := toJson (modelSlug, title, captionHtml)
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data (α := String × String × String) with
      | .error err =>
        Verso.reportError s!"spatial3d deserialization error: {err}"
        pure .empty
      | .ok (slug, ttl, cap) =>
        let usdzUrl := s!"static/models/{slug}.usdz"
        let glbUrl := s!"static/models/{slug}.glb"
        pure {{
          <div class="spatial-stage">
            <div class="spatial-stage-header">
              <span class="spatial-stage-title">{{ttl}}</span>
              <span class="spatial-stage-badge">"Vision Pro 3D · iPhone AR & Orbit"</span>
            </div>
            <div class="spatial-viewport">
              <model class="spatial-model-native" src={{usdzUrl}} stagemode="orbit" interactive="interactive" aria-label={{ttl}}>
                <source src={{usdzUrl}} type="model/vnd.usdz+zip" />
                <div class="spatial-model-fallback" data-glb={{glbUrl}} data-usdz={{usdzUrl}} data-alt={{ttl}}></div>
              </model>
            </div>
            <div class="spatial-stage-footer">
              <div class="spatial-stage-desc">{{Html.text false cap}}</div>
              <a class="spatial-ar-link" rel="ar" href={{usdzUrl}}>
                "◈ View 3D / AR (.usdz)"
              </a>
            </div>
          </div>
        }}

@[code_block]
def spatial3d : CodeBlockExpanderOf Spatial3DConfig
  | cfg, str =>
    `(Verso.Doc.Block.other
        (Block.spatial3d $(quote cfg.model) $(quote cfg.title) $(quote str.getString.trimAscii.toString))
        #[])

structure SvgCardConfig where
  src : String
  alt : String

def SvgCardConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] :
    ArgParse m SvgCardConfig :=
  SvgCardConfig.mk <$> .named `src .string false <*> .named `alt .string false

instance [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] :
    FromArgs SvgCardConfig m := ⟨SvgCardConfig.parse⟩

-- Illustrated SVG/image diagram card with formatted HTML caption.
block_extension Block.svgCard (src : String) (alt : String) (captionHtml : String) where
  data := toJson (src, alt, captionHtml)
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data (α := String × String × String) with
      | .error err =>
        Verso.reportError s!"svgCard deserialization error: {err}"
        pure .empty
      | .ok (imgSrc, altText, cap) =>
        pure {{
          <figure class="hr-diagram-card">
            <img src={{imgSrc}} alt={{altText}} loading="lazy" />
            <figcaption class="hr-diagram-caption">{{Html.text false cap}}</figcaption>
          </figure>
        }}

@[code_block]
def svgCard : CodeBlockExpanderOf SvgCardConfig
  | cfg, str =>
    `(Verso.Doc.Block.other
        (Block.svgCard $(quote cfg.src) $(quote cfg.alt) $(quote str.getString.trimAscii.toString))
        #[])

end Book
