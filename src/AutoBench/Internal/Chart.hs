
{-# OPTIONS_GHC -Wall            #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-|

  Module      : AutoBench.Internal.Chart
  Description : Produce graphs of runtime measurements and trend lines
                predicted by linear regression
  Copyright   : (c) 2018 Martin Handley
  License     : BSD-style
  Maintainer  : martin.handley@nottingham.ac.uk
  Stability   : Experimental
  Portability : GHC

  This module is responsible for producing graphs of runtime measurements and
  trend lines predicted by linear regression. Graphs are saved to file.

-}

{-
   ----------------------------------------------------------------------------
   <TO-DO>:
   ----------------------------------------------------------------------------
   - More user options for graphing, plot just raws/just trends/etc.;
   - Combine lens setters;
   - Add more colours;
   -
-}

module AutoBench.Internal.Chart (plotAndSaveAnalGraph) where

import Control.Exception                      (SomeException, catch)
import Control.Lens                           ((.=), (%=), _Just)
import Control.Monad                          (void)
import Data.Colour                            (AlphaColour, opaque, withOpacity)
import Data.Colour.SRGB                       (sRGB24)
import Data.Default.Class                     (def)
import Data.List                              (nub)
import Data.Maybe                             (catMaybes)
import Data.Tuple.Select                      (sel1, sel3)
import Graphics.Rendering.Chart.Backend.Cairo ( FileFormat(..), FileOptions(..)
                                              , renderableToFile )
import Graphics.Rendering.Chart.Grid         -- ( Grid, above, empty, gridToRenderable, overlay
                                             -- , tspan )
import Graphics.Rendering.Chart.State         (EC, execEC, plot, liftEC)
import System.Directory                       (doesFileExist)
import System.FilePath.Posix                  (makeValid)
import Data.Colour.Names
import Graphics.Rendering.Chart

import AutoBench.Internal.AbstractSyntax (Id)
import AutoBench.Internal.Types          (Coord)
import AutoBench.Internal.Utils          ((.*))



-- | Plot and save graph of runtime measurements.
plotAndSaveAnalGraph
  :: FilePath
  -> [(Id, [Coord], Maybe String, Maybe [Coord])]     -- (Program name, raw measurements, model's pretty name, model's predictions).
  -> Maybe (Id, [Coord], Maybe String, Maybe [Coord]) -- As above but for baseline measurements.
  -> IO ()
plotAndSaveAnalGraph fp = saveAnalGraph fp .* plotAnalGraph

-- | Save graph and check file has been created. Catch all errors and print
-- them, don't allow errors to be thrown.
saveAnalGraph :: FilePath -> Renderable a -> IO ()
saveAnalGraph fp r =
  ( do void $ renderableToFile fileOpts fp' r
       b <- doesFileExist fp'
       if b
         then putStrLn $ "Runtime graph created: " ++ fp'
         else putStrLn $ "Runtime graph could not be created."
  ) `catch` (\(e :: SomeException) -> putStrLn $         -- Catch all errors here.
      "Runtime graph could not be created: " ++ show e)  -- Show error.

  where
    fp' = makeValid fp
    -- Compatible resolution with my MacBook at least?
    -- Note: this should probably be a user setting?
    fileOpts :: FileOptions
    fileOpts  = FileOptions (2560, 1600) PNG

-- | Plot graph of runtime measurements.
plotAnalGraph
  :: [(Id, [Coord], Maybe String, Maybe [Coord])]     -- (Program name, raw measurements, model's pretty name, model's predictions).
  -> Maybe (Id, [Coord], Maybe String, Maybe [Coord]) -- As above but for baseline measurements.
  -> Renderable (LayoutPick Double Double Double)
plotAnalGraph progPlots blPlot = fillBackground def . gridToRenderable $
   tspan logo (8, 8) `overlay` graphGrid `overlay` (tspan xAxisLabel (8, 7))

  where

    -- Graph elements: START --------------------------------------------------

    -- The spacing for the x-axis title is annoying, and doesn't seem to be
    -- modifiable. So we've hacked it.
    -- Hack to move the x-axis title away from the legend.
    legendWidth = sum $ fmap length $ take 4 $ fmap sel1 progPlots ++ nub
      (catMaybes $ fmap sel3 progPlots) ++ maybe [] (\bl -> maybe [] return $
        sel3 bl) blPlot
    xAxisLabel = setPickFn nullPickFn $
      label (def {_font_size = 40 }) HTA_Centre VTA_BaseLine $
      concat (replicate (legendWidth - 48) "\t\t") ++ "Input Size"  -- Hack to move the x-axis title away from the legend.

    -- Add an AutoBench logo.
    logo = setPickFn nullPickFn
            $ label (def { _font_size = 30.0
                         , _font_slant = FontSlantOblique
                         , _font_color = opaque grey
                         }
                    ) HTA_Right VTA_Bottom "Generated by AutoBench."

    -- The actual graph to plot with its titles, labels etc.
    graphGrid :: Grid (Renderable (LayoutPick Double Double Double))
    graphGrid  = layoutToGrid . execEC $ do

      -- Basics:
      layout_margin     .= 40.0
      layout_foreground .= opaque black

      -- Font size:
      layout_axes_title_styles . font_size %= (* 1.2)
      layout_all_font_styles   . font_size %= (* 3.5)

      -- Title:
      layout_title .= foldr1 (\s1 acc -> s1 ++ " vs. " ++ acc) (fmap sel1 progPlots)

      -- Axes:

      -- Note: hacked the x-axis title because the spacing was an issue.
      -- We set the title to empty string for the spacing, then placed a label
      -- underneath it.
      layout_x_axis . laxis_title .= " "
      -- Edit the font size to change distance between x-axis labels and title.
      layout_x_axis . laxis_title_style . font_size .= 15.0
      -- Rest of settings are standard
      layout_x_axis . laxis_style . axis_line_style . line_width .= 3.0
      layout_x_axis . laxis_style . axis_grid_style . line_width .= 3.0
      layout_x_axis . laxis_style . axis_label_gap               .= 20.0
      layout_x_axis . laxis_generate                             .= scaledAxis axis (xMin, xMax)

      -- y-axis doesn't need to be hacked.
      layout_y_axis . laxis_title                                .=  "Time (" ++ yUnits ++ ")"
      layout_y_axis . laxis_title_style . font_size              .= 40.0
      layout_y_axis . laxis_style . axis_line_style . line_width .= 3.0
      layout_y_axis . laxis_style . axis_grid_style . line_width .= 3.0
      layout_y_axis . laxis_style . axis_label_gap               .= 20.0
      layout_y_axis . laxis_generate                             .= scaledAxis axis (yMin, yMax)

      -- Legend:
      layout_legend . _Just . legend_margin      .= 20.0
      layout_legend . _Just . legend_plot_size   .= 20.0
      layout_legend . _Just . legend_position    .= LegendBelow
      layout_legend . _Just . legend_orientation .= LORows 4

      -- Plots:
      -- Need to plot points first then lines, otherwise legend looks bad.
      let (pointPlotss, linePlotss) = unzip $ fmap (uncurry graphProgPlots)
                                       (zip scaledProgPlots colours)
      mapM_ plot (concat pointPlotss)                             -- Raw measurements.
      mapM_ plot (concat linePlotss ++ graphBlPlot scaledBlPlot)  -- Trend lines and baseline measurements.


      --mapM_ (uncurry graphProgPlots) (zip scaledProgPlots colours)
      --graphBlPlot scaledBlPlot

    -- Graph elements: END ----------------------------------------------------

    -- Axis scaling: START ----------------------------------------------------

    -- All the coordinates from every plot /pre scaling/, including baseline
    -- measurements.
    allCoords :: [Coord]
    allCoords  = (concatMap getCoords progPlots) ++ (maybe [] getCoords blPlot)

    -- Calculate the y-axis scale and units for plotting runtime measurements.                      -- <TO-DO>: Sanitise runtimes to avoid error?
    -- Note: runtimes should be sanitised first to ensure that they are all
    -- non-negative, see 'sanitiseRuntimes'.
    calcYAxisScaleAndUnits :: [Double] -> (Double, String)
    calcYAxisScaleAndUnits ds = scale_ dsMax
      where
        dsMax = maximum ds
        scale_ d
          | d < 0      = error "negative runtime: calcYAxisScaleAndUnits"
          | d >= 1     = (1,     "s")
          | d >= 1e-3  = (1e3,  "ms")
          | d >= 1e-6  = (1e6,  "μs")
          | d >= 1e-9  = (1e9,  "ns")
          | d >= 1e-12 = (1e12, "ps")
          | d >= 1e-15 = (1e15, "fs")
          | d >= 1e-18 = (1e18, "as")
          | otherwise  = (1,     "s")

    -- Calculate the scale. All measurements are scaled according to the
    -- /maximum/ y-value.
    (yScale, yUnits) = calcYAxisScaleAndUnits (fmap snd allCoords)

    -- Runtime measurements are in seconds, so scale them to ms, μs, ns,
    -- etc., so the scaling on the y-axis isn't, e.g., 0.0000001 seconds.
    -- This function re-scales the y-values of each given plot according to
    -- the 'yScale'.
    scalePlot
      :: (Id, [Coord], Maybe String, Maybe [Coord])
      -> (Id, [Coord], Maybe String, Maybe [Coord])
    scalePlot (idt, cs, modelIdt, modelCs) =
      (idt,scaleYCoords yScale cs, modelIdt, fmap (scaleYCoords yScale) modelCs)
      where scaleYCoords = fmap . fmap . (*)

    -- /Scaled/ plots.
    scaledProgPlots = fmap scalePlot progPlots
    scaledBlPlot    = fmap scalePlot blPlot

    -- All the coordinates from every /scaled/ plot, including baseline
    -- measurements.
    allScaledCoords = (concatMap getCoords scaledProgPlots) ++
      (maybe [] getCoords scaledBlPlot)

    -- Min/max for axes /post scaling/.
    xMin = max 0 $ minimum $ fmap fst allScaledCoords
    xMax = maximum $ fmap fst allScaledCoords
    yMin = max 0 $ minimum $ fmap snd allScaledCoords
    yMax = maximum $ fmap snd allScaledCoords

    -- Axis scaling: END ------------------------------------------------------

    -- Plotting: START --------------------------------------------------------

    -- Plot raw measurement from test programs and their trend lines predicted
    -- by the model in the same colour.
    -- Note: 'Maybes' are both 'Just' or both 'Nothing'.
    graphProgPlots
      :: (Id, [Coord], Maybe String, Maybe [Coord])
      -> AlphaColour Double
      -> ([EC l (PlotPoints Double Double)], [EC l1 (PlotLines Double Double)])
    -- Plot model predictions as a line of best fit.
    graphProgPlots (idt, cs, Just modelIdt, Just modelCs) colour =
      ( [plotPoints idt cs colour]
      , [plotLines modelIdt modelCs colour] )
    -- Just plot raw data, no line of best fit.
    graphProgPlots (idt, cs, _, _) colour = ([plotPoints idt cs colour], [])

    -- Plot baseline measurements, if applicable.
    graphBlPlot
      :: Maybe (Id, [Coord], Maybe String, Maybe [Coord])
      -> [EC l1 (PlotLines Double Double)]
    -- Just plot trend line for baseline measurements.
    graphBlPlot (Just (_, _, Just modelIdt, Just modelCs)) =
      [plotDashedLines modelIdt modelCs (withOpacity black 0.7)]
    graphBlPlot _ = []

    -- Points for raw runtime measurements.
    plotPoints
      :: String
      -> [(Double, Double)]
      -> AlphaColour Double
      -> EC l (PlotPoints Double Double)
    plotPoints title coords colour = liftEC $ do
      plot_points_values                     .= coords
      plot_points_title                      .= title
      plot_points_style . point_color        .= colour
      plot_points_style . point_border_color .= colour
      plot_points_style . point_border_width .= 2.0
      plot_points_style . point_shape        .= PointShapeCross
      plot_points_style . point_radius       .= 10.0

    -- Solid trend lines for model predictions.
    plotLines
      :: String
      -> [(Double, Double)]
      -> AlphaColour Double
      -> EC l (PlotLines Double Double)
    plotLines title coords colour = liftEC $ do
      plot_lines_title  .= title
      plot_lines_values .= [coords]
      plot_lines_style  .= solidLine 3.0 colour

    -- Dashed trend lines for baseline measurements.
    plotDashedLines
      :: String
      -> [(Double, Double)]
      -> AlphaColour Double
      -> EC l (PlotLines Double Double)
    plotDashedLines title coords colour = liftEC $ do
      plot_lines_title  .= title
      plot_lines_values .= [coords]
      plot_lines_style  .= dashedLine 3.0 [40.0, 15.0] colour

    -- Other helpers: ---------------------------------------------------------

    -- We want ~10 labels on each axis and ~100 ticks.
    -- We use scaledAxis anyway, so can generate more labels if needed.
    axis = def {_la_nLabels = 10, _la_nTicks = 100 }

    -- | Opaque colours for points/lines.
    colours :: [AlphaColour Double]                                                                 -- <TO-DO>: Add more colours.
    colours  = fmap opaque                                                                          -- Number of colours = number of test programs so 7 isn't enough!
      [
        orange
      , skyblue
      , bluishgreen
      , yellow
      , blue
      , vermillion
      , reddishpurple
      , black
      , red
      , forestgreen
      , darkmagenta
      , deeppink
      , darkorange
      , coral
      , gainsboro
      , maroon
      , orchid
      , sandybrown
      , wheat
      , yellowgreen
      , gold
      , indianred
      ]

    bluishgreen = sRGB24 0 158 115
    vermillion = sRGB24 213 94 0
    reddishpurple = sRGB24 204 121 167

    -- Get the coordinates from each plot.
    getCoords :: (Id, [Coord], Maybe String, Maybe [Coord]) -> [Coord]
    getCoords (_, cs, _, Just modelCs) = cs ++ modelCs
    getCoords (_, cs, _, _) = cs
