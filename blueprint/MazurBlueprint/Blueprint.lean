import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import MazurBlueprint.Chapters.IntegratedBaseline
import MazurBlueprint.Chapters.FiniteEndpoints
import MazurBlueprint.Chapters.SharedGeometry
import MazurBlueprint.Chapters.PrimeInfrastructure
import MazurBlueprint.Chapters.PrimeArgument
import MazurBlueprint.Chapters.Integration

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Mazur's rational torsion theorem" =>

This Blueprint is the canonical dependency map for the remaining formalization
of Mazur's theorem. Its 48 labelled nodes are the exact work items from
`coordination/program.json`. A `uses` arrow records a mathematical dependency;
stage membership is shown by the six groups. Existing declarations are named
as such, while every not-yet-built interface is explicitly marked *proposed*.

{include 0 MazurBlueprint.Chapters.IntegratedBaseline}
{include 0 MazurBlueprint.Chapters.FiniteEndpoints}
{include 0 MazurBlueprint.Chapters.SharedGeometry}
{include 0 MazurBlueprint.Chapters.PrimeInfrastructure}
{include 0 MazurBlueprint.Chapters.PrimeArgument}
{include 0 MazurBlueprint.Chapters.Integration}

{blueprint_graph (direction := LR) (pack := true) (preview := pinned)}
{blueprint_summary}
