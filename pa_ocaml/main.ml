(** Entry point for the standard preprocessor. *)

open Earley_ocaml

module Main = Pa_main.Start(Pa_ocaml.Make(Pa_parser.Ext(Pa_ocaml.Initial)))
