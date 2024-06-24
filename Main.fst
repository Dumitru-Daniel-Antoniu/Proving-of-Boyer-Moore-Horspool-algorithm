module Main

open BoyerMooreHorspool
open Belongs
open UpdateBc
open GlobalData
open ItemIndices
open NewOrOld
open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

//output verification
let rec convert_english_letters_to_int (l:list english_letters)
  : list int 
  = match l with 
    | [] -> []
    | hd :: tl -> if hd = A then 
                  0 :: convert_english_letters_to_int tl 
                  else 1 :: convert_english_letters_to_int tl

let main() =
  let message =
     sprintf "The result is %d." (boyer_moore_horspool text pattern 0 0)
  in
  print_string message

#push-options "--warn_error -272"
let _ = main()
#pop-options