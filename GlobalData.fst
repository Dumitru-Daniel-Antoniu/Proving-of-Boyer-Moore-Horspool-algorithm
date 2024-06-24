module GlobalData

open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

type english_letters =
  | A
  | B

val alphabet : (l:list english_letters{(forall (x:english_letters). mem x l = true) /\ l <> []})
let alphabet = [A;B]
  
val text : (l:list english_letters{l <> []})
let text = [A;A;A;A;B;A;A;B;A;B;A;A;A;B;A;B;B]

val pattern : (l:list english_letters{length l <= length text})
let pattern = if length [B;A;B;A;A;A;B;A;B] <= length text 
              then [B;A;B;A;A;A;B;A;B]
              else []