type english_letters =
  | A
  | B
  | C 
  | D
  | E
  | F 
  | G
  | H
  | I 
  | J
  | K
  | L 
  | M 
  | N 
  | O 
  | P 
  | Q 
  | R 
  | S 
  | T 
  | U 
  | V 
  | W 
  | X 
  | Y 
  | Z
  
val alphabet : list english_letters 
let alphabet = [A;B;C;D;E;F;G;H;I;J;K;M;N;O;P;Q;R;S;T;U;V;W;X;Y;Z]
  
val text : list english_letters
let text = [A;B;A;B;X;A;B;Z;A;B;A;B;A;B]

val pattern : list english_letters
let pattern = [Z;A;B;A;B;A;B]

val length (#a:Type) (l:list a) : nat
let rec length l
  = match l with
      | [] -> 0
      | hd :: tl -> 1 + length tl

val alphabet_length : nat
let alphabet_length = length alphabet

val alphabet_character_index (c:english_letters) (l:list english_letters) (i:int): int
let rec alphabet_character_index c l i
  = match l with 
      | [] -> -1
      | hd::tl -> if hd = c
                  then i
                  else alphabet_character_index c tl (i+1)
      
val verify_character_in_pattern (c:english_letters) (l:list english_letters) : bool
let rec verify_character_in_pattern c l =
    match l with
        | [] -> false
        | hd::tl -> if hd = c
                    then true
                    else verify_character_in_pattern c tl

val change_element_in_bc_list (l:list int) (i:int) (j:int) (n:int) : list int
let rec change_element_in_bc_list l i j n=
    match l with
        | [] -> []
        | hd::tl -> if i = j
                    then n::change_element_in_bc_list tl (i + 1) j n
                    else hd::change_element_in_bc_list tl (i + 1) j n

val create_bc (i:nat{i >= 0}) : list int
let rec create_bc i 
  =match i with
      | 0 -> []
      | _ -> (-1) :: (create_bc (i-1))
      
let bc : list int = create_bc alphabet_length

val update_bc (l:list english_letters) (a:list english_letters) (b:list int) (i:int) : list int
let rec update_bc l a b i = 
    match l with 
        | [] -> b
        | hd::tl -> update_bc tl a (change_element_in_bc_list b 0 (alphabet_character_index hd a 0) i) (i + 1)
        
let final_bc : list int = update_bc pattern alphabet bc 0

(*let main() =*)
(*    let result = Printf.sprintf "Hello"*)
(*    in *)
(*    FStar.IO.print_string result*)
(*    *)
(*let _ = main()*)

val first_characters (l:list english_letters) (j:nat{j >= 0}) : list english_letters
let rec first_characters l j =
    match l with
        | [] -> []
        | hd :: tl -> if j > 0 
                      then hd :: first_characters tl (j - 1)
                      else first_characters tl j
                    
val last_characters (l:list english_letters) (i:nat) (j:nat{j >= 0}) : list english_letters
let rec last_characters l i j =
    match l with
        | [] -> []
        | hd::tl -> if i >= j
                    then hd :: last_characters tl (i + 1) j
                    else last_characters tl (i + 1) j

val compare_frontier (l:list english_letters) (i:nat) (j:nat{j >= 0}) : bool
let compare_frontier l i j =
    if first_characters l j = last_characters l i j
    then true
    else false
    
val maximum_frontier (l:list english_letters) (i:nat) (j:nat{j >= 0}) (k:nat) : nat
let rec maximum_frontier l i j k =
    let nr = length l in
    match j with
        | nr -> k
        | _ -> if compare_frontier l i j = true
               then maximum_frontier l i (j + 1) j
               else maximum_frontier l i (j + 1) k

val create_pr (l:list english_letters) (j:nat{j >= 0}) : list int
let rec create_pr l j =
    let nr = length l + 1 in
    match j with 
        | nr -> []
        | _ -> if j = 0 
               then (-1) :: (create_pr l (j + 1))
               else (maximum_frontier (first_characters l j) 0 0 0) :: (create_pr l (j + 1))
               
let f : list int = create_pr pattern 0

val give_value (f:list int) (nr:nat) (i:nat{i >= 0}) : int
let rec give_value f nr i =
    match f with
        | [] -> -1
        | hd::tl -> if i = nr
                    then hd
                    else give_value tl nr (i + 1)

val create_gs (f:list int) (m:nat) (i:nat{i >= 0}) : list int
let rec create_gs f m i =
    match i with
        | m -> []
        | _ -> ((give_value f m 0) - m + i) :: (create_gs f m (i + 1))
        
let gs : list int = create_gs f (length pattern) 0

val append (#a:Type) (m:list a) (n:a) : list a
let rec append m n = 
    match m with
        | [] -> n :: []
        | hd :: tl -> hd :: (append tl n)

val reverse (#a:Type) (l:list a) : list a
let rec reverse l =
    match l with
        | [] -> []
        | hd :: tl -> append (reverse tl) hd

let r : list english_letters = reverse pattern
let g : list int = create_pr r 0
let h : list int = reverse g

val change_value (l:list int) (m:int) (n:int) (i:nat{i >= 0}) : list int
let rec change_value l m n i =
    match l with
        | [] -> []
        | hd :: tl -> if i = m
                      then n :: change_value tl m n (i + 1)
                      else hd :: change_value tl m n (i + 1)
                      
val update_gs (gs:list int) (h:list int) (i:nat{i >= 0}) (new_gs:list int) : list int
let rec update_gs gs h i new_gs =
    let nr = length gs in
    match gs with
        | [] -> new_gs
        | hd :: tl -> update_gs tl h (i + 1) (change_value gs (nr - (give_value h i 0)) i 0)

let final_gs : list int = update_gs gs h 0 []

val give_value_letter (f:list english_letters) (nr:nat) (i:nat{i >= 0}) : english_letters
let rec give_value_letter f nr i =
    match f with
        | [] -> A
        | hd::tl -> if i = nr
                    then hd
                    else give_value_letter tl nr (i + 1)
                  
val maximum (m:int) (n:int) : int
let maximum m n =
    if m > n 
    then m
    else n
                    
val boyer_moore (k:nat) (i:nat) (m:nat) (n:nat) (t:list english_letters) (p:list english_letters) (bc:list int) (gs:list int) (alphabet:list english_letters) : bool
let rec boyer_moore k i m n t p bc gs alphabet =
    let limit = n - m + 1 in
    match k, i with 
        | _, limit -> false
        | m, _ -> true
        | _, _ -> if give_value_letter t (i + m - 1 - k) 0 = give_value_letter p (m - 1 -k) 0
                  then boyer_moore (k + 1) i m n t p bc gs alphabet
                  else 
                      let shiftbc = m - k - 1 - (give_value bc (alphabet_character_index (give_value_letter t (i + m - 1 - k) 0) alphabet 0) 0) in
                      let shiftgs = m - k - (give_value gs (m - k) 0) in
                      boyer_moore 0 (i + (maximum shiftbc shiftgs)) m n t p bc gs alphabet