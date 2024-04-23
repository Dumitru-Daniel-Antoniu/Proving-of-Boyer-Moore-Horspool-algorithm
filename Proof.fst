module Proof

open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

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
let text = [E;A;A;A;X;A;B;X;A;A;X;B;A;X;B;A;A;A;B;A;B;B]

val pattern : list english_letters
let pattern = [E;A;A;A;X;E;C;F;C]

val alphabet_length : (i:nat{i > 0})
let alphabet_length = length alphabet

//equivalent with mem c l 
// val verify_character_in_pattern (c:english_letters) (l:list english_letters) : bool
// let rec verify_character_in_pattern c l =
//     match l with
//         | [] -> false
//         | hd::tl -> if hd = c
//                     then true
//                     else verify_character_in_pattern c tl

//equivalent with map (new_or_old) l
// val change_element_in_bc_list (l:list int) (i:int) (j:int) (n:int) : list int
// let rec change_element_in_bc_list l i j n=
//     match l with
//         | [] -> []
//         | hd::tl -> if i = j
//                     then n::change_element_in_bc_list tl (i + 1) j n
//                     else hd::change_element_in_bc_list tl (i + 1) j n

let rec create_bc (i:nat) : Tot (list int) (decreases i) 
  =match i with
      | 0 -> []
      | _ -> (-1) :: (create_bc (i-1))

let rec length_create_bc_is_positive (i:nat)
  : Lemma (ensures length (create_bc i) >= 0)
  = match i with
    | 0 -> ()
    | _ -> length_create_bc_is_positive (i - 1)

let rec length_create_bc_is_i (i:nat) :
   Lemma (ensures (length (create_bc i) = i)) =
   match i with 
     | 0 -> ()
     | _ -> length_create_bc_is_i (i - 1)

let rec index_n_bc_is_minusone (i:nat) :
  Lemma (ensures 
        (let l = (create_bc i) in 
         forall (n:nat). n < length l ==> index l n = -1))
  = match i with
    | 0 -> ()
    | _ -> index_n_bc_is_minusone (i - 1)

let bc : list int = create_bc alphabet_length

let bc_length_is_positive = length_create_bc_is_positive alphabet_length
let bc_length_is_alphabet = length_create_bc_is_i alphabet_length
let bc_nth_element_is_minusone = index_n_bc_is_minusone alphabet_length

val item_index (#a:eqtype) (item:a) (l:list a) (i:nat): list nat
let rec item_index item l i
  = match l with 
      | [] -> []
      | hd::tl -> if hd = item
                  then i :: item_index item tl (i + 1)
                  else item_index item tl (i + 1)

let item_list_length_is_zero_if_the_list_length_is_zero (#a:eqtype) (l:list a)
  : Lemma (requires l = [])
          (ensures forall (item:a). length (item_index item l 0) = 0)
  = ()

let item_head (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). length (item_index item [hd l] 0) <= 1)
  = ()

let rec item_head_not_equal (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). hd l <> item ==> length (item_index item [hd l] 0) = 0)
  = match l with
    | last -> ()
    | hd :: tl -> item_head_not_equal tl

let rec item_head_equal (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). hd l = item ==> length (item_index item [hd l] 0) = 1)
  = match l with
    | last -> ()
    | hd :: tl -> item_head_equal tl

let rec item_head_count (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1) 
          (ensures forall (item:a). length (item_index item [hd l] 0) = count item [hd l])
  = match l with 
    | last -> ()
    | hd :: tl -> item_head_count tl

let item_empty_list_count (a:eqtype)
  : Lemma (ensures forall (item:a). length (item_index item [] 0) = count item [])
  = ()

let rec item_tail_count (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1) 
          (ensures forall (item:a). length (item_index item (tl l) 0) = count item (tl l))
  = match l with 
    | last -> admit()
    | hd :: tl -> admit(item_tail_count tl)

let rec item_tail (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). length (item_index item l 0) = length (item_index item [hd l] 0) + length (item_index item (tl l) 1))
  = match l with 
    | final -> ()
    | hd :: tl -> item_tail tl

let rec count_tail (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). count item l = count item [hd l] + count item (tl l))
  = match l with
    | final -> ()
    | hd :: tl -> count_tail tl

let rec item_list_has_correct_length (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). length (item_index item l 0) = count item l)
  = match l with 
    | [] -> ()
    | hd :: tl -> item_list_has_correct_length tl

let rec item_index_is_empty (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). (l = []) \/ (forall (i:nat{i < length l}). index l i <> item) ==> item_index item l 0 = [])
  = match l with
    | [] -> ()
    | hd :: tl -> admit(item_index_is_empty tl)

// let rec reunite_the_list (#a:eqtype) (l:list a)
//   : Lemma (requires length l >= 1)
//           (ensures l = append [hd l] (tl l))
//   = match l with 
//     | final -> ()
//     | hd :: tl -> reunite_the_list tl

let rec item_tail_not_equal (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). item_index item l 0 = append (item_index item [hd l] 0) (item_index item (tl l) 1))
  = match l with
    | final -> ()
    | hd :: tl -> item_tail_not_equal tl

let rec item_list_has_length_at_least_zero (#a:eqtype) (l:list a) 
  : Lemma (ensures forall (item:a). length (item_index item l 0) >= 0)
  = match l with
    | [] -> ()
    | hd :: tl -> item_list_has_length_at_least_zero tl

let rec item_has_at_most_length_l_occurrences (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). count item l <= length l)
  = match l with 
    | [] -> ()
    | hd :: tl -> item_has_at_most_length_l_occurrences tl

//correct store of indexes

let rec exists_item_zero_then_correct_index (#a:eqtype) (l:list a)
  : Lemma (requires length l > 0)
          (ensures forall (item:a).  index l 0 = item ==> mem 0 (item_index item l 0))
  = match l with
    | [last] -> ()
    | hd :: tl -> exists_item_zero_then_correct_index tl

let rec exists_item_one_then_correct_index (#a:eqtype) (l:list a)
  : Lemma (requires length l > 1)
          (ensures forall (item:a).  index l 1 = item ==> mem 1 (item_index item l 0))
  = match length l with
    | 2 -> ()
    | _ -> exists_item_one_then_correct_index (tl l)

let rec exists_item_i_then_correct_index (#a:eqtype) (l:list a) (i:nat)
  : Lemma (requires length l > i)
          (ensures forall (item:a). index l i = item ==> mem i (item_index item l 0))
  = let j = i + 1 in
    match length l with
    | j -> admit()
    | _ -> exists_item_i_then_correct_index (tl l) i

let rec index_is_or_is_not_item_is_or_is_not_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). (index l i = item || index l i <> item) ==> (mem i (item_index item l 0) = true || mem i (item_index item l 0) = false))
  = match l with
    | [] -> ()
    | hd :: tl -> index_is_or_is_not_item_is_or_is_not_mem tl

let rec index_is_not_item_is_not_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). index l i <> item ==> mem i (item_index item l 0) = false)
  = match l with
    | [] -> ()
    | hd :: tl -> admit(index_is_not_item_is_not_mem tl)

let rec exists_item_then_correct_index (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). index l i = item ==> mem i (item_index item l 0))
  = match l with
    | [] -> ()
    | hd :: tl -> admit(exists_item_then_correct_index tl)

let rec correct_index_then_exists_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). mem i (item_index item l 0) ==> index l i = item)
  = match l with
    | [] -> ()
    | hd :: tl -> admit(correct_index_then_exists_item tl)

let rec exists_item_index_iff_correct_index (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). index l i = item <==> mem i (item_index item l 0))
  = match l with
    | [] -> ()
    | hd :: tl -> exists_item_index_iff_correct_index tl;
                  exists_item_then_correct_index l;
                  correct_index_then_exists_item l

let rec index_is_in_interval (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat). mem i (item_index item l 0) = true ==> i >= 0 && i < length l)
  = match l with 
    | [] -> ()
    | hd :: tl -> admit(index_is_in_interval tl)

let rec last_is_in_interval (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). item_index item l 0 <> [] ==> last (item_index item l 0) >= 0 && last (item_index item l 0) < length l)
  = match l with
    | [] -> ()
    | hd :: tl -> admit(last_is_in_interval tl)

let new_or_old (#a:eqtype) (c:a) (l:list a) : int
  = if item_index c l 0 <> []
    then last (item_index c l 0)
    else -1

let rec not_new_or_old_empty_list (#a:eqtype) (l:list a) 
  : Lemma (ensures forall (item:a). new_or_old item l = -1 ==> item_index item l 0 = [])
  = match l with
    | [] -> ()
    | hd :: tl -> not_new_or_old_empty_list tl 

let rec empty_list_length_zero (#a:eqtype) (l:list a) 
  : Lemma (ensures forall (item:a). item_index item l 0 = [] ==> length (item_index item l 0) = 0)
  = match l with 
    | [] -> ()
    | hd :: tl -> empty_list_length_zero tl

//make the lemma without admit
let rec length_zero_count_zero (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). length (item_index item l 0) = 0 ==> count item l = 0)
  = match l with
    | [] -> ()
    | hd :: tl -> length_zero_count_zero tl;
                  item_list_has_correct_length l

let rec count_zero_mem_false (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). count item l = 0 ==> mem item l = false)
  = match l with
    | [] -> ()
    | hd :: tl -> count_zero_mem_false tl
                 
let rec mem_false_not_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). mem item l = false ==> (forall (i:nat). i < length l ==> index l i <> item))
  = match l with 
    | [] -> ()
    | hd :: tl -> mem_false_not_item tl

let rec new_or_old_not_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). new_or_old item l = -1 ==> (forall (i:nat). i < length l ==> index l i <> item))
  = match l with
    | [] -> ()
    | hd :: tl -> new_or_old_not_item tl;
                  not_new_or_old_empty_list l;
                  empty_list_length_zero l;
                  length_zero_count_zero l;
                  count_zero_mem_false l;
                  mem_false_not_item l

let rec new_or_old_not_empty_list (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). new_or_old item l <> -1 ==> item_index item l 0 <> [])
  = match l with
    | [] -> ()
    | hd :: tl -> new_or_old_not_empty_list tl

let rec not_empty_list_length_greater_than_zero (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). (item_index item l 0 <> [] && last (item_index item l 0) < length l) ==> last (item_index item l 0) >= 0)
  = match l with
    | [] -> ()
    | hd :: tl -> not_empty_list_length_greater_than_zero tl                  

let rec last_list_mem (#a:eqtype) (l:list a)
  : Lemma (requires length l > 0)
          (ensures mem (last l) l = true)
  = match l with
    | [hd] -> ()
    | hd :: tl -> last_list_mem tl

let length_greater_than_zero_mem (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_index item l 0 <> [])
          (ensures last (item_index item l 0) >= 0 ==> mem (last (item_index item l 0)) (item_index item l 0) = true)
  = last_list_mem (item_index item l 0)

let mem_index_is_item (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_index item l 0 <> [] && last (item_index item l 0) < length l)
          (ensures mem (last (item_index item l 0)) (item_index item l 0) = true ==> index l (last (item_index item l 0)) = item)
  = exists_item_index_iff_correct_index l;
    ()

let new_or_old_not_empty_list_correct_item (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_index item l 0 <> [] && last (item_index item l 0) < length l)
          (ensures new_or_old item l <> -1 ==> index l (last (item_index item l 0)) = item)
  = new_or_old_not_empty_list l;
    not_empty_list_length_greater_than_zero l;
    length_greater_than_zero_mem l item;
    mem_index_is_item l item;
    ()

val update_bc (a:list english_letters) : list int
let rec update_bc a = 
    match a with 
        | [] -> []
        | hd::tl -> (new_or_old hd pattern) :: update_bc tl

let final_bc : list int = update_bc alphabet

let rec final_bc_length_is_alphabet_length (a:list english_letters)
  : Lemma (ensures length (update_bc a) = length a)
  = match a with
      | [] -> ()
      | hd :: tl -> final_bc_length_is_alphabet_length tl

// let rec element_not_minusone_is_part_of_the_pattern (i:nat{i < length final_bc})
//   : Lemma (requires i < length alphabet)
//           (ensures index final_bc i <> -1 ==> item_index (index alphabet i) (rev pattern) 0 <> -1)
//   = match i with 
//       | 0 -> ()
//       | _ -> element_not_minusone_is_part_of_the_pattern (i - 1)

// let rec element_not_minusone_is_in_interval (i:nat{i < length final_bc})
//   : Lemma (ensures index final_bc i <> -1 ==> index final_bc i >= 0 && index final_bc i < length pattern)
//   = match i with 
//       | 0 -> ()
//       | _ -> final_bc_length_is_alphabet_length alphabet;
//              pattern_elements_are_in_interval 0 (index alphabet i);
//              element_not_minusone_is_in_interval (i - 1)

// let rec last_index_of_character_versus_the_next_character (i:nat) 
//   : Lemma (requires i < length final_bc) 
//           (ensures (index final_bc i <> -1 && i + 1 < length pattern) ==> index pattern (i + 1) <> index alphabet i)
//   = match i with
//       | 0 -> ()
//       | _ -> last_index_of_character_versus_the_next_character (i - 1)

// let rec last_index_of_character_stored_correctly (i:nat)
//   : Lemma (requires i < length final_bc)
//           (ensures index final_bc i <> -1 ==> (forall j. j > i && j < length final_bc ==> index pattern j <> index alphabet i))
//   = match i with
//       | 0 -> ()
//       | _ -> last_index_of_character_stored_correctly (i - 1) 

//good suffix part
val first_characters (l:list english_letters) (j:nat{j >= 0}) : list english_letters
let rec first_characters l j =
    match l with
        | [] -> []
        | hd :: tl -> if j > 0 
                      then hd :: first_characters tl (j - 1)
                      else first_characters tl j
                    
val last_characters (l:list english_letters) (dim:nat) (i:nat) (j:nat{j >= 0}) : list english_letters
let rec last_characters l dim i j =
    match l with
        | [] -> []
        | hd::tl -> if i >= dim - j
                    then hd :: last_characters tl dim (i + 1) j
                    else last_characters tl dim (i + 1) j

val compare_frontier (l:list english_letters) (dim:nat) (i:nat) (j:nat{j >= 0}) : bool
let compare_frontier l dim i j =
    if first_characters l j = last_characters l dim i j && j < (length l)
    then true
    else false
    
val maximum (m:int) (n:int) : int
let maximum m n =
    if m > n 
    then m
    else n

val maximum_frontier (l:list english_letters) (dim:nat) (i:nat) (j:nat{j >= 0}) : nat
let rec maximum_frontier l dim i j =
    match j with
        | 0 -> 0
        | _ -> if compare_frontier l dim i j = true
               then j
               else maximum_frontier l dim i (j - 1)

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

val create_pr (l:list english_letters) (j:nat{j >= 0}) : list int
let rec create_pr l j =
    match j with 
        | 0 -> [-1]
        | _ -> (maximum_frontier (first_characters l j) (length (first_characters l j)) 0 (length (first_characters l j))) :: (create_pr l (j - 1))
               
let f : list int = reverse (create_pr pattern (length pattern))

val give_value (f:list int) (nr:int) (i:nat{i >= 0}) : int
let rec give_value f nr i =
    match f with
        | [] -> -1
        | hd::tl -> if i = nr
                    then hd
                    else give_value tl nr (i + 1)

val create_gs (f:list int) (m:nat) (i:nat{i >= 0}) : list int
let rec create_gs f m i =
    match i with
        | 0 -> [(give_value f m 0) - m]
        | _ -> ((give_value f m 0) - m + i) :: (create_gs f m (i - 1))
        
let gs : list int = reverse (create_gs f (length pattern) ((length pattern) - 1))
 
let r : list english_letters = reverse pattern
let g : list int = reverse (create_pr r (length r)) 
let h : list int = reverse g

val change_value (l:list int) (m:int) (n:int) (i:nat{i >= 0}) : list int
let rec change_value l m n i : Tot (list int) (decreases l) =
    match l with
        | [] -> []
        | hd :: tl -> if i = m
                      then n :: change_value tl m n (i + 1)
                      else hd :: change_value tl m n (i + 1)
                      
val update_gs (gs:list int) (h:list int) (i:int{i >= 0}) (dim:nat) : Tot (list int) (decreases i)
let rec update_gs gs h i dim =
    match i with
        | 0 -> gs
        | _ -> update_gs (change_value gs (dim - (give_value h (dim - i) 0)) (dim - i) 0) h (i - 1) dim

let final_gs : list int = append (update_gs gs h (length pattern) (length pattern)) ((length pattern) - 1)

val give_value_letter (f:list english_letters) (nr:int) (i:nat{i >= 0}) : english_letters
let rec give_value_letter f nr i =
    match f with
        | [] -> A
        | hd::tl -> if i = nr
                    then hd
                    else give_value_letter tl nr (i + 1)
                    
// val boyer_moore (k:nat) (i:nat) (m:nat) (n:nat) (t:list english_letters) (p:list english_letters) (bc:list int) (gs:list int) (alphabet:list english_letters) : Tot bool (decreases %[i;k])
// let rec boyer_moore k i m n t p bc gs alphabet =
//     match k, i with 
//         | _, 0 -> false
//         | 0, _ -> true
//         | _, _ -> if give_value_letter t ((n - m + 1 - i) + m - 1 - (m - k)) 0 <> give_value_letter p (m - 1 - (m - k)) 0
//                   then let shiftbc = m - (m - k) - 1 - (give_value bc (alphabet_character_index (give_value_letter t ((n - m + 1 - i) + m - 1 - (m - k)) 0) alphabet 0) 0) in
//                        let shiftgs = m - (m - k) - (give_value gs (m - (m - k)) 0) in
//                        let index = i - (maximum shiftbc shiftgs) in
//                        if index >= 0 && index < i
//                        then boyer_moore m index m n t p bc gs alphabet
//                        else boyer_moore m 0 m n t p bc gs alphabet
//                   else boyer_moore (k - 1) i m n t p bc gs alphabet

//conversion functions, print and main
let convert_to_int f =
  match f with
    | false -> 0
    | true -> 1

let string_of_int_list l =
  Printf.sprintf "[%s]" (String.concat "; " (List.Tot.map (Printf.sprintf "%d") l))

// let rec convert_letters_to_int (l:list english_letters) : list int =
//   match l with
//     | [] -> []
//     | hd::tl -> (alphabet_character_index hd alphabet 0)::(convert_letters_to_int tl)

// let convert_letter_to_int c =
//   alphabet_character_index c alphabet 0

let main() =
  let message =
     sprintf "The result is %d\n" (new_or_old J (rev pattern))
  in
  print_string message

#push-options "--warn_error -272"
let _ = main()
#pop-options