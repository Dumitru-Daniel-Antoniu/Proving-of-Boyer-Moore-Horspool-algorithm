module UpdateBc

open GlobalData
open ItemIndices
open NewOrOld
open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

let rec update_bc (a:list english_letters) (p:list english_letters) 
  : list int
  = match a with 
    | [] -> []
    | hd :: tl -> (new_or_old hd p) :: update_bc tl p

let rec update_bc_length_is_initial_list_length (l:list english_letters) (p:list english_letters)
  : Lemma (ensures length (update_bc l p) = length l)
  = match l with 
    | [] -> ()
    | hd :: tl -> update_bc_length_is_initial_list_length tl p

let rec update_bc_for_minusone_base (l:list english_letters) (p:list english_letters)
                                    (i:nat{i < length l && i < length (update_bc l p)}) 
                                    (j:nat{j < length p})
  : Lemma (ensures 
           (let l' = update_bc l p in
            index l' i = -1 ==> index p j <> index l i))
  = update_bc_length_is_initial_list_length l p;
    match l with 
    | [] -> ()
    | fst :: tl -> match i with 
                   | 0 -> assert(update_bc l p = (new_or_old fst p) :: update_bc tl p);
                          assert(index (update_bc l p) i = new_or_old fst p);
                          assert(fst = index l i);
                          new_or_old_not_item_base p fst j;
                          assert(new_or_old fst p = -1 ==> index p j <> fst)
                   | _ -> update_bc_for_minusone_base tl p (i - 1) j

let update_bc_for_minusone_forall_j (l:list english_letters) 
                                    (p:list english_letters) 
                                    (i:nat{i < length l && i < length (update_bc l p)})
  : Lemma (ensures forall (j:nat{j < length p}).  
           (let l' = update_bc l p in
            index l' i = -1 ==> index p j <> index l i))
  = forall_intro (update_bc_for_minusone_base l p i)

let update_bc_for_minusone (l:list english_letters) (p:list english_letters)
  : Lemma (ensures forall (i:nat{i < length l && i < length (update_bc l p)}). (forall (j:nat{j < length p}).  
           (let l' = update_bc l p in
            index l' i = -1 ==> index p j <> index l i)))
  = forall_intro (update_bc_for_minusone_forall_j l p)

let rec update_bc_for_nat_base (l:list english_letters)
                               (p:list english_letters)
                               (i:nat{i < length l && i < length (update_bc l p)}) 
                               (j:nat{j < length p})
  : Lemma (ensures 
           (let l' = update_bc l p in
            index l' i = j ==> index p j = index l i /\ (forall (i':nat{i' > j && i' < length p}). index p i' <> index l i)))
  = update_bc_length_is_initial_list_length l p;
    match l with 
    | [] -> ()
    | fst :: tl -> match i with 
                   | 0 -> assert(update_bc l p = (new_or_old fst p) :: update_bc tl p);
                          assert(index (update_bc l p) i = new_or_old fst p);
                          assert(fst = index l i);
                          if j = new_or_old fst p
                          then (
                            if item_indices (index l i) l 0 <> []
                            then (
                              item_indices_is_in_interval (index l i) l 0 (last (item_indices (index l i) l 0));
                              new_or_old_not_empty_list_correct_item p fst
                            )
                            else ()
                          )
                          else ()
                   | _ -> update_bc_for_nat_base tl p (i - 1) j

let update_bc_for_nat_forall_j (l:list english_letters) 
                               (p:list english_letters)
                               (i:nat{i < length l && i < length (update_bc l p)})
  : Lemma (ensures 
           (let l' = update_bc l p in forall (j:nat{j < length p}).
            index l' i = j ==> index p j = index l i /\ (forall (i':nat{i' > j && i' < length p}). index p i' <> index l i)))
  = forall_intro (update_bc_for_nat_base l p i)

let update_bc_for_nat (l:list english_letters) (p:list english_letters)
  : Lemma (ensures 
           (let l' = update_bc l p in forall (i:nat{i < length l && i < length (update_bc l p)}) (j:nat{j < length p}).
            index l' i = j ==> index p j = index l i /\ 
            (forall (i':nat{i' > j && i' < length p}). index p i' <> index l i)))
  = forall_intro (update_bc_for_nat_forall_j l p)

let rec update_bc_has_values_in_interval (l:list english_letters) (p:list english_letters) (i:nat{i < length (update_bc l p)})
  : Lemma (ensures 
           (let l' = update_bc l p in 
            index l' i = -1 || (index l' i >= 0 && index l' i < length p)))
  = match l with 
    | [] -> ()
    | fst :: tl -> if i = 0 
                   then new_or_old_return_values p fst
                   else update_bc_has_values_in_interval tl p  (i - 1)

let final_bc : list int = update_bc alphabet pattern

let update_bc_has_index_minusone_if_letter_is_not_in_pattern_for_alphabet ()
  : Lemma (ensures forall (i:nat{i < length alphabet && i < length (update_bc alphabet pattern)}). (forall (j:nat{j < length pattern}).  
           (let l' = update_bc alphabet pattern in
            index l' i = -1 ==> index pattern j <> index alphabet i)))
  = update_bc_for_minusone alphabet pattern

let update_bc_has_correct_index_if_letter_is_in_pattern_for_alphabet ()
  : Lemma (ensures 
           (let l' = update_bc alphabet pattern in forall 
            (i:nat{i < length alphabet && i < length (update_bc alphabet pattern)}) (j:nat{j < length pattern}).
            index l' i = j ==> index pattern j = index alphabet i /\ 
            (forall (i':nat{i' > j && i' < length pattern}). index pattern i' <> index alphabet i)))
  = update_bc_for_nat alphabet pattern

let final_bc_has_same_length_as_alphabet () 
  : Lemma (ensures length final_bc = length alphabet)
  = update_bc_length_is_initial_list_length alphabet pattern