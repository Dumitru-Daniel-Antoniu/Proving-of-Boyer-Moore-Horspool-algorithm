## Proving of Boyer-Moore-Horspool algorithm

This is my bachelor thesis, where I implemented and I verified the Boyer-Moore-Horspool algorithm in F*. The thesis is divided in the following files: <br />
* GlobalData.fst - the file where I described the input data for the algorithm; <br />
2)ItemIndices.fst - a function for returning a list with the indices where a certain value occurs in a list; <br />
3)NewOrOld.fst - a function that returns -1 if a character is not in a list, and the last position of the character in the list otherwise; <br />
4)UpdateBc.fst - a function that makes the bc array for the preprocessing part; <br />
5)Belongs.fst - a function that returns true if a substring is part of a string and false otherwise; <br />
6)BoyerMooreHorspool.fst - the main algorithm; <br />
7)Main.fst - the file where the instructions for printing the result are written; <br />
8)MainProof.fst - this file contains all of the code from the previous files put together. <br />
All of the functions in these files contains proofs of certain criteria. Except MainProof.fst, all of the files have also a .checked file generated.
