This is my bachelor thesis, where I implemented and I verified the Boyer-Moore-Horspool algorithm in F*. The thesis is divided in the following files: <br />
1)GlobalData.fst - the file where I described the input data for the algorithm;
2)ItemIndices.fst - a function for returning a list with the indices where a certain value occurs in a list;
3)NewOrOld.fst - a function that returns -1 if a character is not in a list, and the last position of the character in the list otherwise;
4)UpdateBc.fst - a function that makes the bc array for the preprocessing part;
5)Belongs.fst - a function that returns true if a substring is part of a string and false otherwise;
6)BoyerMooreHorspool.fst - the main algorithm;
7)Main.fst - the file where the instructions for printing the result are written;
8)MainProof.fst - this file contains all of the code from the previous files put together;
All of the functions in these files contains proofs of certain criteria.
