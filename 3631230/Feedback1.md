Grading:
1
0.5
0
1
0.25
0.5
0
0.25
0

Total: 1 + the above = 4,5

1: Correct
2: Hole in idMatrix. It is difficult to program it instantly in agda, but if you visualize what you exactly want to do (or program it in haskell) you can figure it out.

2x Hole in Transpose. Again, same can be done as above.

3: Hole in plan. Use C-c C-, to figure out what the goal here is, and try to program towards that.
Forget is incorrect, which spills over to embed and correct.

4: 
Wrong answer in difference function, you should return Succ k / Zero / Succ k.

5: Holes in plusSucc, plusCommutes and distributivity.

For the first hole in plusSucc, you could try entering C-c C-, and see that both sides have a Succ, which you can remove using the cong function. Then, entering recursion may not be a bad idea, so you enter cong Succ (plusSucc ? ? ) and C-c C-a all the way to the end.

6: For sublistTrans, you could have tried going in recursion in the holes, and C-c C-a all the way to the answer. SubListAntiSym makes use of magic, which is against the Genevan Convention, so you get free points for that.

7 (8 in the answer model): No answers here :(

7 (this is 7 in the answer model): You got the first hole plugged, so 0.25 points for that.

9: Not finished. Nowhere is required that you make use of dependent types when scopechecking, so you could have literally just made a function to check depth of a variable (remember de bruijn indices), making this the easiest exercise in the entire set.

The issues you had with this can be easily fixed be either:

1) Starting earlier
2) Ask for hints from fellow students. There is a very clear line between fraud (working together) and just discussing ways to solve the problem. A basic hint such as using a Base and Step construction in Exercise 7 would have netted you all the points,
the agda tricks with C-c and C-, would have gotten you some points as well, and trying harder to go in recursion would have easily made your grade a 7.
