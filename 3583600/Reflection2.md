Grade

  Completing 2a : 3 points
  Adding Pairs : 1 point
  Completing 2b : 2.3 points
  
Total : 7.3

Completing 2a

Big-Step semantics were defined properly, completeness and soundness was proven, all other parts were completed as well. An implicit argument was forgotten in prepend-step.

Adding Pairs

Adding pairs was difficult. Big-Step pairs were defined, although they differed in some details. Mistakes were also made with adding Pairs in small-step semantics, mainly them operating on terms instead of values.
The four functions between big-step definition and sound/complete were done, although had tons of yellow in them - and due to semantic definitions were incorrect.
Soundness was done. Completeness basically had the same thing as in the provided answer, but I could not solve it there - this should have been an indication that my
Big-Step semantics were incorrect. Many holes were also left open in the small-step semantics proofs.

Completing 2b

Whilst I see the general idea behind the proof - proof normalization in order to prove termination, completing this was not easy.
I've reasoned both from the start of the file and the end of the file, ending up at closure-normalization and unable to finish the 
proofs there.

The difficulty lies in both that a wrong case expansion can and will spell doom upon your efforts, and that you can't exactly reason about
what you need to complete a proof - for example I would have gotten Var if I knew that i needed an additional Lemma. 
I also knew that I needed an additional lemma to prove Abs, but I did not know how to formulate it.
