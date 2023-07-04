# Challenges of verifying persistent data structures

This is the repository for my semester project at EPFL Spring 2023. The project proposal, the final report, and the presentation slides can all be found at the top level. The file `FatNode.dfy` contains the verified (but partial) implementation of the fat node method for binary search trees in Dafny. Specifically, only a single if-else branch of `Insert` is verified, and we have not got to implement and verify `Remove` in Dafny by the end of this project.

Before reading the report or the slides, it is strongly encouraged to first play with [the visualization](https://kumom.io/persistent-bst) of the fat node method. [The source code](https://github.com/kumom/persistent-tree-visualization) contains a complete implementation of the fat node method for partially binary search trees in TypeScript.

The fat node method is introduced by Driscoll et al. in [this paper](https://www.cs.cmu.edu/~sleator/papers/making-data-structures-persistent.pdf). A better approach, named node copying, is illustrated in the same paper and achieves constant amortized time and space complexity. Previously, I have written [a seminar report](https://kumom.io/articles/persistent-avl) that applies the same techniques on AVL trees. Another approach to make data structures partially persistent, called path copying, has been implemented and verified [as a course project](https://github.com/kumom?tab=repositories) for AVL trees. 


After reading the report, you may be intrigued to inspect all the interesting snapshots we have collected. An easier way to navigate through these examples is to read [this blog post](https://kumom.io/articles/instability), but you can also directly check out different branches and search for `COMMENT` in the code to inspect the relevant part. Commits in the `main` branch are also interesting snapshots, although they are less representative and harder to understand.

Comments and suggestions are welcomed.

NOTE: We refactored our code in the middle of the project from Dafny 3.13.1 to 4.0.0. Since the syntax of these two versions are not compatible, hopefully it would be easy to figure out which version to use when navigating through the snapshots.