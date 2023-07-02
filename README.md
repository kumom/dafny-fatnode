# Challenges of verifying persistent data structures

This is the repository for my semester project at EPFL Spring 2023. The project proposal, the final report, and the presentation slides can all be found at the top level. The file `FatNode.dfy` contains the partial verified implementation of the fat node method in Dafny. 

The fat node method is introduced by Driscoll et al. and illustrated in [this paper](https://www.cs.cmu.edu/~sleator/papers/making-data-structures-persistent.pdf). Previously, I have written [a seminar report on this paper](https://kumom.io/articles/persistent-avl). Another relevant approach to make data structures persistent, called path copying, has been implemented and verified [as a course project](https://github.com/kumom?tab=repositories) for AVL trees.

Before reading the report or the slides, it is strongly encouraged to first play with [the visualization](https://kumom.io/persistent-bst) of the fat node method, where the source code can be found [here](https://github.com/kumom/persistent-tree-visualization). 

After reading the report, you may be intrigued to inspect all the interesting snapshots we have collected. An easier way to navigate through these examples is to read [this blog article](https://kumom.io/articles/instability), but you can also directly check out different branches and search for `COMMENT` in the code to inspect the relevant part. Commits in the `main` branch are also interesting snapshots, although they are less representative and harder to understand.

Comments and suggestions are welcomed and should be sent to my private gmail address (see my GitHub profile).

NOTE: We refactored our code in the middle of the project from Dafny 3.13.1 to 4.0.0. Since the syntax of these two versions are not compatible, hopefully it is easy figure out which version to use when navigating through the snapshots.