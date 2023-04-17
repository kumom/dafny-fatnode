# Verified Persistent Trees

## Project description

A persistent data structure is a structure that allows to have access to previous versions and act on them. Such data structures can be used to simulate immutable data structures, since their operations do not visibly update the structure in-place, but instead always yield a new updated structure. The term was introduced in Driscoll, Sarnak, Sleator, and Tarjans' 1986 paper [1]. The paper [1] introduces several ways to make pointer-based data structures partially and fully persistent. A partially persistent data structure allows lookup on previous versions, while a fully persistent data structure allows additionally modification on previous versions. The best approach, called node copying method for partial persistence and node splitting method for full persistence, achieves amortized constant time for both lookup and modification, given that the original data structure (more precisely, the *ephemeral* data structure) has bounded in-degree for every node. For a short overview, one can refer to [my seminar report that describes how to make an AVL tree persistent using the approaches from the paper [1]](https://kumom.io/articles/persistent-avl).

This project aims to use Dafny to implement and verify the fat node method for a partially persistent binary search tree, which has a logarithmic blowup for each lookup operation and only constant additional time for insertion and deletion. To compare it with the standard approach - making data structures immutable - that is taken in many functional programming languages (e.g., Closure), we need to consider the pros and cons from using fat node method or node copying/splitting method. An immutable binary search tree has no additional lookup time because for every modification a new binary search tree will be returned. We can simply build an interface that stores all the returned roots and perform lookup or modification operations using these root pointers with timestamps. However, the space complexity would be huge if a node in the structure is big, because the immutable data structure essentially implements the so-called path copying method, i.e., it copies all the nodes it encounters along the way when it performs modification. From a more practical point of view, it is important to take into account that immutable data structures do not guarantee cache locality, and its lookup time may not be constant in reality if we frequently access data structures of several previous versions. Through this point of view, it seems natural to have a persistent data structure that saves space complexity while keeping time complexity reasonable. 

The fat node method is a general approach that can be used to implement both partially and fully persistent data structures. The high-level idea is to store relevant updates inside the node and allow to node to grow as "fat" as it can. A node in an ephemeral binary search tree would have three fields `value: int`, `left: Node?`, and `right: Node?`, while a persistent node implemented using the fat node method would have three sequences `values: seq<(int, int)>`, `lefts: seq<(int, Node?)>`, and `rights: seq<(int, Node?)>`. The first element in the tuple is the timestamp. For example, an entry `(3, 5)` in `value` means at timestamp 3, this node has value `5`. 

The persistent binary search tree is a shared mutable data structure under the hood. Using Dafny means we need to use dynamic frames to specify the data sharing situation. It may come as surprise for people who do not know enough about formal verification to see a shared mutable data structure is much more difficult to verify than an immutable data structure. One can first have a look at [my previous course project that used Stainless to verify an immutable AVL tree](https://github.com/kumom/cs550-persistent-avl-tree) and wait for the results of this project to compare the difficulty of verification for these two approaches. 

*A paper published in 2003 [2] introduces an approach to implement confluently persistent data structure, which in addition to lookup and modification on previous versions, also allows melting two previous versions. One can think of this melt operation as similar to merge in version control system.*

## Timeline

### 15.02 - 30.04

- Implement the fat node method for partially persistent BST in Dafny.
- Verify the implementation of the fat node method using Dafny.

### 30.04 - 31.05

- Generalize the tricks to solve performance issues (timeout) encountered in the project.
- Visualize the data structure.

### 01.06 - 08.06 (submission date: 09.06)

- Rewrite the seminar report that was based on AVL instead of BST.
- Write the semester report.

## References

[1] Driscoll, J. R., Sarnak, N., Sleator, D. D., & Tarjan, R. E. (1986, November). Making data structures persistent. In Proceedings of the eighteenth annual ACM symposium on Theory of computing (pp. 109-121).

[2] Fiat, A., & Kaplan, H. (2003). Making data structures confluently persistent. Journal of Algorithms, 48(1), 16-58.
