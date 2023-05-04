# Verified Persistent Trees

## Abbreviations

Partially Persistent Tree - PPT

Fully Persistent Tree - FPT

Confluently Persistent Tree - CPT

## Project description

A persistent data structure is a structure that allows to have access to previous versions and act on them. Such data structures are effectively immutable, as their operations do not (visibly) update the structure in-place, but instead always yield a new updated structure. The term was introduced in Driscoll, Sarnak, Sleator, and Tarjans' 1986 article [1].

This project aims to implement and verify the algorithms introduced in the same paper [1] that can make all linked data structures persistent. There are three kinds of persistent data structures: PPT, FPT, and CPT. In the paper [1], only PPT and FPT are discussed. In 2003, there is a paper [2] on CPT, focusing on achieving good space complexity. (If you think about it, we really care more about space complexity because an immutable data structure has NO additional lookup time...)


The Wikipedia page for [Persistent data structure](https://en.wikipedia.org/wiki/Persistent_data_structure#cite_note-Driscoll-1) is quite detailed, although its usages of *persistence* and *immutable* are inconsistent, so you will find lots of confusing (or even wrong) statements in the section `Usage in programming languages`.

## Timeline

### Before 07.04

Verify the implementation of fat node method for partial persistent BST.

### 07.04 - 17.04

Implement the node copying method for partially persistent BST.
Rewrite the seminar report that was based on AVL instead of BST.

### 01.05 - 31.05

Verify the node copying method.

### 01.06 - 08.06 (submission date: 09.06)

Write the semester report.


## References

[1] Driscoll, J. R., Sarnak, N., Sleator, D. D., & Tarjan, R. E. (1986, November). Making data structures persistent. In Proceedings of the eighteenth annual ACM symposium on Theory of computing (pp. 109-121).

[2] Fiat, A., & Kaplan, H. (2003). Making data structures confluently persistent. Journal of Algorithms, 48(1), 16-58.
