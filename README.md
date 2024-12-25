# zddb

zddb is a command line tool reprints a text file, lines sorted and uniqued. It
is the same as `sort -u`. Internally it builds up a ZDD per line of text, unions
them, and then enumerates every set stored in the ZDD, printing them. The
purpose is to serve as example code to show fast unioning of many ZDDs. The
`multiunion` function unions all the ZDDs in one shot without creating any
temporary ZDDs.

A ZDD stores a set-of-sets, which to keep the two sets distinct we'll call a
family-of-sets. The set members we'll call by names v0, v1, v2 and so on. A ZDD
is built out of `if-then-else` nodes that form a decision diagram.

Starting with a set in hand and querying whether it's present in the ZDD, each
if-then-else node asks us about a value and tells us which node is next
depending on whether the value is present in our set in hand. We are asked
about each value zero or one times, always in ascending order. If the set in
hand contains a value and there is no if-then-else querying us about that value
(we can always see whether we've skipped over it, including going to the
terminal node), then we stop as the family does not contain the set.

For example:

```
[0]: If (v3) Then [1] Else [5]
[1]: If (v5) Then [2] Else [5]
[2]: If (v6) Then [3] Else [5]
[3]: If (v7) Then [4] Else [5]
[4]: If (v8) Then [6] Else [6]
[5]: Done, not present.
[6]: Done, present.
```

This ZDD represents a family of two sets
`{ { v3, v5, v6, v7 }, { v3, v5, v6, v7, v8 } }`. It can also be viewed
graphically:

![Visualization of ZDD](https://g.gravizo.com/source/custom_markexample1?https%3A%2F%2Fraw.githubusercontent.com%2Fnlewycky%2Fzddb%2Fmaster%2FREADME.md)
<details>
<summary></summary>
custom_markexample1
digraph example1 {
  node[shape=square]
  { rank=same;
    n0[label="LO"]
    n1[label="HI"]
  }
  n2[label="v3", peripheries=2]
  n3[label="v5"]
  n4[label="v6"]
  n5[label="v7"]
  n6[label="v8"]
  n2:sw -> n0[style=dashed]
  n2:se -> n3
  n3:sw -> n0[style=dashed]
  n3:se -> n4
  n4:sw -> n0[style=dashed]
  n4:se -> n5
  n5:sw -> n0[style=dashed]
  n5:se -> n6
  n6:sw -> n1[style=dashed]
  n6:se -> n1
}
custom_markexample1
</details>

The formal definition of a ZDD is any directed oriented graph with two terminal
nodes labelled `LO` and `HI` and all non-terminal nodes have a label and two
out-edges `lo` and `hi` which point to nodes with a greater label (`LO` and `HI`
sort greatest). No node has its `hi` edge pointing to the `LO` node. There are
no two nodes with the same label, `lo` edge destination, and `hi` edge
destination.

As a consequence of this definition, every node has a path to `HI`. Each path
from the root node to `HI` represents one of the sets contained in the ZDD.
Given a valid ZDD you could pick any node to be the root and it would form
another valid ZDD.

## Compiling

zddb is written in C++23.

```sh
$(CXX) -std=c++23 zddb.cc -o zddb
```

Please add `-O2 -DNDEBUG` for performance builds.

## References

 * https://crypto.stanford.edu/pbc/notes/zdd/zdd.html
 * https://www.youtube.com/watch?v=-HzQYeqS9Wc
