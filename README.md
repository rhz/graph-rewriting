graph-rewriting
===============

Graph rewriting library for Scala.

Installation
------------

1. Clone the repo: `git clone https://github.com/rhz/graph-rewriting.git`

Use
---

1. [Install sbt](http://www.scala-sbt.org/release/tutorial/Setup.html)
2. Enter the REPL: `sbt console` (this should download all necessary packages and compile the project as well)
3. Import the graph rewriting package: `import graph_rewriting._`
4. Create a graph: `val g1 = Graph("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")("b"~~>"c1", "b"~~>"c2", "c1"~~>"c2")`
5. Create another graph and try taking the intersection of subgraphs of these two graphs for instance: `val g2 = Graph("b" -> "bimotor", "c1" -> "chain", "c2" -> "chain")("b"~~>"c1", "b"~~>"c1", "c1"~~>"c2"); intersections(g1, g2)`
6. Play!

License
-------

This software is licensed using the GPLv3 or higher.

Happy modelling!
