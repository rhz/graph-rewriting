graph-rewriting
===============

Graph rewriting library for Scala. It is based on the [`scala-graph`](https://github.com/scala-graph/scala-graph) library.

Installation
------------

1. Clone the repo: `git clone https://github.com/rhz/graph-rewriting.git`

Use
---

1. [Install sbt](http://www.scala-sbt.org/release/docs/Getting-Started/Setup.html#installing-sbt)
2. Enter the REPL: `sbt console` (this should download all necessary packages and compile the project as well)
3. Import the graph rewriting object: `import graph_rewriting.RewritingSystem._`
4. Create some nodes: `val b = "b:bimotor"; val c1 = "c1:chain"; val c2 = "c2:chain"`
5. Create a graph: `val g1 = Graph(b~>c1, b~>c2, c1~>c2)`
6. Create another graph and try taking the intersection of subgraphs of these two graphs for instance: `val g2 = Graph(b~>c1, b~>c1, c1~>c2); intersections(g1, g2)`
7. Play!

License
-------

This software is licensed using the GPLv3 or higher.

Happy modelling!
