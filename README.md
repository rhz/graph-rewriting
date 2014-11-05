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

### Mean field approximations

1. Define a set of rules

        // Creates an edge from u to v.
        val e = "u" ~~> "v"
        // Creates a graph with a red and a blue node, and
        // an edge from the red node to the blue node.
        val rb = Graph("u" -> "red", "v" -> "blue")(e)
        // Creates a blue node to blue node graph.
        val bb = Graph("u" -> "blue", "v" -> "blue")(e)
        // Creates a red node to red node graph.
        val rr = Graph("u" -> "red", "v" -> "red")(e)
        // Creates a rule that transforms a red-to-blue subgraph into a
        // red-to-red one by changing the label on "u" from "red" to "blue".
        // The two maps are required to know what nodes and edges are
        // preserved by the rule, ie not destroyed nor created.  In this case,
        // every node and edge is preserved (but not necessarily their labels).
        val b2r = Rule(rb, rr, Map("u" -> "u", "v" -> "v"), Map(e -> e), 1)
        val r2b = Rule(rb, bb, Map("u" -> "u", "v" -> "v"), Map(e -> e), 10)

2. Define a set of observables

        val red = Graph("u" -> "red")()

3. (Optional) Define a set of transformers on graphs
4. Compute the mean-field approximation and print the resulting set of equations

        import meanfield._
        val eqs = mfa(1, List(r2b, b2r), List(r))
        eqs.printEqs

Have a look at [VoterModel.scala](https://github.com/rhz/graph-rewriting/blob/master/src/test/scala/graph-rewriting/VoterModel.scala), [Rabbits.scala](https://github.com/rhz/graph-rewriting/blob/master/src/test/scala/graph-rewriting/Rabbits.scala), and [Bimotor.scala](https://github.com/rhz/graph-rewriting/blob/master/src/test/scala/graph-rewriting/Bimotor.scala) for more examples on how to use this tool to derive mean-field approximations of your graph transformation systems.

Roadmap
-------

1. Pair approximation and approximate master equation transformers
2. Module for [mois](https://github.com/edinburgh-rbm/mois/)
3. Octave/Matlab output
4. DOT output
5. Simulation

License
-------

This software is licensed using the GPLv3 or higher.

Happy modelling!
