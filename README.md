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

    ```scala
    // Instantiate a Graph constructor of the selected type
    val G = Graph.withType[String,String,IdDiEdge[Int,String],String]
    // Creates an edge from u to v.
    val e = "u" ~~> "v"
    // Creates a graph with a red and a blue node, and
    // an edge from the red node to the blue node.
    val rb = G("u" -> "red", "v" -> "blue")(e)
    // Creates a blue node to blue node graph.
    val bb = G("u" -> "blue", "v" -> "blue")(e)
    // Creates a red node to red node graph.
    val rr = G("u" -> "red", "v" -> "red")(e)
    // Creates a rule that transforms a red-to-blue subgraph into a
    // red-to-red one by changing the label on "u" from "red" to "blue".
    // The two maps are required to know what nodes and edges are
    // preserved by the rule, ie not destroyed nor created.  In this case,
    // every node and edge is preserved (but not necessarily their labels).
    val b2r = Rule(rb, rr, Map("u" -> "u", "v" -> "v"), Map(e -> e), "kBR")
    val r2b = Rule(rb, bb, Map("u" -> "u", "v" -> "v"), Map(e -> e), "kRB")
    ```

2. Define a set of observables

    ```scala
    val red = G("u" -> "red")()
    ```

3. (Optional) Define a set of transformers on graphs
4. Compute the mean-field approximation and write the resulting set of equations to the standard output and an [Octave](https://www.gnu.org/software/octave/) file

    ```scala
    import meanfield._
    val eqs = mfa(1, List(r2b, b2r), List(red))
    ODEPrinter(eqs).print // print to standard output
    startTime = 0.0
    finalTime = 10.0
    numSteps = 1000
    ODEPrinter(eqs).saveAsOctave("filename.m", startTime, finalTime, numSteps,
      // function that defines the initial concentration of an observable
      g => if (Graph.iso(g, red)) 1.0 else 0.0)
    ```

Have a look at [VoterModel.scala](https://github.com/rhz/graph-rewriting/blob/master/src/test/scala/graph-rewriting/VoterModel.scala), [Rabbits.scala](https://github.com/rhz/graph-rewriting/blob/master/src/test/scala/graph-rewriting/Rabbits.scala), and [Bimotor.scala](https://github.com/rhz/graph-rewriting/blob/master/src/test/scala/graph-rewriting/Bimotor.scala) for more examples on how to use this tool to derive mean-field approximations of your graph transformation systems.

Papers
------

- "[Approximations for stochastic graph rewriting](http://www.pps.univ-paris-diderot.fr/~danos/pdf/icfem.pdf)". Vincent Danos, Tobias Heindel, Ricardo Honorato-Zimmer, Sandro Stucki. ICFEM, 2014.
- "[Moment Semantics for Reversible Rule-Based Systems](http://infoscience.epfl.ch/record/210228/files/momsem_1.pdf)". Vincent Danos, Tobias Heindel, Ricardo Honorato-Zimmer, Sandro Stucki. Reversible Computation, 2015.
- "[Computing approximations for graph transformation systems](http://webconf.inrialpes.fr/wp-content/uploads/sites/9/2015/06/memo2015-preproc.pdf#page=37)". Vincent Danos, Tobias Heindel, Ricardo Honorato-Zimmer, Sandro Stucki. MeMo 2015, 2015.

Roadmap
-------

1. Pair approximation and approximate master equation transformers
3. LaTeX and DOT output
3. Simulation

License
-------

This software is licensed using the GPLv3 or higher.

Happy modelling!
