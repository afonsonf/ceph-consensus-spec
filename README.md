# TLA+ specification of the Ceph consensus algorithm

This is a formal specification of the Ceph consensus algorithm (based on Paxos). <br>
The specification is based on the following source file: https://github.com/ceph/ceph/blob/master/src/mon/Paxos.cc.<br>
The specification is written in the TLA+ language https://lamport.azurewebsites.net/tla/tla.html.

A detailed description of the model can be found at: [description.md](description.md)
<br>
Results of the model can be found at: [results](results)

Some of the useful things that can be done with this model are:
* Prove safety and liveness properties of the implemented algorithm. Test new versions of the algorithm to see if properties still hold.
* Possibility of creating traces of segments of the algorithm and see how the variables change (example: [trace-example](trace-example)).
* Make interactive visualizations of the algorithm (such as this one: https://github.com/afonsonf/tlaplus-graph-explorer).
* Analyse statistics of the state machine generated from the algorithm.
* Debug the algorithm. Search behaviours that lead to certain configurations and study what can happen from there.

## How to run using TLC

The specification is in the src folder and the main file is the [src/ceph.tla](src/ceph.tla). The file [src/ceph.cfg](src/ceph.cfg) has a description of a model with 3 monitors.

The folder src/ceph.toolbox has some default settings used by the toolbox.

#### Using the Command-Line tools

1. Get tla2tools.jar from https://github.com/tlaplus/tlaplus/releases and CommunityModules.jar from https://github.com/tlaplus/CommunityModules/releases. Alternatively there is a copy of the files in the [tools](tools) folder.

2. Some available tools (https://lamport.azurewebsites.net/tla/standalone-tools.html):
  * Syntax checker: <br>
  `java -cp tla2tools.jar tla2sany.SANY ceph.tla`

  * Model checker: <br>
  `java -DTLA-Library=CommunityModules.jar -cp tla2tools.jar tlc2.TLC -workers 4 ceph.tla`

  * Interactive TLA+ REPL (version 1.8 or above): <br>
  `java -cp tla2tools.jar tlc2.REPL`

Alternatively, you can use the Dockerfile to create a container with the TLA+ tools. <br>
The container comes with alias to run the tools, respectively: tla-sany, tla-tlc, tla-trace and tla-repl.

1. Create the container: <br>
`docker build -t tla .`

2. Run the container and mount src folder: <br>
`docker run --rm -v $PWD/src:/src -it tla`

#### Using the TLA+ Toolbox

The toolbox can be downloaded from https://github.com/tlaplus/tlaplus/releases. The main file to load in the toolbox is ceph.tla in the src folder.

## Apalache
[Apalache](https://apalache.informal.systems) is a symbolic model checker for TLA+, as an alternative to TLC. Apalache translates the specification to a set of logical constraints that are solved using Microsoft's Z3. Apalache also comes with a type checker named snowcat (https://apalache.informal.systems/docs/apalache/typechecker-snowcat.html).

#### Type check using apalache's snowcat
The snowcat type checker can infer and check the types of the expressions in a specification. Both the specification in [apalache-version](apalache-version) and [src](src) have type annotations that can be checked with the following command: <br>
`apalache typecheck ceph.tla`

#### Model check using apalache
In the folder [apalache-version](apalache-version) there is a specification that was adapted to be able to run using apalache. However, in the current version, the specification takes to long to run in apalache.

To run the model checker you can use the following command: <br>
`apalache --cinit=InitConst check ceph.tla`
