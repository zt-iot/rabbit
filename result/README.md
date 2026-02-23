\[WIP\]

## Trace Graph
Trace graph is a graph for visualization of the verification result using Rabbit code fragments.

- Each node is divided into 2 layers. The upper layer is preconditions field, which shows what guard conditions are required in case or loop operation. The lower layer is effects field.
- In each block of nodes, the code fragment and the location of it are written. 
  - **Note**: For now, when a syscall is executed, the definition location is displayed.
- Each directed edge means a constraint on the execution order. Black edges represent communication between processes, and light gray edges represent the other constraints such as control flow.

## Translation of the result

First, to output a metadata file `camserver.spthy.sexp` along with a Tamarin file, run Rabbit with `--aux-file` flag:
```bash
dune exec rabbit -- examples/camserver.rab -o camserver.spthy --aux-file
```

Then, to generate a dependency graph (as DOT file), run Tamarin with `--output-dot=FileName` or `--od=FileName` flag:
```bash
tamarin-prover camserver.spthy --prove= --output-dot=camserver_dep.dot
```

Finally, translate the graph from Tamarin to Rabbit:
```bash
dune exec result -- camserver_dep.dot --with camserver.spthy.sexp -o camserver_trace.dot
```

To convert a DOT file into a graph image, you can use Graphviz ([https://graphviz.org](https://graphviz.org)) like this:
```bash
dot -Tsvg -O camserver_trace.dot
```