## Some results obtained from the specification model

The results were obtained using an Intel(R) Core(TM) I5 7400 with 4 workers and 8GB allocated to the model checker.

These results have the goal to see the performance impact of changing the size of the monitors set and the value set.
In the current specification, the value set is a symmetry set, but the monitor set is not. By using a symmetry set the performance of the model improves.

Model with 3 monitors and a value set of size 1:
* Diameter: 62
* Approximated running time: 3min
* Number of distinct states: 7 457 350
* The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 11 and the 95th percentile is 5).

<!-- ![](version-1-3m-1v.png) -->

Model with 3 monitors and a value set of size 2:
* Diameter: 62
* Approximated running time: 11min
* Number of distinct states: 27 323 902
* The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 11 and the 95th percentile is 5).

<!-- ![](version-1-3m-2v.png) -->

Model with 3 monitors and a symmetric value set of size 2:
* Diameter: 62
* Approximated running time: 6min
* Number of distinct states: 13 678 564
* The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 11 and the 95th percentile is 5).
