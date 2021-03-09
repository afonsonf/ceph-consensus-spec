## Some results obtained from the specification model

The results were obtained using an Intel(R) Core(TM) I5 7400 with 4 workers and 8GB allocated to the model checker.

These results have the goal to see the performance impact of changing the size of the monitors set and the value set.

The conditions to stop the model are:
* Epoch less than 6 (limit to 2 election cycles).
* Number of monitor crashes less than 3.
* Last committed version less than 2.
* Accepted proposal number less than 300.

In the current specification, the value set is a symmetry set, but the monitor set is not. By using a symmetry set the performance of the model improves.

Model with 3 monitors and a value set of size 1:
* Diameter: 46
* Approximated running time: 3min
* Number of distinct states: 6 861 067
* The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 10 and the 95th percentile is 5).

Model with 3 monitors and a value set of size 2:
* Diameter: 46
* Approximated running time: 10min
* Number of distinct states: 25 092 769
* The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 11 and the 95th percentile is 5).

Model with 3 monitors and a symmetric value set of size 2:
* Diameter: 46
* Approximated running time: 6min
* Number of distinct states: 12 566 200
* The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 11 and the 95th percentile is 5).
