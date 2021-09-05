## Some results obtained from the specification model

The results were obtained using an Intel(R) Core(TM) I5 7400 with 4 workers and 8GB allocated to the model checker.

These results have the goal to see the performance impact of changing the size of the monitors set and the value set.

The conditions to stop the model are:
* Epoch less than 8 (limit to 3 election cycles).
* Last committed version less than 2.
* Accepted proposal number less than 300.

## Results

Model with 3 monitors and a value set of size 2:
* Diameter: 53
* Approximated running time: 6s
* Number of distinct states: 246 713
* The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 7 and the 95th percentile is 4).

Model with 4 monitors and a value set of size 2:
* Diameter: 70
* Approximated running time: 3min
* Number of distinct states: 4 842 173
* The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 9 and the 95th percentile is 5).
