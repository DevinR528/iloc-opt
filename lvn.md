To run
```
lvn ./input/file.il
```

In addition to local value number redundancy elimination, I implemented constant folding,
constant propagation, identity transformations of immediate instructions as well as three address,
and combining of compare, test, and branch instruction sequences. We are using my interpreter for 
the commands you will run, but the output and way the interpreter count instruction are identical.


| File            | Original | LVN   | Time        |
| -               | -        | -     | -           |
|`arrayparam.il`  |841       | 442   | 70.18 ms    |
|`bubble.il`      |4374      | 2374  | 69.30 ms    |
|`check.il`       |140       | 87    | 64.73 ms    |
|`dynamic.il`     |39155     | 19129 | 64.10 ms    |
|`fib.il`         |274       | 209   | 62.83 ms    |
|`gcd.il`         |103       | 72    | 75.93 ms    |
|`newdyn.il`      |136919    | 58436 | 65.73 ms    |
|`qs.il`          |4574      | 2907  | 65.31 ms    |
|`while_array.il` |377       | 250   | 64.11 ms    |
