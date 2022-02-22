To run
```
ssa ./input/file.il
```

In addition to dominator value numbering redundancy elimination, I implemented constant folding,
constant propagation, and resolution of conditional branch instructions. I also implemented a 
rough dead code elimination pass, but there is no elimination of useless control flow, so
it misses things. I had to remove DCE from the final turn in because I was still working on getting
the post-dominator tree correct.
We are using my interpreter for the commands you will run, but the output and way the interpreter
counts instructions are identical.


| File            | Original | SSA   | Time     |
| -               | -        | -     | -        |
|`arrayparam.il`  |841       | 408   | 4.41 ms  |
|`bubble.il`      |4374      | 1970  | 5.83 ms  |
|`check.il`       |140       | 56    | 4.26 ms  |
|`dynamic.il`     |39155     | 16846 | 17.32 ms |
|`fib.il`         |274       | 168   | 3.88 ms  |
|`gcd.il`         |103       | 62    | 3.78 ms  |
|`newdyn.il`      |136919    | 51557 | 19.70 ms |
|`qs.il`          |4574      | 2589  | 6.69  ms |
|`while_array.il` |377       | 190   | 4.44 ms  |

Time includes the time taken to interpret the program; it would be slightly better.
