To run
```
ralloc [opt|or nothing to just interpret] [number of registers]  ./input/file.il
```
So an example would be
```
ralloc opt 12 ./input/check.il
```
to run optimization then allocation with 12 real registers and finally interpret the optimized file.

For this assignment I had to fix a few bugs in the way I did dominator based value numbering since the live
ranges depend on exactly correct phi nodes (you can get away with less connected phi nodes until live ranges).
I have implemented a bottom up coloring of the live range interference graph, I coalesce moves and do very basic
rematerialization. The actual register allocation wasn't super difficult to implement, the problem was that it
forced you to have fix any inconsistencies in SSA numbering and dead code removal. It was important to not have
extra phi so there isn't unnecessary connection in the interference graph.


| File            | Original | LAST      | ALLOC 16(12)  | Time     | Percentage |
| -               | -        | -         | -             | -        | -          |
|`arrayparam.il`  |841       | 366       | 336           | 2 ms     | 60.0%      |
|`bubble.il`      |4374      | 1810      | 1673          | 3 ms     | 61.7%      |
|`check.il`       |140       | 3         | 3             | 0 ms     | 98.5%      |
|`dynamic.il`     |39155     | 13598     | 21315         | 11 ms    | 45.5%      |
|`fib.il`         |274       | 168       | 147           | 0 ms     | 46.3%      |
|`gcd.il`         |103       | 62        | 62            | 1 ms     | 42.7%      |
|`newdyn.il`      |136919    | 41556     | 57880         | 12 ms    | 57.7%      |
|`qs.il`          |4574      | 2443      | 2203          | 5  ms    | 51.8%      |
|`while_array.il` |377       | 176       | 155           | 1 ms     | 58.8%      |

| File            | Original | LAST      | ALLOC  12(8)  | Time     | Percentage |
| -               | -        | -         | -             | -        | -          |
|`arrayparam.il`  |841       | 366       | 336           | 2 ms     | 56.7%      |
|`bubble.il`      |4374      | 1810      | 1760          | 3 ms     | 59.7%      |
|`check.il`       |140       | 3         | 3             | 0 ms     | 98.5%      |
|`dynamic.il`     |39155     | 13598     | 22511         | 11 ms    | 42.5%      |
|`fib.il`         |274       | 168       | 147           | 0 ms     | 38.6%      |
|`gcd.il`         |103       | 62        | 62            | 1 ms     | 42.7%      |
|`newdyn.il`      |136919    | 41556     | 71423         | 7 ms     | 47.8%      |
|`qs.il`          |4574      | 2443      | 2410          | 5  ms    | 47.3%      |
|`while_array.il` |377       | 176       | 155           | 1 ms     | 58.8%      |

Time is ONLY the time taken to optimize the program.
