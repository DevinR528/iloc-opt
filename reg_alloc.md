To run
```
pre ./input/file.il
```

For this assignment I had to fix a few bugs in the way I did dominator based value numbering since the live
ranges depend on exactly correct phi nodes (you can get away with less connected phi nodes until live ranges).
I have implemented a bottom up coloring of the live range interference graph, I coalesce copies and do very basic
rematerialization.


| File            | Original | LAST      | ALLOC 16  | ALLOC  12 | Time     | Percentage |
| -               | -        | -         | -         | -         | -        | -          |
|`arrayparam.il`  |841       | 366       | 366       | ???       | 2 ms     | 56.7%      |
|`bubble.il`      |4374      | 1810      | 1808      | ???       | 4 ms     | 55.9%      |
|`check.il`       |140       | 2         | 2         | 2         | 0 ms     | 98.5%      |
|`dynamic.il`     |39155     | 13598     | 22064     | ???       | 15 ms    | 56.2%      |
|`fib.il`         |274       | 168       | 168       | ???       | 0 ms     | 38.6%      |
|`gcd.il`         |103       | 62        | 62        | ???       | 1 ms     | 42.7%      |
|`newdyn.il`      |136919    | 41556     | 62121     | ???       | 12 ms    | 61.7%      |
|`qs.il`          |4574      | 2443      | 2443      | ???       | 5  ms    | 47.0%      |
|`while_array.il` |377       | 176       | 176       | ???       | 1 ms     | 50.9%      |

Time is ONLY the time taken to optimize the program.
