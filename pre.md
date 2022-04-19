To run
```
pre ./input/file.il
```

For this assignment I finished SSA based dead code elimination and implemented partial redundancy elimination.
The DCE pass took me the majority of time this month, I spent at least 2 and half weeks fixing the bad
SSA numbering I was doing. DCE forced me to correct SSA numbering and stop removing certain critical instructions.
The PRE pass, once I got correct initial sets (Available/Anticipated/Transparent/Kill) I was able to implement a
working insertion and removal pass, moving instruction up to predecessor blocks or splitting critical edges by adding
a block between.

I added a loop analysis pass that generates all the loop information, what block is the loop header and what blocks are
part of it's loop. It also can calculate the parents of any nested loops. This was used for `bubble.il` where normal PRE
seems to want to move instruction deeper into the nested loop causing higher instruction count. With loop detection I can
determine when this is a net loss or find the parent header of nested loops and insert invariant instruction there.

We are using my interpreter for the commands you will run, but the output and way the interpreter
counts instructions are identical.


| File            | Original | PRE/DCE   | Time     | Percentage |
| -               | -        | -         | -        | -          |
|`arrayparam.il`  |841       | 366       | 1 ms     | 56.7%      |
|`bubble.il`      |4374      | 1810      | 1 ms     | 55.9%      |
|`check.il`       |140       | 2         | 0 ms     | 98.5%      |
|`dynamic.il`     |39155     | 13598     | 4 ms     | 56.2%      |
|`fib.il`         |274       | 168       | 0 ms     | 38.6%      |
|`gcd.il`         |103       | 62        | 0 ms     | 42.7%      |
|`newdyn.il`      |136919    | 41556     | 2 ms     | 61.7%      |
|`qs.il`          |4574      | 2443      | 2  ms    | 47.0%      |
|`while_array.il` |377       | 176       | 0 ms     | 50.9%      |

Time is ONLY the time taken to optimize the program.
