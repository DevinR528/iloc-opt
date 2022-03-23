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

We are using my interpreter for the commands you will run, but the output and way the interpreter
counts instructions are identical.


| File            | Original | PRE/DCE   | Time     |
| -               | -        | -         | -        |
|`arrayparam.il`  |841       | 364       | 4.41 ms  |
|`bubble.il`      |4374      | 1955?      | 5.83 ms  |
|`check.il`       |140       | 3         | 4.26 ms  |
|`dynamic.il`     |39155     | 17115     | 17.32 ms |
|`fib.il`         |274       | 168       | 3.88 ms  |
|`gcd.il`         |103       | 59        | 3.78 ms  |
|`newdyn.il`      |136919    | 52429     | 19.70 ms |
|`qs.il`          |4574      | 2420      | 6.69  ms |
|`while_array.il` |377       | 185       | 4.44 ms  |

Time includes the time taken to interpret the program; it would be slightly better.
