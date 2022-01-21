Original instruction counts

| File            | Original | LVN   | SSA DBRE | SSA DCE | RA        | % Reduction |
| -               | -        | -     | -        | -       | -         | -           |
|`arrayparam.il`  |841       |487    | 465      | 443     | 443       | 47.3%       |
|`bubble.il`      |4374      |2855   | 2736     | 2481    | 2481      | 43.3%       |
|`check.il`       |140       |130    | 120      | 3       | 3         | 97.9%       |
|`dynamic.il`     |39155     |23579  | 19448    | 18434   | **19311** | 50.7%       |
|`fib.il`         |274       |252    | 232      | 211     | 211       | 23%         |
|`gcd.il`         |103       |83     | 78       | 73      | 73        | 29.1%       |
|`newdyn.il`      |136919    |82256  | 67755    | 64270   | **65204** | 52.4%       |
|`qs.il`          |4574      |3468   | 3373     | 3073    | 3073      | 32.8%       |
|`while_array.il` |377       |315    | 293      | 255     | 255       | 32.4%       |

My instruction counts

| File            | Original | LVN    | SSA DBRE | SSA DCE | RA        | % Reduction |
| -               | -        | -      | -        | -       | -         | -           |
|`arrayparam.il`  |841       |+ 547   | N/A      | N/A     | N/A       | 47.3%       |
|`bubble.il`      |4374      |+ 3102  | N/A      | N/A     | N/A       | 43.3%       |
|`check.il`       |140       |= 130   | N/A      | N/A     | N/A       | 97.9%       |
|`dynamic.il`     |39155     |- 23117 | N/A      | N/A     | N/A       | 50.7%       |
|`fib.il`         |274       |= 252   | N/A      | N/A     | N/A       | 23%         |
|`gcd.il`         |103       |+ 86    | N/A      | N/A     | N/A       | 29.1%       |
|`newdyn.il`      |136919    |- 80402 | N/A      | N/A     | N/A       | 52.4%       |
|`qs.il`          |4574      |+ ????  | N/A      | N/A     | N/A       | 32.8%       |
|`while_array.il` |377       |= 315   | N/A      | N/A     | N/A       | 32.4%       |