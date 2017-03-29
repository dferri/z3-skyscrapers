# z3-skyscrapers
Generate a skyscrapers puzzle game solver for z3

# Usage

The first argument is the size of the grid

Indexes from 0 while the actual skyscraper's height starts from 1

# Example
To solve this puzzle:

![unsolved puzzle](https://i.imgur.com/oxIdeeG.png)

Run the command:

```
python z3-skyscrapers.py 5 r2=2 u1=5 l1=3 d0=3 d3=4 r4c3=2
```

E.g. the file [example.smt2](https://github.com/dferri/z3-skyscrapers/blob/master/example.smt2) was generated with:
```
python z3-skyscrapers.py 5 r2=2 u1=5 l1=3 d0=3 d3=4 r4c3=2 > example.smt2
```

Run and uncomment `(get-model)` to get the solution and fill the grid!

![solved puzzle](https://i.imgur.com/dON5iP1.png)

## Credits
Puzzle's images from [Conceptis Puzzles](http://www.conceptispuzzles.com/index.aspx?uri=puzzle/skyscrapers)
