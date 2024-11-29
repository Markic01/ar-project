# Stochastic SAT Solver

This project implements **stochastic SAT solvers**, specifically **GSAT** and **WalkSAT**, for solving satisfiability problems in **DIMACS CNF format**.

## Features
- **GSAT**: Greedy SAT solving strategy for optimizing variable assignments.
- **WalkSAT**: A stochastic local search method using randomness to escape local optima.
- The program uses heuristic methods to solve SAT problems and outputs the solution if found.

## How It Works
The program:
1. Reads the CNF formula from an input file in **DIMACS format**.
2. Initializes a random variable valuation.
3. Uses **GSAT** or **WalkSAT** to iteratively improve the solution.
4. Outputs either a satisfying assignment (`SAT`) or a message indicating no solution was found within the given limits.

## Requirements
- **C++ Compiler**: Make sure you have a C++ compiler, such as `g++`.

## Compilation and Execution
1. **Compile the Program**  
   Run the following command to compile:
   ```bash
   g++ -o stochasticSAT stochasticSAT.cpp

2. **Run it**  
   Run the following command to compile:
   ```bash
   ./stochasticSAT < dimacs.in
   ```
## Output
- If the formula is satisfiable and the algorithm finds a solution, the output will look like:
```yaml
SAT
1: true
2: false
...
```
- If no satisfying valuation is found:
```
Solution not found
```

⚠️ Note: The algorithm uses heuristics, so it is possible that a solution exists but is not found due to the stochastic nature of the search process. Adjusting parameters like maxTries, maxSteps, or the WalkSAT threshold may improve results for certain formulas.