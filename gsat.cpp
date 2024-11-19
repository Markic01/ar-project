#include <iostream>
#include <vector>
#include <map>
#include <optional>
#include <ctime>
#include <cstdlib>
using namespace std;

typedef unsigned Atom;
typedef int Literal;
typedef vector<Literal> Clause;
typedef vector<Clause> Formula;
typedef vector<bool> Valuation;

void skipRestOfLine(istream& istr) {
    while(istr.get() != '\n');
}

int skipSpaces(istream& istr) {
    int c;
    while((c = istr.get()) == ' ' || c == '\t' || c == '\n');
    return c;
}

bool readDIMACS(Formula& f, unsigned& numVars, istream& istr) {
    unsigned numClauses;
    int c;

    while((c = skipSpaces(istr)) == 'c')
    skipRestOfLine(istr);

    if(c != 'p') {
        return false;
    }
    else {
        string s;
        istr >> s;
        if(s != "cnf") {
            return false;
        }

        istr >> numVars;
        istr >> numClauses;
    }

    for(unsigned i = 0; i < numClauses; ++i) {
        Clause c;
        int n;
        istr >> n; 
        while(!istr.eof() && !istr.fail() && n != 0) {
            c.push_back(n);
            istr >> n;
        }

        if(istr.eof() || istr.fail()) {
            return false;
        }

        f.push_back(c);
    }

    return true;
}

class GSAT {
private:
    Formula _formula;
    int _maxTries;
    int _maxSteps;
    int _numVars;
    bool _useWalk;
    double _threshold;
    // map atoms to clauses that they appear in
    vector<vector<int>> _variableToClauses;
    vector<int> _gain;
    // count how many literals are true in a clause
    vector<int> _trueLiteralsCount;

    bool isSatisfied(const Formula& formula, const Valuation& val) const {
        for (int i = 0; i < formula.size(); ++i) {
            if (_trueLiteralsCount[i] == 0) {
                return false;
            }
        }

        return true;
    }

    Valuation initialize() {
        Valuation val(_numVars+1);
        for (int i = 1; i <= _numVars; ++i) {
            val[i] = rand() % 2;
        }

        fill(_trueLiteralsCount.begin(), _trueLiteralsCount.end(), 0);
        fill(_gain.begin(), _gain.end(), 0);

        for (int i = 0; i < _formula.size(); ++i) {
            for (const Literal l : _formula[i]) {
                Atom a = abs(l);
                if ((l < 0 && !val[a]) || (l > 0 && val[a])) {
                    ++_trueLiteralsCount[i];
                }
            }
        }

        for (int i = 1; i <= _numVars; i++) {
            for (int j : _variableToClauses[i]) {
                if (_trueLiteralsCount[abs(j) - 1] > 1) {
                    continue;
                }

                if (j < 0 && val[i] && _trueLiteralsCount[-j - 1] == 0) {
                    ++_gain[i];
                }

                if (j < 0 && !val[i] && _trueLiteralsCount[-j - 1] == 1) {
                    --_gain[i];
                }

                if (j > 0 && val[i] && _trueLiteralsCount[j - 1] == 1) {
                    --_gain[i];
                }

                if (j > 0 && !val[i] && _trueLiteralsCount[j - 1] == 0) {
                    ++_gain[i];
                }
            }
        }

        return val;
    }

    Atom chooseVarGain() const {
        Atom max = 1;
        for (Atom i = 2; i <= _numVars; ++i) {
            if (_gain[i] > _gain[max]) {
                max = i;
            }
        }

        return max;
    }

    Atom chooseRandomVar() const {
        std::vector<int> unsatisfiedClauses;

        for(int i = 0; i < _formula.size(); ++i) {
            if (_trueLiteralsCount[i] == 0) {
                unsatisfiedClauses.push_back(i);
            }
        }

        int randomIndex = rand() % unsatisfiedClauses.size();
        Clause c = _formula[randomIndex];
        randomIndex = rand() % c.size();
        return abs(c[randomIndex]);
    }

    void flipAtom(const Atom a, vector<bool>& val) {
        val[a] = !val[a];

        for (int i = 0; i < _variableToClauses[a].size(); ++i) {
            int ind = _variableToClauses[a][i];
            int trueLiteralsBefore;

            if (ind < 0) {
                trueLiteralsBefore = _trueLiteralsCount[-ind - 1];
                _trueLiteralsCount[-ind - 1] += val[a] ? -1 : 1;
            }
            else {
                trueLiteralsBefore = _trueLiteralsCount[ind - 1];
                _trueLiteralsCount[ind - 1] += val[a] ? 1 : -1;
            }

            ind = abs(ind) - 1;
            if (_trueLiteralsCount[ind] == 1 && trueLiteralsBefore == 0) {
                // other literals in this clause now don't gain anything when flipping
                for (Literal l : _formula[ind]) {
                    --_gain[abs(l)];
                }
                // not only the flipped literal doesn't gain anything but it also sets current clause to unsatisfied
                --_gain[a];
            }

            if (_trueLiteralsCount[ind] == 1 && trueLiteralsBefore == 2) {
                for (Literal l : _formula[ind]) {
                    if (abs(l) == a) {
                        continue;
                    }

                    if ((l < 0 && !val[abs(l)]) || (l > 0 && val[l])) {
                        // the literal that is left positive, when flipped leaves the clause unsatisfied
                        --_gain[abs(l)];
                        break;
                    }
                }
            }

            if (_trueLiteralsCount[ind] == 2 && trueLiteralsBefore == 1) {
                for (Literal l : _formula[ind]) {
                    if (abs(l) == a) {
                        continue;
                    }

                    if ((l < 0 && !val[abs(l)]) || (l > 0 && val[l])) {
                        ++_gain[abs(l)];
                        // the literal that was positive alone is now not leaving the clause unsatisfied
                        break;
                    }
                }
            }

            if (_trueLiteralsCount[ind] == 0 && trueLiteralsBefore == 1) {
                for (Literal l : _formula[ind]) {
                    // all literals when flipped, make clause satisfied
                    ++_gain[abs(l)];
                }
                // not only flipped literal makes the clause satisfied but it also doesn't make the clause unsatisfied like before
                ++_gain[a];
            }
        }
    }

public:
    GSAT(const int maxTries, const int maxSteps) : _maxTries(maxTries), _maxSteps(maxSteps) {}

    void setFormula(const Formula& formula, const int numVars, const bool useWalk = true, const double threshold = 0.05) {
        _formula = formula;
        _numVars = numVars;
        _useWalk = useWalk;
        _threshold = threshold;
        _variableToClauses.resize(numVars + 1);
        _gain.resize(numVars + 1, 0);
        _trueLiteralsCount.resize(formula.size(), 0);

        for(int i = 0; i < formula.size(); ++i) {
            for (Literal l : formula[i]) {
                if (l < 0) {
                    _variableToClauses[-l].push_back(-(i+1));
                }
                else {
                    _variableToClauses[l].push_back(i+1);
                }
            }
        }
    }

    Atom chooseVarToFlip() const {
        if (_useWalk && (rand() / double(RAND_MAX) < _threshold)) {
            return chooseRandomVar();
        }

        return chooseVarGain();
    }

    optional<Valuation> solve() {
        Valuation val;
        Atom atom;
        for(int i = 0; i < _maxTries; ++i) {
            val = initialize();
            for(int j = 0; j < _maxSteps; ++j) {
                if(isSatisfied(_formula, val)) {
                    return val;
                }
                Atom atom = chooseVarToFlip();
                flipAtom(atom, val);
            }
        }

        return {};
    }
};

int main() {
    std::srand(static_cast<unsigned int>(std::time(0)));
    unsigned num_of_vars;
    Formula f;
    if (!readDIMACS(f, num_of_vars, cin)) {
        cerr << "Error reading input file" << endl;
        exit(1);
    }

    GSAT gsat(3000, 10000);
    gsat.setFormula(f, num_of_vars);

    optional<Valuation> val = gsat.solve();
    if(val) {
        cout << "SAT" << endl;
        for (Atom a = 1; a <= num_of_vars; ++a) {
            cout << a << ": " << ((*val)[a] ? "true" : "false") << endl;
        }
    }
    else {
        cout << "Solution not found" << endl;
    }

    return 0;
}