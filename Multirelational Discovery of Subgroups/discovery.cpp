// MIDOS subgroup discovery algorithm for binary attributes.

#include <cassert>
#include <cmath>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <algorithm>
#include <utility>
#include <map>
#include <vector>
#include <deque>
#include <queue>

#include <ctime>

using namespace std;

// Store the database of items as a map with keys being item IDs and values
// being pairs, in which
// - the first item is an attribute list (vector<int>).
// - the second item is the target attribute (int).
typedef vector<pair<vector<int>, int>> db;
// Represent a hypothesis as a vector of integers from
// {-n, ... , n} in the natural way, e.g. [1, -2, 4] ~ x1!x2x4.
typedef vector<int> hypothesis;

void get_data(string path, int& m, int& n, int& k, int& F, db& D) {
  /* Set the input parameters m, n, k, F for the algorithm, as well as the
  database D.

  An attribute list is a vector<int> with entries from {-1, 1}, where a `1`
  (resp. `-1`) in the i-th entry corresponds to attribute i being true
  (resp. false).
  */

  ifstream file_in(path);

  file_in >> m >> n >> k >> F;

  string line;
  getline(file_in, line);
  stringstream ss;

  // Read in database of items. This is stored as a dictionary of
  // {TID : (attribute list, target attribute)} pairs.
  for(int i = 0; i < m; i++) {
    getline(file_in, line);
    ss.str(line);

    // Read in attribute list.
    vector<int> attr_list (n);
    string attr_val;
    for (int j = 0; j < n; j++) {
      getline(ss, attr_val, ',');
      attr_list[j] = pow(-1, stoi(attr_val) + 1);  // Convert 0, 1 to -1, 1 resp.
    }

    // Write this item to database.
    getline(ss, attr_val);
    int target = pow(-1, stoi(attr_val) + 1);
    D[i] = pair<vector<int>, int>(attr_list, target);
    ss.clear();
  }
}

vector<int> ext(hypothesis& hyp, vector<int> S, db& D) {
  /* Return a list of the items in S satisfying hyp.

  S is a vector of keys from the map D.
  */

  vector<int> extension;
  for (auto& key : S) {
    bool satisfied = true;
    for (auto& attr : hyp) {
      // If the attribute of this item has opposite value to that
      // specified by the hypothesis:
      if (attr * D[key].first[abs(attr) - 1] < 0) {
        satisfied = false;
        break;
      }
    }
    if (satisfied) {
      extension.push_back(key);
    }
  }
  return extension;
}

vector<hypothesis> refine(hypothesis& hyp, int n) {
  /* Return a vector of the refinements of hyp.

  The Boolean monomials are ordered lexicographically according to the
  rule !x1 < x1 < !x2 < x2 < ... < !xn < xn.
  */

  int j = hyp.empty() ? 0 : abs(hyp.back());
  vector<hypothesis> refinement (2*(n - j));
  for (int attr = j + 1; attr <= n; attr++) {
    hypothesis r (hyp);
    r.push_back(-attr);
    refinement[2*(attr-j-1)] = r;
    r = hyp;
    r.push_back(attr);
    refinement[2*(attr-j-1) + 1] = r;
  }
  return refinement;
}

// Solutions to the subgroup discovery problems are stored as pairs:
// the first entry is the quality, the second is the hypothesis.
typedef pair<double, hypothesis> solution;

vector<solution> midos(int m, int n, int k, int F, db& D, int g_min=0) {
  /* MIDOS algorithm implementation for
  - n binary attributes
  - on a database D
  - of m items,
  - returning the k best subgroups
  - according to quality function F
  - that contain at least g_min items.

  Return a vector of solutions sorted in ascending order of quality.
  */

  // Timing.
  clock_t start;
  double duration;
  start = clock();

  // The following constants are calculated once here and used throughout the algorithm.
  // Proportion of items in database with positive label:
  int positive = 0;
  for (auto& i : D) {
    if (i.second == 1) {  // Count number of items with positive label.
      positive++;
    }
  }
  double p0 = double(positive) / m;
  // For the optimistic estimator later:
  double opt = max(p0, 1-p0);

  auto q = [&] (int F, hypothesis& hyp, vector<int>& S) {
    /* Quality function.

    S is a vector of keys from the database D.
    */

    // The following are respectively the size of ext(hyp, S) = ext(hyp, D),
    // and the number of items in ext(hyp, D) with positive label.
    int s = 0;
    int num_positive = 0;
    for (auto& k : ext(hyp, S, D)) {
      s++;
      if (D[k].second == 1) {
        num_positive++;
      }
    }

    // Now calculate quality.
    double q;
    if (s == 0) {
      q = 0;
    }
    else {
      double g = double(s) / m;
      double p = double(num_positive) / s;

      if (F == 1) {
        q = sqrt(g) * abs(p - p0);
      }
      else if (F == 2) {
        q = g / (1 - g) * pow((p - p0), 2);
      }
      else if (F == 3) {
        q = g * (2*p - 1) + 1 - p0;
      }
    }
    return q;
  };

  auto q_max = [&] (int F, hypothesis& hyp, vector<int>& S) {
    /* Optimistic estimators.
    I know the exercise didn't as us to prune for F = 2, 3, but still.
    */
    int s = 0;
    int num_positive = 0;
    for (auto& k : ext(hyp, S, D)) {
      s++;
      if (D[k].second == 1) {
        num_positive++;
      }
    }
    double g = double(s) / m;
    double q;
    if (F == 1) {
      q = sqrt(g) * opt;
    }
    else if (F == 2) {
      q = g / (1 - g) * pow(opt, 2);
    }
    else {
      q = g + 1 - p0;
    }
    return q;
  };

  // The actual algorithm:

  // Start with the empty hypothesis.
  hypothesis nil;
  // Store hypotheses to check in a queue.
  deque<hypothesis> Q (1, nil);
  // Maintain a min-heap of the k best hypotheses sorted by quality.
  priority_queue<solution, vector<solution>, function<bool(solution,solution)>>
    sols( [](solution a, solution b) -> bool { return a.first > b.first; } );

  // Database item IDs.
  vector<int> D_keys (m);
  for (int i = 0; i < m; i++) {
    D_keys[i] = i;
  }

  hypothesis h0;
  while (!Q.empty()) {
    // Pop parent hypothesis.
    h0 = Q.front();
    Q.pop_front();

    /* We take advantage of monotonicity of the refinement operator w.r.t.
    inclusion, and restrict ourselves to getting the extensions of each child
    hypothesis h in T = ext(h0, D).
    This saves us having to check the entire database D for each child h that we
    consider.
    */
    vector<int> T (ext(h0, D_keys, D));

    for (auto& h : refine(h0, n)) {
      vector<int> S (ext(h, T, D));

      if (S.size() <= g_min) {  // Prune if the extension size is too small.
        continue;
      }

      if (sols.size() < k) {
        double quality = q(F, h, S);
        pair<double, hypothesis> sol (quality, h);
        sols.push(sol);
        Q.push_back(h);
      }
      else {
        // Prune if the optimistic estimate is too small.
        double q_opt = q_max(F, h, S);
        if (q_opt < sols.top().first) {
          continue;
        }

        double quality = q(F, h, S);
        if (quality > sols.top().first) {
          sols.pop();
          pair<double, hypothesis> sol (quality, h);
          sols.push(sol);
        }

        Q.push_back(h);
      }
    }
  }

  int num_sols = sols.size();
  assert(num_sols <= k);  // Sanity check.

  vector<solution> solutions;
  for (int i = 0; i < num_sols; i++) {
    solutions.push_back(sols.top());
    sols.pop();
  }

  duration = ( std::clock() - start ) / (double) CLOCKS_PER_SEC;
  cout << "Time: " << duration << '\n';
  return solutions;
}

void write_output(vector<solution> sols) {
  // Write the solutions to file.

  auto pretty = [](int attr) -> string { return ((attr < 0) ? string("-") : string(" ")) + "x" + to_string(abs(attr)); };

  ofstream file_out("discovery.out");
  for (int i = sols.size() - 1; i >= 0; i--) {
    file_out << sols[i].first << '\t';
    for (auto& attr : sols[i].second) {
      file_out << pretty(attr) << " ";
    }
    file_out << '\n';
  }
}

int main(int argc, char* argv[]) {  // Put them together and what have you got? https://www.youtube.com/watch?v=CACPu39fgBg
  if (argc == 1) {
    cout << "Please specify input file.\n";
  }

  int m, n, k, F;
  db D (m);
  get_data(argv[1], m, n, k, F, D);
  vector<solution> sols (midos(m, n, k, F, D, 0));
  write_output(sols);
}
