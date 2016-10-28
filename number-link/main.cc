
#include <iostream>
#include <iterator>
#include <map>
#include <vector>

#include "minisat/core/Solver.h"

void Equiv(Minisat::Solver& solver,
           const Minisat::Lit& x,
           const Minisat::Lit& y) {
  // x <=> y
  // x => y & y => x
  // (~x || y) & (x || ~y)
  solver.addClause(~x, y);
  solver.addClause(x, ~y);
}

void Glue(Minisat::Solver& solver,
          const Minisat::Lit& g,
          const Minisat::Lit& x,
          const Minisat::Lit& y) {
  // g => (x <=> y)
  // ~g || ((~x || y) & (x || ~y))
  // (~g || ~x || y) & (~g || x || ~y)
  solver.addClause(~g, ~x, y);
  solver.addClause(~g, x, ~y);
}

void Stick(Minisat::Solver& solver,
           const Minisat::Lit& g,
           const Minisat::Lit& x,
           const Minisat::Lit& y) {
  // (x & y) => g
  // g || ~x || ~y
  solver.addClause(g, ~x, ~y);
}

// Stores |k| items from |itr| to |end| into |c|, and call |f|.
template <typename Iterator, typename Container, typename F>
void Choose(int k,
            Iterator itr, Iterator end,
            Container& c,
            F f) {
  int n = std::distance(itr, end);
  if (k > n)
    return;

  if (k == 0) {
    f();
    return;
  }

  if (k == n) {
    c.insert(c.end(), itr, end);
    f();
    c.erase(c.end() - n, c.end());
    return;
  }

  c.push_back(*itr);
  ++itr;
  Choose(k - 1, itr, end, c, f);
  c.pop_back();

  Choose(k, itr, end, c, f);
}

template <typename Iterator>
void LessThan(Minisat::Solver& solver, int n, Iterator itr, Iterator end) {
  std::vector<Minisat::Lit> vs;
  Choose(n, itr, end, vs, [&]() {
    Minisat::vec<Minisat::Lit> clause;
    clause.capacity(vs.size());
    for (auto& v : vs)
      clause.push(~v);
    solver.addClause(clause);
  });
}

template <typename Iterator>
void GreaterThan(Minisat::Solver& solver, int n, Iterator itr, Iterator end) {
  std::vector<Minisat::Lit> vs;
  Choose(std::distance(itr, end) - n, itr, end, vs, [&]() {
    Minisat::vec<Minisat::Lit> clause;
    clause.capacity(vs.size());
    for (auto& v : vs)
      clause.push(v);
    solver.addClause(clause);
  });
}

template <typename Iterator>
void Exact(Minisat::Solver& solver, int n, Iterator itr, Iterator end) {
  LessThan(solver, n + 1, itr, end);
  GreaterThan(solver, n - 1, itr, end);
}

template <typename T>
void Exact(Minisat::Solver& solver, int n, const T& xs) {
  using std::begin;
  using std::end;
  Exact(solver, n, begin(xs), end(xs));
}

struct Instance {
  enum Direction {
    Sink = 0, North, South, East, West
  };

  Minisat::Solver solver;
  std::vector<char> labels;
  int pairs, width, height;
  std::vector<Minisat::Lit> assignments;
  std::vector<Minisat::Lit> sinks;
  std::vector<Minisat::Lit> east_west;
  std::vector<Minisat::Lit> north_south;

  std::vector<Minisat::Lit> MakeLiterals(size_t s) {
    std::vector<Minisat::Lit> ret;
    ret.reserve(s);
    for (size_t i = 0; i < s; ++i)
      ret.push_back(Minisat::mkLit(solver.newVar()));
    return ret;
  }

  Instance() = delete;
  Instance(const Instance&) = delete;
  Instance(Instance&&) = delete;
  Instance& operator=(const Instance&) = delete;
  Instance& operator=(Instance&&) = delete;

  Instance(std::vector<char> labels, int pairs, int width, int height)
      : labels(std::move(labels)),
        pairs(pairs), width(width), height(height),
        assignments(MakeLiterals(pairs * width * height)),
        sinks(MakeLiterals(width * height)),
        east_west(MakeLiterals((width + 1) * height)),
        north_south(MakeLiterals(width * (height + 1))) {
  }

  ~Instance() {}

  const Minisat::Lit& assignment(int i, int j, int k) {
    assert(0 <= i && i < height);
    assert(0 <= j && j < width);
    assert(0 <= k && k < pairs);
    return assignments[(i * width + j) * pairs + k];
  }

  const Minisat::Lit& edge(int i, int j, Direction d) {
    assert(0 <= i && i < height);
    assert(0 <= j && j < width);
    switch (d) {
      case Sink:
        return sinks[i * width + j];
      case East:
      case West:
        return east_west[i * (width + 1) + j + (d == East ? 1 : 0)];
      case North:
      case South:
        return north_south[(i + (d == South ? 1 : 0)) * width + j];
    }
    assert(false);
  }

  void SetUpBasicConstraints() {
    SetUpAssignmentConstraints();
    SetUpWallConstraints();
    SetUpDegreeConstraints();
    SetUpLinkConstraints();
  }

  void SetUpSpanningUniqueConstraints() {
    SetUpStickConstraints();
    SetUpCornerPropagationConstraints();
  }

  void SetUpAssignmentConstraints() {
    for (int i = 0; i < height; ++i) {
      for (int j = 0; j < width; ++j) {
        std::vector<Minisat::Lit> xs;
        for (int k = 0; k < pairs; ++k)
          xs.push_back(assignment(i, j, k));
        Exact(solver, 1, xs);
      }
    }
  }

  void SetUpWallConstraints() {
    for (int i = 0; i < height; ++i) {
      solver.addClause(~edge(i, 0, West));
      solver.addClause(~edge(i, width - 1, East));
    }
    for (int j = 0; j < width; ++j) {
      solver.addClause(~edge(0, j, North));
      solver.addClause(~edge(height - 1, j, South));
    }
  }

  void SetUpDegreeConstraints() {
    for (int i = 0; i < height; ++i) {
      for (int j = 0; j < width; ++j) {
        std::vector<Minisat::Lit> xs;
        for (int d = Sink; d <= West; ++d)
          xs.push_back(edge(i, j, static_cast<Direction>(d)));
        Exact(solver, 2, xs);
      }
    }
  }

  void SetUpLinkConstraints() {
    for (int i = 1; i < height; ++i)
      for (int j = 0; j < width; ++j) {
        auto& e = edge(i, j, North);
        for (int k = 0; k < pairs; ++k)
          Glue(solver, e, assignment(i, j, k), assignment(i - 1, j, k));
      }

    for (int i = 0; i < height; ++i)
      for (int j = 1; j < width; ++j) {
        auto& e = edge(i, j, West);
        for (int k = 0; k < pairs; ++k)
          Glue(solver, e, assignment(i, j, k), assignment(i, j - 1, k));
      }
  }

  void SetUpStickConstraints() {
    for (int i = 1; i < height; ++i)
      for (int j = 0; j < width; ++j) {
        auto& e = edge(i, j, North);
        for (int k = 0; k < pairs; ++k)
          Stick(solver, e, assignment(i, j, k), assignment(i - 1, j, k));
      }

    for (int i = 0; i < height; ++i)
      for (int j = 1; j < width; ++j) {
        auto& e = edge(i, j, West);
        for (int k = 0; k < pairs; ++k)
          Stick(solver, e, assignment(i, j, k), assignment(i, j - 1, k));
      }
  }

  void SetUpCornerPropagationConstraints() {
    for (int i = 0; i < height; ++i) {
      for (int j = 0; j < width; ++j) {
        if (i > 0 && j > 0)
          CornerPropagation(i, j, North, West);
        if (i > 0 && j < width - 1)
          CornerPropagation(i, j, North, East);
        if (i < height - 1 && j > 0)
          CornerPropagation(i, j, South, West);
        if (i < height - 1 && j < width - 1)
          CornerPropagation(i, j, South, East);
      }
    }
  }

  void CornerPropagation(int i, int j, Direction in, Direction out) {
    int ii = i + (in == North ? -1 : 1);
    int jj = j + (out == West ? -1 : 1);

    auto& e = edge(i, j, in);
    auto& f = edge(i, j, out);
    auto& s = edge(ii, jj, Sink);
    solver.addClause(~e, ~f, s, edge(ii, jj, in));
    solver.addClause(~e, ~f, s, edge(ii, jj, out));
  }

  void Fill(int i, int j, int k) {
    solver.addClause(assignment(i, j, k));
    solver.addClause(edge(i, j, Sink));
  }

  void Empty(int i, int j) {
    solver.addClause(~edge(i, j, Sink));
  }

  static std::unique_ptr<Instance> read(std::istream& in) {
    std::vector<std::string> input;

    std::vector<char> labels;
    std::map<char, int> label_to_index;

    std::string line;
    while (std::getline(in, line)) {
      if (line.empty() || line[0] == '#')
        continue;
      input.push_back(line);

      for (char c : line) {
        auto inserted = label_to_index.insert(std::make_pair(c, 0));
        if (inserted.second) {
          inserted.first->second = labels.size();
          labels.push_back(c);
        }
      }
    }

    int pairs = labels.size();
    int height = input.size();
    int width = height ? input.front().size() : 0;
    auto instance = std::make_unique<Instance>(
        std::move(labels), pairs, width, height);

    instance->SetUpBasicConstraints();
    instance->SetUpSpanningUniqueConstraints();

    for (int i = 0; i < height; ++i) {
      assert(input[i].size() == width);
      for (int j = 0; j < width; ++j) {
        if (input[i][j] == '.')
          instance->Empty(i, j);
        else
          instance->Fill(i, j, label_to_index[input[i][j]]);
      }
    }

    return instance;
  }

  void show(std::ostream& out) {
    auto& m = solver.model;;
    auto toBool = [&](const Minisat::Lit& x) {
      int i = Minisat::toInt(m[Minisat::var(x)]);
      assert(i != 2);
      return i == 0;
    };

    for (int i = 0; i < height; ++i) {
      for (int j = 0; j < width; ++j) {
        if (toBool(edge(i, j, Sink))) {
          for (int k = 0; k < pairs; ++k) {
            if (toBool(assignment(i, j, k))) {
              out << labels[k];
              break;
            }
          }
          continue;
        }

        int line = 0;
        if (toBool(edge(i, j, North)))
          line |= 1;
        if (toBool(edge(i, j, South)))
          line |= 2;
        if (toBool(edge(i, j, East)))
          line |= 4;
        if (toBool(edge(i, j, West)))
          line |= 8;
        switch (line) {
          case 3: out << u8"\u2502"; break;
          case 5: out << u8"\u2514"; break;
          case 9: out << u8"\u2518"; break;
          case 6: out << u8"\u250c"; break;
          case 10: out << u8"\u2510"; break;
          case 12: out << u8"\u2500"; break;
          default: out << " "; break;
        }
      }
      out << '\n';
    }
  }
};

int main() {
  auto instance = Instance::read(std::cin);
  if (!instance->solver.solve()) {
    std::cout << "No unique spanning solution.\n";
    return -1;
  }

  instance->solver.printStats();
  instance->show(std::cout);
  return 0;
}
