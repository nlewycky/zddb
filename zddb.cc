#include <cassert>
#include <fstream>
#include <iostream>
#include <print>
#include <tuple>
#include <unordered_map>
#include <vector>

// begin cut-and-paste from stackoverflow
// function has to live in the std namespace
// so that it is picked up by argument-dependent name lookup (ADL).
namespace std {
  namespace {

    // Code from boost
    // Reciprocal of the golden ratio helps spread entropy
    //     and handles duplicates.
    // See Mike Seymour in magic-numbers-in-boosthash-combine:
    //     https://stackoverflow.com/questions/4948780

    template <class T>
    inline void hash_combine(std::size_t &seed, T const &v) {
      seed ^= hash<T>()(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    }

    // Recursive template code derived from Matthieu M.
    template <class Tuple, size_t Index = std::tuple_size<Tuple>::value - 1>
    struct HashValueImpl {
      static void apply(size_t& seed, Tuple const &tuple) {
        HashValueImpl<Tuple, Index-1>::apply(seed, tuple);
        hash_combine(seed, get<Index>(tuple));
      }
    };

    template <class Tuple>
    struct HashValueImpl<Tuple, 0> {
      static void apply(size_t& seed, Tuple const &tuple) {
        hash_combine(seed, get<0>(tuple));
      }
    };
  }

  template <typename ... TT>
  struct hash<std::tuple<TT...>> {
    size_t operator()(std::tuple<TT...> const &tt) const {
      size_t seed = 0;
      HashValueImpl<std::tuple<TT...> >::apply(seed, tt);
      return seed;
    }
  };
}
// end cut-and-paste from stackoverflow

namespace {

using LabelTy = int;
using IdxTy = int;

static constexpr IdxTy lo_idx = -1;
static constexpr IdxTy hi_idx = -2;
static constexpr LabelTy LO = -1;
static constexpr LabelTy HI = -2;

struct ZddNode {
  IdxTy lo = -3;
  IdxTy hi = -3;
  LabelTy label = -3;
};

struct ZddNodes {
  std::vector<ZddNode> nodes;
  std::unordered_map<std::tuple<IdxTy, IdxTy, LabelTy>, IdxTy> unique;

  LabelTy get_label(IdxTy idx) const {
    if (idx == lo_idx)
      return LO;
    if (idx == hi_idx)
      return HI;
    assert(idx < nodes.size());
    return nodes[idx].label;
  }

  const ZddNode &operator[](IdxTy idx) const {
    assert(idx < nodes.size());
    return nodes[idx];
  }

  IdxTy get(IdxTy lo, IdxTy hi, LabelTy label) {
    assert(label != LO && label != HI);
    assert(hi != lo_idx);
    auto [it, did_insert] = unique.try_emplace({lo, hi, label}, nodes.size());
    if (did_insert) {
      auto idx = nodes.size();
      nodes.emplace_back(lo, hi, label);
      return idx;
    }
    return it->second;
  }
};

struct Zdd {
  Zdd() {}
  explicit Zdd(ZddNodes *memory) : memory(memory) {}
  explicit Zdd(ZddNodes *memory, IdxTy root) : memory(memory), root(root) {}

  ZddNodes *memory = nullptr;
  IdxTy root = lo_idx;

  LabelTy get_label(IdxTy idx) const {
    assert(memory);
    return memory->get_label(idx);
  }

  const ZddNode &operator[](IdxTy idx) const {
    assert(memory);
    return (*memory)[idx];
  }

  IdxTy get(IdxTy lo, IdxTy hi, LabelTy label) {
    assert(memory);
    return memory->get(lo, hi, label);
  }

  void check() {
    assert(memory);
    for (auto n : memory->nodes) {
      assert(n.lo == lo_idx || n.lo == hi_idx || n.label < (*memory)[n.lo].label);
      assert(n.hi == hi_idx || n.label < (*memory)[n.hi].label);
    }
  }
};

IdxTy multiunion(Zdd &ret, std::vector<Zdd> worklist, bool include_hi);
IdxTy multiunion(Zdd &ret, const std::vector<Zdd> &in) {
  std::vector<Zdd> worklist;
  bool include_hi = false;
  for (int i = 0, e = in.size(); i != e; ++i) {
    if (in[i].root == lo_idx)
      continue;
    if (in[i].root == hi_idx) {
      include_hi = true;
      continue;
    }
    worklist.push_back(in[i]);
  }
  return multiunion(ret, worklist, include_hi);
}

IdxTy multiunion(Zdd &ret, std::vector<Zdd> worklist, bool include_hi) {
#ifndef NDEBUG
  for (auto [_idx, root] : worklist)
    assert(root >= 0);
#endif

  if (worklist.empty())
    return include_hi ? hi_idx : lo_idx;

  LabelTy next_label;
  {
    auto next_it =
      std::min_element(worklist.begin(), worklist.end(),
                       [&](const Zdd &lhs, const Zdd &rhs) {
        bool l_term = lhs.root < 0;
        bool r_term = rhs.root < 0;
        if (!l_term && !r_term)
          return lhs.get_label(lhs.root) < rhs.get_label(rhs.root);
        if (l_term && r_term)
          return lhs.root < rhs.root;
        return r_term;
    });
    next_label = next_it->get_label(next_it->root);
  }

  assert(next_label != LO && next_label != HI);

  std::vector<Zdd> next_lo, next_hi;
  bool include_hi_lo = include_hi, include_hi_hi = false;
  for (const auto &z : worklist) {
    auto root = z.root;
    if (z.get_label(root) == next_label) {
      switch (z[root].lo) {
      case lo_idx:
        break;
      case hi_idx:
        include_hi_lo = true;
        break;
      default:
        next_lo.emplace_back(z.memory, z[root].lo);
      }
      if (z[root].hi == hi_idx)
        include_hi_hi = true;
      else
        next_hi.emplace_back(z.memory, z[root].hi);
    } else {
      next_lo.push_back(z);
    }
  }
  return ret.get(multiunion(ret, next_lo, include_hi_lo),
                 multiunion(ret, next_hi, include_hi_hi),
                 next_label);
}

IdxTy line_to_zdd(Zdd &ret, std::string line) {
  assert(line.size() < 8388608);  // assumes 32-bit 'LabelTy'
  IdxTy hi = hi_idx;
  int count = line.size() - 1;
  for (auto i = line.rbegin(), e = line.rend(); i != e; ++i) {
    hi = ret.get(lo_idx, hi, *i + (256 * count));
    --count;
  }
  return hi;
}
}

int main(int argc, char **argv) {
  ZddNodes flat2;
  Zdd all_lines(&flat2);

  {
    ZddNodes flat1;
    std::vector<Zdd> lines;

    {
      std::ifstream ifs(argv[1]);
      for (std::string line; std::getline(ifs, line);) {
        lines.emplace_back(&flat1);
        lines.back().root = line_to_zdd(lines.back(), line);
        assert((lines.back().check(), true));
      }
    }

    all_lines.root = multiunion(all_lines, lines);
    assert((all_lines.check(), true));
  }
}
