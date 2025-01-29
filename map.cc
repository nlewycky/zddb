#include <algorithm>
#include <bit>
#include <cassert>
#include <memory>
#include <print>
#include <queue>
#include <string_view>
#include <spanstream>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

// TODO: steal should take a Zdd of the srcs, should be able to do bulk-steal
//       (multiple steals of srcs to dest), should be fused with replace_values
//       to do that whole operations with no further temporaries.

// TODO: implement replace_values

// TODO: add a CLI to run the functions

// TODO: ZddSpigot is slow by virtue of being virtual methods through a
//       shared_ptr. This is fixable at the cost of more confusing C++ (fold
//       all the types into one with a std::variant). Any nice way to do it?


// We need to define std::hash for our std::tuple in order to put them in
// a std::unordered_map.

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
  explicit ZddNode(IdxTy lo, IdxTy hi, LabelTy label)
    : lo(lo), hi(hi), label(label) {}

  IdxTy lo = -3;
  IdxTy hi = -3;
  LabelTy label = -3;
};

// This is a container that holds any number of ZDDs that share the same set of
// underlying variables, and can only be mutated by adding new nodes.
struct ZddNodes {
  std::vector<ZddNode> nodes;
  std::unordered_map<std::tuple<IdxTy, IdxTy, LabelTy>, IdxTy> unique;

  // Get the label for the given node by index.
  LabelTy label(IdxTy idx) const {
    if (idx == lo_idx)
      return LO;
    if (idx == hi_idx)
      return HI;
    assert(idx < nodes.size());
    return nodes[idx].label;
  }

  // Look up the node by index.
  const ZddNode &operator[](IdxTy idx) const {
    assert(idx < nodes.size());
    return nodes[idx];
  }

  // Create a new node, or return the unique one if it already exists.
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

// This is a thin wrapper around ZddNodes that represents a single specific ZDD
// by pointing at the underlying flat array of nodes and knowing the index of
// the root node.
struct Zdd {
  explicit Zdd() {}
  explicit Zdd(ZddNodes *memory) : memory(memory), root(lo_idx) {}
  explicit Zdd(ZddNodes *memory, IdxTy root) : memory(memory), root(root) {}

  ZddNodes *memory = nullptr;
  IdxTy root = -3;

  LabelTy label(IdxTy idx) const {
    assert(memory);
    return memory->label(idx);
  }

  LabelTy root_label() const {
    return label(root);
  }

  const ZddNode &operator[](IdxTy idx) const {
    assert(memory);
    return (*memory)[idx];
  }

  IdxTy get(IdxTy lo, IdxTy hi, LabelTy label) {
    assert(memory);
    return memory->get(lo, hi, label);
  }

  // Verify that this is a correctly constructed ZDD.
  void verify() const {
    assert(memory);
    for (auto n : memory->nodes) {
      (void)n;
      assert(n.lo == lo_idx || n.lo == hi_idx ||
             n.label < (*memory)[n.lo].label);
      assert(n.hi == hi_idx || n.label < (*memory)[n.hi].label);
    }
  }

  Zdd adv_lo() const {
    assert(root >= 0);
    return Zdd(memory, (*memory)[root].lo);
  }

  Zdd adv_hi() const {
    assert(root >= 0);
    return Zdd(memory, (*memory)[root].hi);
  }

  // Find the start of the zdd that contains the elements specified in 'hi'
  // and does not contain any elements between the last element in 'hi' and
  // 'lo'.
  // If no such path exists, returns lo_idx.
  IdxTy walk(const std::vector<LabelTy> &hi, std::optional<LabelTy> lo) const {
    assert(hi.empty() || hi.back() >= 0);
    assert(!lo || *lo != lo_idx);
    assert(std::is_sorted(hi.begin(), hi.end()));
    assert(!lo || hi.empty() || hi.back() <= lo || *lo == hi_idx);
    
    if (hi.empty() && root == hi_idx)
      return !lo ? hi_idx : lo_idx;

    auto it = hi.begin(), e = hi.end();
    IdxTy x = root;
    while (it != e) {
      if (x < 0)
        return lo_idx;
      if (*it > (*this)[x].label)
        x = (*this)[x].lo;
      else if (*it < (*this)[x].label)
        return lo_idx;
      else {
        x = (*this)[x].hi;
        ++it;
      }
    }

    assert(x != lo_idx);
    
    if (lo) {
      if (x == hi_idx)
        return hi_idx;
      while ((*this)[x].label <= *lo || (*lo == hi_idx && x != hi_idx)) {
        x = (*this)[x].lo;
        if (x < 0)
          return x;
      }
    }

    return x;
  }
  
  // Enumerates every set in the ZDD and calls your callback for them, stops
  // when your callback returns true.
  template<typename CB>
  void enumerate_sets(CB cb) {
    if (root == lo_idx)
      return;

    std::vector<std::pair<IdxTy, std::vector<LabelTy>>> stack;
    stack.emplace_back(root, std::vector<LabelTy>{});
    do {
      auto &[nidx, variables] = stack.back();
      assert(nidx != lo_idx);
      if (nidx == hi_idx) {
        if constexpr (std::is_void_v<decltype(cb(variables))>)
          cb(variables);
        else if (cb(variables))
          return;
        stack.pop_back();
        continue;
      }
      const auto &n = (*this)[nidx];
      if (n.lo == lo_idx) {
        // Reuse existing `stack` entry to follow 'hi' edge. Update index, add
        // current node to the list of variables.
        nidx = n.hi;
        variables.emplace_back(n.label);
        continue;
      }

      // Existing entry in `stack` follows 'lo' edge. Update index but the
      // variables stay the same.
      nidx = n.lo;

      // Follow 'hi' edge and add it to `stack`. Add current node label to
      // the variables.
      auto variables_copy = variables;
      variables_copy.emplace_back(n.label);
      stack.emplace_back(n.hi, variables_copy);
    } while (!stack.empty());
  }
};

// How many non-terminal nodes are reachable from root?
uint32_t count_nodes(Zdd z) {
  if (z.root < 0)
    return 0;

  auto cmp = [&](IdxTy lhs, IdxTy rhs) {
    if (z.label(lhs) > z.label(rhs))
      return true;
    if (z.label(lhs) < z.label(rhs))
      return false;
    return lhs > rhs;
  };
  std::priority_queue<IdxTy, std::vector<IdxTy>, decltype(cmp)> worklist(cmp);
  worklist.push(z.root);
  IdxTy previous = hi_idx;
  uint32_t count = 0;

  do {
    auto idx = worklist.top();
    worklist.pop();
    assert(idx >= 0);

    if (idx == previous)
      continue;
    previous = idx;

    ++count;

    auto hi = z[idx].hi;
    auto lo = z[idx].lo;

    if (hi != hi_idx)
      worklist.push(hi);
    if (lo != lo_idx && lo != hi_idx && lo != hi)
      worklist.push(lo);
  } while (!worklist.empty());
  return count;
}

// How many sets are in this ZDD?
uint32_t count_sets(Zdd z) {
  if (z.root == lo_idx)
    return 0;
  if (z.root == hi_idx)
    return 1;

  auto cmp = [&](IdxTy lhs, IdxTy rhs) {
    if (z.label(lhs) > z.label(rhs))
      return true;
    if (z.label(lhs) < z.label(rhs))
      return false;
    return lhs > rhs;
  };
  std::priority_queue<IdxTy, std::vector<IdxTy>, decltype(cmp)> worklist(cmp);
  worklist.push(z.root);
  IdxTy previous = hi_idx;
  std::unordered_map<IdxTy, int> count;
  count[z.root] = 1;

  while (!worklist.empty()) {
    auto idx = worklist.top();
    worklist.pop();
    assert(idx >= 0);
    assert(count[idx] >= 1);

    if (idx == previous)
      continue;
    previous = idx;

    auto hi = z[idx].hi;
    auto lo = z[idx].lo;

    count[hi] += count[idx];
    if (hi != hi_idx)
      worklist.push(hi);

    if (lo != lo_idx) {
      count[lo] += count[idx];
      if (lo != hi && lo != hi_idx)
        worklist.push(lo);
    }
  }

  return count[hi_idx];
}

// This interface represents a generator of a ZDD, so that we can have ZDDs that
// are computing their contents as they go and don't have actual nodes in memory
// yet. The main downside is that we can't compare two spigots for equality:
// a unioning spigot simply does not know whether two different unions will
// happen to produce the same node for inputs it hasn't examined yet.
struct ZddSpigot {
  virtual ~ZddSpigot() {}
  virtual LabelTy root_label() const = 0;
  virtual std::shared_ptr<ZddSpigot> adv_lo() const = 0;
  virtual std::shared_ptr<ZddSpigot> adv_hi() const = 0;

  // This base implementation does not know about ZDD nodes with multiple
  // in-edges in the spigot. Any subclass that knows its internal shape should
  // implement this function to take advantage. For example, a chain of don't-
  // care nodes would take exponential work to reify but only requires a linear
  // number of nodes after all.
  virtual IdxTy reify_into(ZddNodes &ret) const {
    return ret.get(adv_lo()->reify_into(ret),
                   adv_hi()->reify_into(ret),
                   root_label());
  }
};

IdxTy copy_into(ZddNodes &ret, Zdd input) {
  auto root = input.root;
  if (root < 0)
    return root;
  auto memory = input.memory;
  std::unordered_map<IdxTy, IdxTy> cache{{lo_idx, lo_idx}, {hi_idx, hi_idx}};
  std::vector<IdxTy> worklist(1, root);
  do {
    auto n_idx = worklist.back();
    Zdd zdd(memory, n_idx);
    auto lo = zdd[n_idx].lo, hi = zdd[n_idx].hi;
    auto lo_it = cache.find(lo), hi_it = cache.find(hi);
    bool contains_lo = lo_it != cache.end();
    bool contains_hi = hi_it != cache.end();
    if (contains_lo && contains_hi) {
      auto idx = ret.get(lo_it->second, hi_it->second, zdd.root_label());
      if (n_idx == root)
        return idx;
      cache[n_idx] = idx;
      worklist.pop_back();
    } else {
      // Don't pop the current node, we'll revisit it after visiting the two
      // we're pushing now, it will be a leaf next time.
      if (!contains_lo)
        worklist.push_back(lo);
      if (!contains_hi && lo != hi)
        worklist.push_back(hi);
    }
  } while (1);
}

struct ZddZddSpigot final : public ZddSpigot {
  ZddZddSpigot(Zdd zdd) : zdd(zdd) {}
  ~ZddZddSpigot() override {}
  Zdd zdd;
  LabelTy root_label() const override { return zdd.root_label(); }
  std::shared_ptr<ZddSpigot> adv_lo() const override {
    return std::make_shared<ZddZddSpigot>(zdd.adv_lo());
  }
  std::shared_ptr<ZddSpigot> adv_hi() const override {
    return std::make_shared<ZddZddSpigot>(zdd.adv_hi());
  }
  IdxTy reify_into(ZddNodes &ret) const override {
    return copy_into(ret, zdd);
  }
};
struct LoSpigot final : public ZddSpigot {
  static std::shared_ptr<ZddSpigot> make() {
    static std::shared_ptr<ZddSpigot> lo_spigot =
      std::make_shared<LoSpigot>();
    return lo_spigot;
  }
  LabelTy root_label() const override { return LO; }
  IdxTy reify_into(ZddNodes &) const override {
    return lo_idx;
  }
  std::shared_ptr<ZddSpigot> adv_lo() const override {
    assert(false);
    std::unreachable();
  }
  std::shared_ptr<ZddSpigot> adv_hi() const override {
    assert(false);
    std::unreachable();
  }  
};
struct HiSpigot final : public ZddSpigot {
  static std::shared_ptr<ZddSpigot> make() {
    static std::shared_ptr<ZddSpigot> hi_spigot = 
      std::make_shared<HiSpigot>();
    return hi_spigot;
  }
  LabelTy root_label() const override { return HI; }
  IdxTy reify_into(ZddNodes &) const override {
    return hi_idx;
  }
  std::shared_ptr<ZddSpigot> adv_lo() const override {
    assert(false);
    std::unreachable();
  }
  std::shared_ptr<ZddSpigot> adv_hi() const override {
    assert(false);
    std::unreachable();
  }  
};

IdxTy multiunion(ZddNodes &ret, std::vector<Zdd> worklist, bool include_hi);

// Unions any number of ZDDs. Commonly used to construct ZDDs by unioning sets.
IdxTy multiunion(ZddNodes &ret, const std::vector<Zdd> &in) {
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

// Internal API. Worklist must not include any lo_idx or hi_idx ZDDs.
// To union with hi_idx, set include_hi instead.
IdxTy multiunion(ZddNodes &ret, std::vector<Zdd> worklist,
                 bool include_hi) {
  assert(std::all_of(worklist.begin(), worklist.end(),
                     [](auto &z) { return z.root_label() >= 0; }));

  if (worklist.empty())
    return include_hi ? hi_idx : lo_idx;

  // When we're down to one ZDD, just make a copy of it.
  //
  // This is a performance improvement only, multiunion works correctly if you
  // simply remove this code block.
  if (worklist.size() == 1 && !include_hi)
    return copy_into(ret, worklist[0]);

  // Find the next lowest label. Every node points to nodes with a greater
  // label or one of the terminal nodes.
  LabelTy next_label;
  {
    auto next_it =
      std::min_element(worklist.begin(), worklist.end(),
                       [&](const Zdd &lhs, const Zdd &rhs) {
        // There are no C++ objects for the terminal nodes, detect their special
        // labels so we don't try to do lookups of them. Terminal labels sort
        // last since any other node with a label must occur first along the
        // path to the terminal nodes.
        bool lhs_is_terminal = lhs.root < 0;
        bool rhs_is_terminal = rhs.root < 0;
        if (!lhs_is_terminal && !rhs_is_terminal)
          return lhs.root_label() < rhs.root_label();
        if (lhs_is_terminal && rhs_is_terminal)
          return lhs.root < rhs.root;
        return rhs_is_terminal;
    });
    next_label = next_it->root_label();
  }

  // The worklist never contains 'LO' nodes because unioning with 'LO' is
  // the identity operation. The worklist never contains 'HI' nodes, we store
  // those by setting `include_hi` to true instead.
  assert(next_label != LO && next_label != HI);

  // Partition the remaining nodes into lo-side and hi-side:
  //  * for nodes with label == next_label, expand them:
  //    + add their lo to next_lo and hi to next_hi
  //      - except don't add lo_idx
  //      - also don't add hi_idx by setting include_hi instead
  //  * otherwise, add the node to next_lo for processing on a later step.
  std::vector<Zdd> next_lo, next_hi;
  bool include_hi_lo = include_hi, include_hi_hi = false;
  for (const auto &z : worklist) {
    auto root = z.root;
    if (z.label(root) == next_label) {
      switch (z[root].lo) {
      case lo_idx:
        break;
      case hi_idx:
        include_hi_lo = true;
        break;
      default:
        next_lo.emplace_back(z.memory, z[z.root].lo);
        break;
      }
      if (z[root].hi == hi_idx)
        include_hi_hi = true;
      else
        next_hi.emplace_back(z.memory, z[z.root].hi);
    } else {
      next_lo.push_back(z);
    }
  }
  return ret.get(multiunion(ret, next_lo, include_hi_lo),
                 multiunion(ret, next_hi, include_hi_hi),
                 next_label);
}

struct MultiunionSpigot final : public ZddSpigot {
  static std::shared_ptr<ZddSpigot>
  make(const std::vector<std::shared_ptr<ZddSpigot>> &u) {
    bool include_hi = false;
    std::vector<std::shared_ptr<ZddSpigot>> to_union;
    for (auto z : u) {
      if (z->root_label() == LO)
        continue;
      if (z->root_label() == HI) {
        include_hi = true;
        continue;
      }
      to_union.push_back(z);
    }
    return std::make_shared<MultiunionSpigot>(to_union, include_hi);
  }

  std::vector<std::shared_ptr<ZddSpigot>> to_union;
  bool include_hi = false;

  mutable std::optional<LabelTy> next_label_cache;
  mutable std::shared_ptr<ZddSpigot> lo_cache, hi_cache;

  MultiunionSpigot(std::vector<std::shared_ptr<ZddSpigot>> to_union,
                   bool include_hi)
    : to_union(to_union), include_hi(include_hi) {
    if (to_union.empty())
      *next_label_cache = include_hi ? HI : LO;
  }

  LabelTy root_label() const override {
    if (next_label_cache)
      return *next_label_cache;

    LabelTy next_label;
    {
      auto next_it =
        std::min_element(to_union.begin(), to_union.end(),
                         [&](const std::shared_ptr<ZddSpigot> &lhs,
                             const std::shared_ptr<ZddSpigot> &rhs) {
          // There are no C++ objects for the terminal nodes, detect their 
          // special labels so we don't try to do lookups of them. Terminal
          // labels sort last since any other node with a label must occur first
          // along the path to the terminal nodes.
          bool lhs_is_terminal = lhs->root_label() < 0;
          bool rhs_is_terminal = rhs->root_label() < 0;
          if (!lhs_is_terminal && !rhs_is_terminal)
            return lhs->root_label() < rhs->root_label();
          if (lhs_is_terminal && rhs_is_terminal)
            return lhs->root_label() < rhs->root_label();
          return rhs_is_terminal;
      });
      next_label = (*next_it)->root_label();
    }

    assert(next_label != LO && next_label != HI);
    *next_label_cache = next_label;
    return next_label;
  }

  std::shared_ptr<ZddSpigot> adv_lo() const override {
    if (lo_cache)
      return lo_cache;

    auto next_label = root_label();
    bool include_hi = this->include_hi;
    std::vector<std::shared_ptr<ZddSpigot>> next;
    for (const auto &z : to_union) {
      if (z->root_label() == next_label) {
        auto lo = z->adv_lo();
        switch (lo->root_label()) {
        case LO:
          break;
        case HI:
          include_hi = true;
          break;
        default:
          next.push_back(lo);
          break;
        }
      } else {
        next.push_back(z);
      }
    }

    if (next.empty())
      return lo_cache = include_hi ? HiSpigot::make() : LoSpigot::make();
          
    if (next.size() == 1 && !include_hi)
      return lo_cache = next[0];

    return lo_cache =
               std::make_shared<MultiunionSpigot>(std::move(next), include_hi);
  }

  std::shared_ptr<ZddSpigot> adv_hi() const override {
    if (hi_cache)
      return hi_cache;

    auto next_label = root_label();
    bool include_hi = false;
    std::vector<std::shared_ptr<ZddSpigot>> next;
    for (const auto &z : to_union) {
      if (z->root_label() == next_label) {
        auto hi = z->adv_hi();
        if (hi->root_label() == HI)
          include_hi = true;
        else
          next.push_back(hi);
      }
    }

    if (next.empty())
      return hi_cache = include_hi ? HiSpigot::make() : LoSpigot::make();
    if (next.size() == 1 && !include_hi)
      return hi_cache = next[0];

    return hi_cache =
               std::make_shared<MultiunionSpigot>(std::move(next), include_hi);
  }
};

IdxTy subtract(ZddNodes &ret, Zdd lhs, Zdd rhs) {
  if (lhs.root == lo_idx)
    return lo_idx;
  if (lhs.root == hi_idx && rhs.root == hi_idx)
    return lo_idx;
  if (rhs.root == lo_idx)
    return copy_into(ret, lhs);

  if (lhs.root == hi_idx) {
    // return subtract(ret, lhs, rhs.adv_lo());
    while (rhs.root >= 0)
      rhs = rhs.adv_lo();
    assert(rhs.root == lo_idx || rhs.root == hi_idx);
    return rhs.root == hi_idx ? lo_idx : hi_idx;
  }
  if (rhs.root == hi_idx)
    return ret.get(subtract(ret, lhs.adv_lo(), rhs),
                   copy_into(ret, lhs.adv_hi()),
                   lhs.root_label());

  if (lhs.root_label() < rhs.root_label()) {
    return ret.get(subtract(ret, lhs.adv_lo(), rhs),
                   copy_into(ret, lhs.adv_hi()),
                   lhs.root_label());
  }

  if (lhs.root_label() > rhs.root_label()) {
    // return subtract(ret, lhs, rhs.adv_lo());
    while (rhs.root_label() >= 0 && lhs.root_label() > rhs.root_label())
      rhs = rhs.adv_lo();
    return subtract(ret, lhs, rhs);
  }

  auto lo = subtract(ret, lhs.adv_lo(), rhs.adv_lo());
  auto hi = subtract(ret, lhs.adv_hi(), rhs.adv_hi());
  if (hi == lo_idx)
    return lo;
  return ret.get(lo, hi, lhs.root_label());
}

IdxTy subtract(ZddNodes &ret,
               std::shared_ptr<ZddSpigot> lhs,
               std::shared_ptr<ZddSpigot> rhs) {
  if (lhs->root_label() == LO)
    return lo_idx;
  if (lhs->root_label() == HI && rhs->root_label() == HI)
    return lo_idx;
  if (rhs->root_label() == LO)
    return lhs->reify_into(ret);

  if (lhs->root_label() == HI) {
    // return subtract(ret, lhs, rhs->adv_lo());
    while (rhs->root_label() >= 0)
      rhs = rhs->adv_lo();
    assert(rhs->root_label() == LO || rhs->root_label() == HI);
    return rhs->root_label() == HI ? LO : HI;
  }
  if (rhs->root_label() == HI)
    return ret.get(subtract(ret, lhs->adv_lo(), rhs),
                   lhs->adv_hi()->reify_into(ret),
                   lhs->root_label());

  if (lhs->root_label() < rhs->root_label()) {
    return ret.get(subtract(ret, lhs->adv_lo(), rhs),
                   lhs->adv_hi()->reify_into(ret),
                   lhs->root_label());
  }

  if (lhs->root_label() > rhs->root_label()) {
    // return subtract(ret, lhs, rhs->adv_lo());
    while (rhs->root_label() >= 0 && lhs->root_label() > rhs->root_label())
      rhs = rhs->adv_lo();
    return subtract(ret, lhs, rhs);
  }

  auto lo = subtract(ret, lhs->adv_lo(), rhs->adv_lo());
  auto hi = subtract(ret, lhs->adv_hi(), rhs->adv_hi());
  if (hi == lo_idx)
    return lo;
  return ret.get(lo, hi, lhs->root_label());
}

IdxTy multiintersect_inner(ZddNodes &ret, std::vector<Zdd> worklist);

// Intersects any number of ZDDs.
IdxTy multiintersect(ZddNodes &ret, const std::vector<Zdd> &in) {
  std::vector<Zdd> worklist;
  bool include_hi = false;
  for (int i = 0, e = in.size(); i != e; ++i) {
    if (in[i].root == lo_idx)
      return lo_idx;
    if (in[i].root == hi_idx && !include_hi) {
      // Include only 1 hi.
      worklist.push_back(in[i]);
      include_hi = true;
      continue;
    }
    worklist.push_back(in[i]);
  }
  return multiintersect_inner(ret, worklist);
}

// Internal API. Worklist must not include any lo_idx ZDDs.
IdxTy multiintersect_inner(ZddNodes &ret, std::vector<Zdd> worklist) {
  assert(std::all_of(worklist.begin(), worklist.end(),
                     [](auto &z) { return z.root != lo_idx; }));

  if (worklist.empty())
    return lo_idx;

  // When we're down to one ZDD, just make a copy of it.
  //
  // This is a performance improvement only, multiintersect works correctly if
  // you simply remove this code block.
  if (worklist.size() == 1)
    return copy_into(ret, worklist[0]);

  LabelTy next_label = 0;
  bool rerun_needed;
  do {
    rerun_needed = false;

    // Walk every ZDD down the LO edge until they reach or pass next_label.
    // If we pass next_label, update next_label to the new label.
    for (auto &z : worklist) {
      while (z.root != hi_idx && (z.root_label() < next_label ||
                                  (next_label == HI && z.root != hi_idx))) {
        z.root = z[z.root].lo;
        if (z.root == lo_idx)
          return lo_idx;
      }
      if (z.root_label() > next_label ||
          (z.root == hi_idx && next_label != HI)) {
        // TODO: we only need to rerun the ones before this point
        next_label = z.root_label();
        rerun_needed = true;
      }
    }
  } while(rerun_needed);

  assert(std::all_of(worklist.begin(), worklist.end(),
                     [&](auto &z) { return z.root_label() == next_label; }));

  if (next_label == HI)
    return hi_idx;

  bool include_hi_lo = false, include_hi_hi = false;
  std::vector<Zdd> next_lo, next_hi;
  bool kill_lo = false;
  for (const auto &z : worklist) {
    // Walk lo edge and add to next_lo.
    if (!kill_lo) {
      switch (z[z.root].lo) {
      case lo_idx:
        kill_lo = true;
        next_lo.clear();
        break;
      case hi_idx:
        if (!include_hi_lo)
          next_lo.emplace_back(z.memory, z[z.root].lo);
        include_hi_lo = true;
        break;
      default:
        next_lo.emplace_back(z.memory, z[z.root].lo);
        break;
      }
    }

    // Walk hi edge and add to next_hi.
    if (z[z.root].hi == hi_idx) {
      if (!include_hi_hi)
        next_hi.emplace_back(z.memory, z[z.root].hi);
      include_hi_hi = true;
    } else
      next_hi.emplace_back(z.memory, z[z.root].hi);
  }

  auto lo = multiintersect_inner(ret, next_lo);
  auto hi = multiintersect_inner(ret, next_hi);
  if (hi == lo_idx)
    return lo;
  return ret.get(lo, hi, next_label);
}

class MultiBiMap {
public:
  ZddNodes memory;
  Zdd contents;

  IdxTy build_zdd(Zdd &ret, uint32_t key, uint32_t value) {
    IdxTy hi = hi_idx;
    LabelTy count = sizeof(key)*8 + sizeof(value)*8 - 1;
    uint32_t mask = 1;
    do {
      if (value & mask)
        hi = ret.get(lo_idx, hi, count);
      mask <<= 1;
      --count;
    } while (mask);
    mask = 1;
    do {
      if (key & mask)
        hi = ret.get(lo_idx, hi, count);
      mask <<= 1;
      --count;
    } while (mask);
    return hi;
  }

public:

  explicit MultiBiMap() : contents(&memory) {}

  // TODO: remove this in favour of ZddSpigot
  struct ResultSet {
    Zdd contents;
    // TODO: remap our labels into caller's notion of key and value.
  };

  void insert(uint32_t key, uint32_t value) {
    bulk_insert({{key, value}});
  }

  void bulk_insert(std::vector<std::pair<uint32_t, uint32_t>> k_v,
                   bool compact = true) {
    ZddNodes temp;
    std::vector<Zdd> kv_zdds;
    kv_zdds.resize(k_v.size() + 1);
    int i = 0;
    for (const auto &[key, value] : k_v) {
      Zdd &kv = kv_zdds[i];
      ++i;
      kv.memory = &temp;
      kv.root = build_zdd(kv, key, value);
    }
    if (!compact) {
      kv_zdds.back() = contents;
      contents.root = multiunion(*contents.memory, kv_zdds);
    } else {
      ZddNodes old_contents_memory;
      std::swap(old_contents_memory, *contents.memory);
      kv_zdds.back() = Zdd(&old_contents_memory, contents.root);
      contents.root = multiunion(*contents.memory, kv_zdds);
    }
  }

  bool contains(uint32_t key, uint32_t value) {
    std::vector<LabelTy> labels;
    labels.reserve(std::popcount(key) + std::popcount(value));
    while (value) {
      labels.push_back(63 - std::countr_zero(value));
      value &= value-1;
    }
    while (key) {
      labels.push_back(31 - std::countr_zero(key));
      key &= key-1;
    }
    std::reverse(labels.begin(), labels.end());
    return contents.walk(labels, hi_idx) == hi_idx;
  }

  ResultSet lookup(uint32_t key) {
    std::vector<LabelTy> labels;
    labels.reserve(std::popcount(key));
    while (key) {
      labels.push_back(31 - std::countr_zero(key));
      key &= key-1;
    }
    std::reverse(labels.begin(), labels.end());
    IdxTy x = contents.walk(labels, sizeof(key)*8 - 1);
    return ResultSet{Zdd{contents.memory, x}};
  }
    
  ResultSet reverse_lookup(uint32_t value, ZddNodes *memory) {
    // TODO: a temporary ZDD + intersection is overkill. We only need to walk
    // to the zdd nodes where the values start, then multiunion those.
    // It's not immediately clear to me whether that will be faster, performance
    // testing will be needed.
    ZddNodes temp;
    Zdd ret{&temp};
    IdxTy hi = hi_idx;
    LabelTy count = sizeof(uint32_t)*8 + sizeof(value)*8 - 1;
    uint32_t mask = 1;
    do {
      if (value & mask)
        hi = ret.get(lo_idx, hi, count);
      mask <<= 1;
      --count;
    } while (mask);
    mask = 1;
    // Create a don't-care path for the keys.
    do {
      hi = ret.get(hi, hi, count);
      mask <<= 1;
      --count;
    } while (mask);
    ret.root = hi;

    IdxTy rs = multiintersect(*memory, {ret, contents});
    ResultSet results{Zdd{memory, rs}};
    return results;
  }

  // TODO: perhaps return the set of values as a Zdd instead? If we returned a
  //       spigot, this could feed directly into steal and replace_values.
  std::vector<int> find_multivalues() const {
    // Count the number of hi edges that cross from a node whose label is
    // a key bit, to a node whose label is a value bit (or hi_idx because that
    // represents the value zero). Also, we need to track the interior key bits
    // that have multiple in-edges and include those in the count of values with
    // multiple keys.

    auto cmp = [this](IdxTy lhs, IdxTy rhs) {
      if (contents.label(lhs) > contents.label(rhs))
        return true;
      if (contents.label(lhs) < contents.label(rhs))
        return false;
      return lhs > rhs;
    };
    std::priority_queue<IdxTy, std::vector<IdxTy>, decltype(cmp)> worklist(cmp);
    if (contents.root >= 0)
      worklist.push(contents.root);
    IdxTy previous = hi_idx;
    std::unordered_map<IdxTy, int> count;
    count[contents.root] = 1;

    while (!worklist.empty()) {
      auto idx = worklist.top();
      worklist.pop();
      assert(idx >= 0);
      assert(count[idx] >= 1);

      if (idx == previous)
        continue;
      previous = idx;

      auto node = contents[idx];
      if (node.label >= 32)
        continue;
      auto hi = node.hi;
      auto lo = node.lo;

      count[hi] += count[idx];
      if (hi != hi_idx)
        worklist.push(hi);

      if (lo != lo_idx) {
        count[lo] += count[idx];
        if (lo != hi && lo != hi_idx)
          worklist.push(lo);
      }
    }

    std::vector<int> values;
    if (count[hi_idx] > 1) {
      values.push_back(0);
      count.erase(hi_idx);
    }
    for (auto [idx_const, number] : count) {
      if (number > 1) {
        // Walk through values labels to find its bits and reconstruct
        // the value.
        uint32_t value = 0;
        IdxTy idx = idx_const;
        while (idx != hi_idx) {
          value |= 1u << (32u - (contents.label(idx) - 31u));
          idx = contents[idx].hi;
        }
        values.push_back(value);
      }
    }
    return values;
  }

  // TODO: make 'srcs' a spigot so that we can pass in a Zdd (or a union) to
  //       specify which keys we're stealing from.
  void steal(const uint32_t dest, const std::vector<uint32_t> &srcs) {
    struct DontCareSpigot final : public ZddSpigot {
      ~DontCareSpigot() override {}
      explicit DontCareSpigot(LabelTy start, LabelTy end)
          : start(start), end(end) {
        assert(start >= 0);
        assert(end >= 0);
        assert(start < end);
      }
      LabelTy start = lo_idx, end = lo_idx;
      LabelTy root_label() const override {
        return start;
      }
      std::shared_ptr<ZddSpigot> adv_lo() const override {
        if (start + 1 == end)
          return HiSpigot::make();
        return std::make_shared<DontCareSpigot>(start + 1, end);
      }
      std::shared_ptr<ZddSpigot> adv_hi() const override {
        if (start + 1 == end)
          return HiSpigot::make();
        return std::make_shared<DontCareSpigot>(start + 1, end);
      }
      IdxTy reify_into(ZddNodes &ret) const override {
        IdxTy hi = hi_idx;
        for (LabelTy l = end - 1; l >= start; --l)
          hi = ret.get(hi, hi, l);
        return hi;
      }
    };

    struct KeySpigot final : public ZddSpigot {
      static std::shared_ptr<ZddSpigot> make(uint32_t key) {
        if (key == 0)
          return std::make_shared<DontCareSpigot>(32, 64);
        return std::make_shared<KeySpigot>(key);
      }
      explicit KeySpigot(uint32_t key) : key(key) {
        assert(key);
      }
      uint32_t key = 0;
      ~KeySpigot() override {}
      LabelTy root_label() const override {
        assert(key);
        return std::countl_zero(key);
      }
      std::shared_ptr<ZddSpigot> adv_lo() const override {
        if (std::popcount(key) > 1)
          return LoSpigot::make();
        return std::make_shared<DontCareSpigot>(32, 64);
      }
      std::shared_ptr<ZddSpigot> adv_hi() const override {
        uint32_t new_key = key ^ (1u << (31 - std::countl_zero(key)));
        assert(new_key < key);
        if (new_key)
          return KeySpigot::make(new_key);
        return std::make_shared<DontCareSpigot>(32, 64);
      }
    };
    struct DifferentKey final : public ZddSpigot {
      static std::shared_ptr<ZddSpigot> make(uint32_t key, Zdd value) {
        if (key == 0)
          return std::make_shared<ZddZddSpigot>(value);
        return std::make_shared<DifferentKey>(key, value);
      }
      DifferentKey(uint32_t key, Zdd value) : key(key), value(value) {
        assert(key);
      }
      uint32_t key = 0;
      Zdd value;
      ~DifferentKey() override {}
      LabelTy root_label() const override {
        assert(key);
        return std::countl_zero(key);
      }
      std::shared_ptr<ZddSpigot> adv_lo() const override {
        if (std::popcount(key) > 1)
          return LoSpigot::make();
        return std::make_shared<ZddZddSpigot>(value);
      }
      std::shared_ptr<ZddSpigot> adv_hi() const override {
        uint32_t new_key = key ^ (1u << (31 - std::countl_zero(key)));
        assert(new_key < key);
        if (new_key)
          return DifferentKey::make(new_key, value);
        return std::make_shared<ZddZddSpigot>(value);
      }
    };

    assert(std::is_sorted(srcs.begin(), srcs.end()));
    assert(!std::binary_search(srcs.begin(), srcs.end(), dest));
    assert(std::adjacent_find(srcs.begin(), srcs.end()) == srcs.end());

    if (srcs.empty())
      return;

    std::vector<std::shared_ptr<ZddSpigot>> src_zdds;
    src_zdds.reserve(srcs.size() + 1);
    src_zdds.push_back(std::make_shared<ZddZddSpigot>(contents));
    for (auto key : srcs) {
      auto lr = lookup(key);
      src_zdds.push_back(DifferentKey::make(dest, lr.contents));
    }

    std::vector<std::shared_ptr<ZddSpigot>> to_del;
    to_del.reserve(srcs.size());
    for (auto key : srcs)
      to_del.push_back(KeySpigot::make(key));

    contents.root = subtract(memory,
                             MultiunionSpigot::make(src_zdds),
                             MultiunionSpigot::make(to_del));
  }

  // 'matcher' contains a set of all values that the replacement will be applied
  // to.
  // TODO: implement
  void replace_values(uint32_t replacement, uint32_t replacement_mask,
                      Zdd matcher) {
    assert((replacement & ~replacement_mask) == 0);
    assert(replacement_mask != 0);

    // clobber([replacement], intersect(contents, matcher))
    //   union
    // subtract(contents, matcher)
  }

  void stats(uint32_t &live, uint32_t &total) const {
    total = contents.memory->nodes.size();
    live = count_nodes(contents);
  }

  void repack() {
    ZddNodes old_memory;
    std::swap(old_memory, memory);
    contents.root = copy_into(memory, Zdd(&old_memory, contents.root));
  }
};

}  // end anonymous namespace

namespace {
  // Produce a ZDD with a single set in it representing the bytes in line, each
  // byte represented with one label in range of [0 .. 255].
  IdxTy line_to_zdd(Zdd &ret, std::string line) {
    assert(std::is_sorted(line.begin(), line.end()));
    assert(line.size() < 255);  // assumes 8-bit 'LabelTy'
    IdxTy hi = hi_idx;
    for (auto i = line.rbegin(), e = line.rend(); i != e; ++i)
      hi = ret.get(lo_idx, hi, *i);
    return hi;
  }

  IdxTy parse(ZddNodes *flat2, std::string_view s) {
    Zdd all_lines(flat2);

    {
      ZddNodes flat1;
      std::vector<Zdd> lines;

      {
        std::ispanstream iss(s);
        for (std::string line; std::getline(iss, line);) {
          lines.emplace_back(&flat1);
          lines.back().root = line_to_zdd(lines.back(), line);
          assert((lines.back().verify(), true));
        }
      }

      all_lines.root = multiunion(*flat2, lines);
      assert((all_lines.verify(), true));
    }
    return all_lines.root;
  }

  namespace tests {
    void test_intersect() {
      ZddNodes memory;

      std::vector<Zdd> zdds;
      zdds.emplace_back(&memory, parse(&memory, "abc\nac\nbd\n"));
      zdds.emplace_back(&memory, parse(&memory, "abcd\nac\nbd\n"));

      //zdds.emplace_back(&memory, parse(&memory, "abc\nd\n"));
      //zdds.emplace_back(&memory, parse(&memory, "ab\nd\n"));
      //zdds.emplace_back(&memory, parse(&memory, "ac\nd\n"));

      //zdds.emplace_back(&memory, parse(&memory, "xy\nx\n"));
      //zdds.emplace_back(&memory, parse(&memory, "x\ny\nxy\n"));

      Zdd zdd(&memory, multiintersect(memory, zdds));

      zdd.enumerate_sets([&](auto variables) {
        for (auto v : variables)
          std::print("{}", (char)(v));
        std::println("");
      });
    }

    void test_walk() {
      ZddNodes memory;
      IdxTy root = parse(&memory, "abc\nac\nbd\n");
      Zdd zdd(&memory, root);

      {
        Zdd test(&memory, zdd.walk({'a'}, 'c'));
        test.enumerate_sets([&](auto variables) {
          for (auto v : variables)
            std::print("{}", (char)(v));
          std::println("");
        });
      }
      return;

      {
        Zdd test(&memory, zdd.walk({'b'}, std::nullopt));
        test.enumerate_sets([&](auto variables) {
          for (auto v : variables)
            std::print("{}", (char)(v));
          std::println("");
        });
      }

      {
        Zdd test(&memory, zdd.walk({'c'}, std::nullopt));
        assert(test.root == lo_idx);
      }

      {
        Zdd test(&memory, zdd.walk({'a', 'b'}, std::nullopt));
        test.enumerate_sets([&](auto variables) {
          for (auto v : variables)
            std::print("{}", (char)(v));
          std::println("");
        });
      }
    }

    void test_lookup() {
      MultiBiMap map;
      map.insert(1, 2);
      map.insert(1, 3);
      map.insert(2, 0);
      map.insert(7, 0);
      auto results = map.lookup(8);
      results.contents.enumerate_sets([&](auto variables) {
        std::print("{{ ");
        for (auto v : variables)
          std::print("{} ", v);
        std::println("}}");
      });
    }

    void test_contains() {
      MultiBiMap map;

#if 0
      ZddNodes memory;
      Zdd z(&memory);
      IdxTy idx = map.build_zdd(z, 0x80000001, 0x80000001);
      std::println("idx: {}", idx);
      Zdd z2(&memory, idx);
      z2.enumerate_sets([&](auto variables) {
       for (auto v : variables)
          std::print("{} ", v);
        std::println("");
      });
#endif

      map.insert(1, 2);
      map.insert(1, 3);
      map.insert(2, 3);
      map.contents.enumerate_sets([&](auto variables) {
        std::print("{{ ");
        for (auto v : variables)
          std::print("{} ", v);
        std::println("}}");
      });
      std::println("{}", map.contains(1, 2));

#if 0
      assert(!map.contains(2, 1));
      assert(!map.contains(1, 2));
      
      assert(!map.contains(2, 1));
      assert(map.contains(1, 2));
#endif

      map.insert(7, 0);
      map.insert(8, 0);
      map.insert(9, 1);
      map.insert(10, 0);
      map.insert(10, 1);
      assert(map.contains(7, 0));
      assert(map.contains(8, 0));
      assert(map.contains(9, 1));
      assert(map.contains(10, 0));
      assert(map.contains(10, 1));

      assert(!map.contains(0, 0));
      assert(!map.contains(0, 1));
      assert(!map.contains(1, 0));
      assert(!map.contains(1, 1));
      assert(!map.contains(0, 7));
      assert(!map.contains(7, 1));
    }

    void test_reverse_lookup() {
      MultiBiMap map;

      map.insert(7, 0);
      map.insert(8, 0);
      map.insert(9, 1);
      map.insert(10, 0);
      map.insert(10, 1);

      ZddNodes temp;
      auto results = map.reverse_lookup(2, &temp);
      results.contents.enumerate_sets([&](auto variables) {
        std::print("{{ ");
        for (auto v : variables)
          std::print("{} ", v);
        std::println("}}");
      });
    }

    void test_find_multivalues() {
      MultiBiMap map;

      auto dump_labels = [](const std::vector<LabelTy> &labels) {
        std::print("{{ ");
        for (auto l : labels)
          std::print("{} ", l);
        std::println("}}");
      };

      dump_labels(map.find_multivalues());
      map.insert(7, 0);
      dump_labels(map.find_multivalues());
      map.insert(8, 0);
      dump_labels(map.find_multivalues());
      map.insert(9, 6);
      dump_labels(map.find_multivalues());
      map.insert(10, 0);
      dump_labels(map.find_multivalues());
      map.insert(10, 6);
      dump_labels(map.find_multivalues());
    }

    void test_subtract() {
      ZddNodes memory;

      Zdd test1(&memory, multiunion(memory, {
            Zdd{&memory, parse(&memory, "a")},
            Zdd{&memory, parse(&memory, "b")},
            Zdd{&memory, parse(&memory, "c")},
            Zdd{&memory, parse(&memory, "d")},
            Zdd{&memory, parse(&memory, "e")}}));
      Zdd test2(&memory, multiunion(memory, {
            Zdd{&memory, parse(&memory, "b")},
            Zdd{&memory, parse(&memory, "d")}}));
      Zdd zdd(&memory, subtract(memory, test1, test2));
      zdd.enumerate_sets([&](auto variables) {
        for (auto v : variables)
          std::print("{}", (char)(v));
        std::println("");
      });
    }

    void test_steal() {
      MultiBiMap map;
      
      map.insert(7, 0);
      map.insert(8, 0);
      map.insert(9, 6);
      map.insert(10, 0);
      map.insert(10, 6);

      uint32_t live, total;
      map.stats(live, total);
      std::println("{} / {}", live, total);

      map.steal(7, {8, 9});

      map.stats(live, total);
      std::println("{} / {}", live, total);
      map.repack();

      std::println("{}", map.contains(7, 0));
      std::println("{}", map.contains(7, 6));
      std::println("{}", map.contains(8, 0));
      std::println("{}", map.contains(8, 6));
      std::println("{}", map.contains(9, 0));
      std::println("{}", map.contains(9, 6));
      std::println("{}", map.contains(10, 0));
      std::println("{}", map.contains(10, 1));
      std::println("{}", map.contains(10, 6));

      map.stats(live, total);
      std::println("{} / {}", live, total);
    }
  }
}

int main(void) {
  //tests::test_intersect();
  //tests::test_walk();
  //tests::test_contains();
  //tests::test_lookup();
  //tests::test_reverse_lookup();
  //tests::test_find_multivalues();
  //tests::test_subtract();
  tests::test_steal();
}
